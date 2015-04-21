package semantics

import syntax.Identifier
import syntax.Tree
import syntax.AstSugar
import TypeTranslation.{MicroCode,In,Out,Check}
import TypeTranslation.InOut
import TypeTranslation.{emit,simplify,canonical}
import semantics.TypeTranslation.TypedIdentifier


import AstSugar.Term
import report.console.NestedListTextFormat



object TypePrimitives {
  
  import AstSugar._
  
  /**
   * Strips type of checks to get the unrefined type.
   */
  def rawtype(micro: List[MicroCode]) = micro filter { case In(_) | Out(_) => true case _ => false }
  
  def rawtype(scope: Scope, micro: List[MicroCode]): List[MicroCode] = micro flatMap {
    case In(t) => Some(if (t.isLeaf) In(t) else In(rawtype(scope, t)))
    case Out(t) => Some(if (t.isLeaf) Out(t) else Out(rawtype(scope, t)))
    case _ => None
  }
  
  def rawtype(scope: Scope, typ: Term): Term = 
    TypeTranslation.canonical(rawtype(scope, TypeTranslation.emit(scope, typ)))
    
  def isRaw_shallow(micro: List[MicroCode]) = ! (micro exists { case Check(_,_) => true case _ => false })

  def isRaw_shallow(scope: Scope, typ: Term): Boolean =
    isRaw_shallow(TypeTranslation.emit(scope, typ))
    
  def shape(typ: Term)(implicit scope: Scope): Term = {
    if (typ =~ ("∩", 2)) shape(typ.subtrees(0))
    else if (typ.isLeaf && scope.sorts.contains(typ.root)) 
      T(scope.sorts.getMasterOf(typ.root))
    else
      T(typ.root, typ.subtrees map shape)
  }
    
  /**
   * Counts the arguments of a function type.
   */
  def arity(micro: List[MicroCode]) = micro count { case In(_) => true case _ => false}

  def arity(typ: Term): Int = 
    if (typ.root == "->") (typ.subtrees.length - 1) + arity(typ.subtrees.last)
    else 0
  
  /**
   * Retrieves the argument types of a (raw) function type.
   */
  def args(micro: List[MicroCode]) = micro flatMap { case In(typ) => Some(typ) case _ => None}

  def args(typ: Term): List[Term] =
    if (typ.root == "->") (typ.subtrees dropRight 1) ++ args(typ.subtrees.last)
    else List()
    
  /**
   * Retrieves the return type of a function type.
   */
  def ret(typ: Term): Term =
    if (typ.root == "->") ret(typ.subtrees.last)
    else typ
    
  /**
   * Computes an intersection type in MicroCode form.
   */
  def intersection(decls: List[List[MicroCode]])(implicit scope: Scope): List[MicroCode] = {
    def isCheck(mc: MicroCode) = mc match { case Check(_,_) => true case _ => false }
    def isLeaf(mc: MicroCode) = (mc match { case In(t) => Some(t) case Out(t) => Some(t) case _ => None }) exists (_.isLeaf)
    def dir(mc: MicroCode) = mc match { case In(_) => InOut.IN case Out(_) => InOut.OUT }
    if (decls forall (_.isEmpty)) List()
    else if (decls.tail forall (_ == decls.head)) decls.head
    else if (decls.exists (l => !l.isEmpty && isCheck(l.head)))
      (decls flatMap (_ takeWhile isCheck)) ++ intersection(decls map (_ dropWhile isCheck))
    else {
      val heads = decls map (_.head)
      if (heads forall (_==heads.head)) heads.head :: intersection(decls map (_ drop 1))
      else if (heads forall isLeaf) throw new Scope.TypingException(s"incompatible type instructions: $heads")
      else if (heads forall (dir(_) == InOut.IN)) In(intersection(scope, heads map { case In(t) => t })) :: intersection(decls map (_ drop 1))
      else  ???  /* high-order arguments? */
    }
  }
  
  
  def intersection(scope: Scope, types: List[Term]): Term = {
    import syntax.Piping._
    if (types.tail forall (_ == types.head)) types.head
    else {
      val emits = types map (emit(scope, _))
      intersection(emits)(scope) |> canonical |> (simplify(scope, _))
    }
  }
  
  def curry(typ: Term)(implicit scope: Scope): (Term, Term) = {
    val (arg, ret) = curry(emit(scope, typ))
    (canonical(arg), canonical(ret))
  }
  
  def curry(micro: List[MicroCode])(implicit scope: Scope): (List[MicroCode], List[MicroCode]) = {
    import syntax.Piping._
    def shift1[A](ab: (List[A], List[A])) = (ab._1 :+ ab._2.head, ab._2.tail)
    val (arg, tail) = (micro span { case In(_) => false case _ => true }) |> shift1
    val (checks, res) = tail span { case In(_) | Out(_) => false case _ => true }
    // make 'res' viable by removing any checks that depend on the first argument
    var depth = 0
    val viable = res filter {
      case In(_) | Out(_) => depth += 1 ; true
      case Check(_,arity) => arity <= depth
    }
    (curriedArg(arg ++ checks), viable)
  }
  
  private def curriedArg(micro: List[MicroCode])(implicit scope: Scope) = {
    micro match {
      case In(tpe) :: tail =>
        if (tpe.isLeaf) Out(tpe) :: tail
        else if (!tail.isEmpty) throw new CurryingException(s"cannot curry ${micro}: high-order checks")
        else emit(scope, tpe)
      case _ =>
        throw new CurryingException(s"cannot curry ${micro}: expected In(...)")
    }
  }
 
  
  class CurryingException(msg: String) extends Scope.TypingException(msg)
}


object LambdaCalculus {
  
  import AstSugar._
  
  def beta(va: Identifier, body: Term, arg: Term): Term = {
    if (body.isLeaf && body.root == va) arg
    else T(body.root, body.subtrees map (x => beta(va, x, arg)))
  }
  
  def beta(fun: Term, arg: Term): Term = {
    assume(fun =~ ("↦", 2) && fun.subtrees(0).isLeaf)
    beta(fun.subtrees(0).root, fun.subtrees(1), arg)
  }
    
}

object TypedLambdaCalculus {

  import AstSugar._
  import TypedTerm.preserve

  def beta(va: Identifier, body: Term, arg: Term): Term = {
    if (body.isLeaf && body.root == va) preserve(body, arg)
    else preserve(body, T(body.root, body.subtrees map (x => beta(va, x, arg))))
  }
  
  def beta(fun: Term, arg: Term): Term = {
    assume(fun =~ ("↦", 2) && fun.subtrees(0).isLeaf)
    beta(fun.subtrees(0).root, fun.subtrees(1), arg)
  }

  def simplify(term: Term): Term = {
    if (term =~ ("@", 2) && term.subtrees(0) =~ ("↦", 2)) beta(term.subtrees(0), term.subtrees(1))
    else preserve(term, T(term.root, term.subtrees map simplify))
  }
  
  def replaceDescendant(term: Term, switch: (Term, Term)): Term =
    if (switch._1 eq term) switch._2
    else preserve(term, new Term(term.root, term.subtrees map (replaceDescendant(_, switch))))
  

  def pullOut(term: Term, subterm: Term): Option[Term] = {
    if (term eq subterm) Some(term)
    else if (term =~ ("↦", 2)) 
      pullOut(term.subtrees(1), subterm) map (x => typecheck0(T(term.root, List(term.subtrees(0), x))))
    else term.subtrees map (pullOut(_, subterm)) find (_.isDefined) map (_.get)
  }
  
  def typecheck0(term: Term): Term = {
    if (term =~ ("↦", 2)) term.subtrees map TypedTerm.typeOf match {
      case List(Some(arg_typ), Some(body_typ)) => TypedTerm(term, arg_typ -> body_typ)
      case _ => term
    }
    else term
  }
}


object `package` {
  
  /**
   * Adds the "untype" method to Term.
   */
  implicit class UntypedTerm(private val term: Term) extends AnyVal {
    def untype = term.map({
      case x: TypedIdentifier => x.untype
      case e => e
    })
  }

  /*
   * Helper class that makes objects equatable by reference
   * rather than .equals() for use in HashMap 
   */
  implicit class Id[A <: AnyRef](private val a: A) {
    override def equals(other: Any) = other match {
      case b: Id[_] => a eq b.a
      case b: AnyRef => a eq b
      case _ => false
    }
    override def hashCode = a.hashCode
    def get = a
  }
}

case class TypedTerm(term: Term, val typ: Term)
  extends AstSugar.Term(term.root, term.subtrees) {
  override def toString = s"${super.toString} :: $typ"
  def untype = term.untype
}
  
  
object TypedTerm {

  import AstSugar._
  
  def typeOf(term: Term) = term match {
    case typed: TypedTerm => Some(typed.typ)
    case _ => (term.isLeaf, term.root) match {
      case (true, tid: TypedIdentifier) => Some(tid.typ)
      case _ => None
    }
  }
  
  def typeOf_!(term: Term) = typeOf(term) match {
    case Some(typ) => typ
    case _ => throw new Scope.TypingException(s"type needed for '${term toPretty}'")
  }
  
  def preserve(term: Term, newterm: Term) = (term, term.root) match {
    case (typed: TypedTerm, _) => TypedTerm(newterm, typed.typ)
    case _ => newterm
  }
  
}


/**
 * Used to simplify first-order formulas using standard identities.
 * E.g. x = x     --->  true
 *      P & true  --->  P
 */
object FolSimplify {
  
  import AstSugar._
  import Prelude.{TRUE,FALSE}
  
  def simplify(phi: Term): Term = {
    val sub = phi.subtrees map simplify
    if (phi.root == "&") {
      val nontrue = sub filter (_ != TRUE)
      nontrue match {
        case Nil => TRUE
        case List(x) => x
        case _ => T(phi.root, nontrue)
      }
    }
    else if (phi.root == "|") {
      val nonfalse = sub filter (_ != FALSE)
      nonfalse match {
        case Nil => FALSE
        case List(x) => x
        case _ => T(phi.root, nonfalse)
      }
    }
    else if (phi =~ ("<->", 2) || phi =~ ("=", 2)) {
      if (sub(0) == sub(1)) TRUE
      else T(phi.root, sub)
    }
    else if (phi =~ ("->", 2)) {
      if (sub(0) == TRUE || sub(1) == TRUE) sub(1)
      else if (sub(0) == FALSE) TRUE
      else if (sub(1) == FALSE) ~(sub(0))
      else T(phi.root, sub)
    }
    else if (phi =~ ("~", 1)) {
      if (sub(0) == TRUE) FALSE
      else if (sub(0) == FALSE) TRUE
      else T(phi.root, sub)
    }
    else if (phi.root == "∀") {
      if (sub.last == TRUE) TRUE
      else T(phi.root, sub)
    }
    else T(phi.root, sub)
  }
  
}


/**
 * Represent a proof sub-forest.
 * Can go in either direction: either the roots are assumptions, and children
 * are implied conjectures; or the roots are goals, and the children are
 * sufficient proof obligations.
 */
class Trench[T](val el: List[Tree[T]]) {
  def this(e: List[T])(implicit d: DummyImplicit) = this(e map (x => new Tree[T](x)))
  
  def applyToLeaves(l: List[Tree[T]], f: T => List[T])(implicit rewrap: (T, List[Tree[T]]) => List[Tree[T]]): List[Tree[T]] = 
    l flatMap {t =>
      if (t.isLeaf) rewrap(t.root, f(t.root) map (x => new Tree(x)))
      else List(new Tree(t.root, applyToLeaves(t.subtrees, f)))
    }
  
  def keep(root: T, sub: List[Tree[T]]) = List(new Tree(root, sub))
  def drop(root: T, sub: List[Tree[T]]) = sub
  
  def map(f: T => T) = new Trench[T]( applyToLeaves(el, x => List(f(x)))(drop) )
  def flatMap(f: T => Seq[T]) = new Trench[T]( applyToLeaves(el, x => f(x).toList)(drop) )

  def map_/(f: T => T) = new Trench[T]( applyToLeaves(el, x => List(f(x)))(keep) )
  def flatMap_/(f: T => Seq[T]) = new Trench[T]( applyToLeaves(el, x => f(x).toList)(keep) )
  
  def /:(newRoot: T) = new Trench[T](List(new Tree(newRoot, el)))
  
  def toList = el flatMap (_.leaves map (_.root))
}

object Trench {
  
  import AstSugar._

  def display(tr: Trench[Term], ● : String = "•", indent: String = "  ", level: String = " ") = {
    val fmta = new NestedListTextFormat[Term](●, indent)((_.untype.toPretty))
    for (a <- tr.el) fmta.layOut(a, level)
  }
}
    
