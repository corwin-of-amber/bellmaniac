package semantics

import report.data.SerializationContainer
import semantics.Scope.TypingException
import syntax.Identifier
import syntax.Tree
import syntax.AstSugar
import syntax.Scheme
import TypeTranslation.{MicroCode,In,Out,Check}
import TypeTranslation.InOut
import TypeTranslation.{emit,simplify,canonical}
import AstSugar.Term
import report.console.NestedListTextFormat
import syntax.transform.TreeSubstitution
import semantics.pattern.MacroMap
import semantics.pattern.Expansion



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
    val subs = typ.subtrees.toStream map shape
    if (typ =~ ("∩", 2)) subs(0)
    else if (typ =~ ("->", 2) && subs(0).root == "×")
      shape((subs(0).subtrees :\ typ.subtrees(1))(_ -> _))
    else if (typ.isLeaf && scope.sorts.contains(typ.root)) 
      T(scope.sorts.getMasterOf(typ.root))
    else
      T(typ.root, subs toList)
  }

  def canonical(micro: List[MicroCode])(implicit scope: Scope): Term =
    TypeTranslation.canonical(scope, micro)
  def canonical(typ: Term)(implicit scope: Scope): Term =
    TypeTranslation.canonical(scope, TypeTranslation.emit(scope, typ))

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
    if (typ.root == "->") (typ.subtrees dropRight 1 flatMap dim) ++ args(typ.subtrees.last)
    else List()
    
  /**
   * Retrieves the return type of a function type.
   */
  def ret(typ: Term): Term =
    if (typ.root == "->") ret(typ.subtrees.last)
    else typ

  /**
   * Retrieves the domain expression of a function type.
   * E.g. dom(J ->: J ->: R) == J x J
   *      dom(I ->: ((J x J) ∩ <) ->: B) == I x ((J x J) ∩ <)
   */
  def dom(typ: Term): Term = {
    def comps(typ: Term): List[Term] =
      if (typ.root == "->") (typ.subtrees dropRight 1) ++ comps(typ.subtrees.last)
      else List()
    comps(typ) reduceOption (_ x _) getOrElse { throw new TypingException("not a function type") at typ }
  }

  def dim(typexpr: Term): List[Term] =
    if (typexpr.root == "×") typexpr.subtrees flatMap dim
    else if (typexpr.root == "∩") {
      val dims = dim(typexpr.subtrees(0))
      if (dims.length == 1) List(typexpr) else dims
    }
    else List(typexpr)

  /**
   * Computes an intersection type in MicroCode form.
   */
  def intersection(decls: List[List[MicroCode]])(implicit scope: Scope): List[MicroCode] = {
    def isCheck(mc: MicroCode) = mc match { case Check(_,_) => true case _ => false }
    def isLeaf(mc: MicroCode) = (mc match { case In(t) => Some(t) case Out(t) => Some(t) case _ => None }) exists (_.isLeaf)
    def dir(mc: MicroCode) = mc match { case In(_) => InOut.IN case Out(_) => InOut.OUT }
    if (decls forall (_.isEmpty)) List()
    else if (decls.tail forall (_ == decls.head)) decls.head
    else if (decls.exists (l => l.nonEmpty && isCheck(l.head)))
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
    implicit val sc = scope
    if (types.tail forall (_ == types.head)) types.head
    else {
      val emits = types map (emit(scope, _))
      intersection(emits)(scope) |> canonical |> (simplify(scope, _))
    }
  }
  
  
  def union(decls: List[List[MicroCode]])(implicit scope: Scope): List[MicroCode] = {
    def isCheck(mc: MicroCode) = mc match { case Check(_,_) => true case _ => false }
    def isLeaf(mc: MicroCode) = (mc match { case In(t) => Some(t) case Out(t) => Some(t) case _ => None }) exists (_.isLeaf)
    def dir(mc: MicroCode) = mc match { case In(_) => InOut.IN case Out(_) => InOut.OUT }
    def common(l: List[List[MicroCode]]) = l.head filter (x => l.tail forall (_ contains x))
    def govern(l: List[List[MicroCode]]) = l map
      { _ collectFirst { case Check(T(s,Nil), 1) if scope.sorts.contains(s) => s } getOrElse Domains.⊤ } reduce scope.sorts.join match {
      case Domains.⊤ => None case s => Some(Check(T(s), 1)) }
    def join(l: List[List[MicroCode]]) = govern(l).toList union common(l)

    if (decls forall (_.isEmpty)) List()
    else if (decls.tail forall (_ == decls.head)) decls.head
    else if (decls.exists (l => l.nonEmpty && isCheck(l.head)))
      join(decls map (_ takeWhile isCheck)) ++ union(decls map (_ dropWhile isCheck))
    else {
      val heads = decls map (_.head)
      if (heads forall (_==heads.head)) heads.head :: union(decls map (_ drop 1))
      else if (heads forall isLeaf) throw new Scope.TypingException(s"incompatible type instructions: $heads")
      else if (heads forall (dir(_) == InOut.IN)) In(union(scope, heads map { case In(t) => t })) :: union(decls map (_ drop 1))
      else  ???  /* high-order arguments? */
    }
  }  
  
  def union(scope: Scope, types: List[Term]): Term = {
    import syntax.Piping._
    implicit val sc = scope
    if (types.tail forall (_ == types.head)) types.head
    else {
      val emits = types map (emit(scope, _))
      union(emits)(scope) |> canonical |> (simplify(scope, _))
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
    
  // returns args and body
  def uncurry(fun: Term): (List[Term], Term) = {
    if (fun =~ ("↦", 2))
      uncurry(fun.subtrees(1)) match { case (args, body) => (fun.subtrees(0) :: args, body) }
    else if (fun =~ (":", 2)) uncurry(fun.subtrees(1))
    else (List(), fun)
  }
  
  // destructs application terms
  def isApp(t: Term): Option[(Term, List[Term])] = 
    if (t =~ ("@", 2)) isApp(t.subtrees(0)) match {
      case Some((f, args)) => Some((f, args :+ t.subtrees(1)))
      case _ => Some((t.subtrees(0), t.subtrees drop 1))
    }
    else if (t =~ (":", 2)) isApp(t.subtrees(1))
    else None

  // destructs application terms with a specific head    
  def isAppOf(t: Term, f: Term): Option[List[Term]] =
    isApp(t) collect { case (f0, args) if f0 == f => args }

  // destructs abstraction terms
  def isAbs(t: Term): Option[(List[Term], Term)] =
    if (t =~ ("↦", 2)) Some(uncurry(t))
    else if (t =~ (":", 2)) isAbs(t.subtrees(1))
    else None

  def freevars(t: Term): Set[Term] =
    if (t.isLeaf) Set(t)
    else if (t =~ ("↦", 2)) freevars(t.subtrees(1)) - t.subtrees(0)
    else if (t =~ (":", 2)) freevars(t.subtrees(1))
    else t.subtrees flatMap freevars toSet
}

object TypedLambdaCalculus {

  import AstSugar._
  import TypedTerm.{preserve,preserveBoth}

  def beta(va: Identifier, body: Term, arg: Term, retype: Boolean=false): Term = {
    if (body.isLeaf && body.root == va) (if (retype) arg else preserve(body, arg))
    else preserve(body, T(body.root, body.subtrees map (x => beta(va, x, arg, retype))))
  }
  
  def beta(fun: Term, arg: Term): Term = {
    assume(fun =~ ("↦", 2))
    getDeclaredVariable(fun.subtrees(0)) match {
      case Some(va) => beta(va, fun.subtrees(1), arg)
      case _ => throw new Scope.TypingException(s"not an argument declaration: '${fun.subtrees(0) toPretty}'")
    }
  }

  def getDeclaredVariable(t: Term): Option[Identifier] = {
    if (t.isLeaf) Some(t.root)
    else if (t =~ ("::", 2)) getDeclaredVariable(t.subtrees(0))
    else None
  }
    
  def simplify(term: Term)(implicit scope: Scope): Term = {
    val sub = term.subtrees map simplify
    if (term =~ ("@", 2) && sub(0) =~ ("↦", 2)) beta(sub(0), sub(1))
    else if (term =~ (":", 2)) sub(1) // TODO only throw away labels when necessary?
    else preserveBoth(term, T(term.root, sub))
  }
  

  def enclosure(term: Term, subterm: Term): Option[List[Term]] = {
    if (term eq subterm) Some(List())
    else if (term =~ ("↦", 2))
      enclosure(term.subtrees(1), subterm) map (term.subtrees(0) :: _)
    else term.subtrees map (enclosure(_, subterm)) find (_.isDefined) map (_.get)
  }

  def context(term: Term, subterm: Term): Map[Any, Term] =
    enclosure(term, subterm) getOrElse List() map (x => (x.leaf.literal, x)) toMap

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
    def untype = term map {
      case x: TypedIdentifier => x.untype
      case e => e
    }
    def untypeShallow = new Term(term.root, term.subtrees)
    def typedLeaf = term.leaf match {
      case tid: TypedIdentifier => tid
      case u => TypedIdentifier(u, TypedTerm.typeOf_!(term))
    }
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

case class TypedIdentifier(symbol: Identifier, typ: Term)
  extends Identifier(symbol.literal, symbol.kind, symbol.ns) {
  import AstSugar._
  override def toString() = s"${super.toString()} :: $typ"
  def toPretty = s"${super.toString()} :: ${typ.toPretty}"
  def untype = new Identifier(symbol.literal, symbol.kind, symbol.ns)

  override def asJson(container: SerializationContainer) =
    super.asJson(container).append("type", typ.asJson(container))
}

case class TypedTerm(term: Term, typ: Term)
  extends AstSugar.Term(term.root, term.subtrees) {
  override def toString() = s"${super.toString()} :: $typ"
  override def asJson(container: SerializationContainer) =
    super.asJson(container).append("type", container.anyRef(typ))
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
  
  def replaceDescendant(term: Term, switch: (Term, Term))(implicit scope: Scope): Term = replaceDescendants(term, Some(switch))

  def replaceDescendants(term: Term, switch: Iterable[(Term, Term)])(implicit scope: Scope): Term = if (switch.isEmpty) term else
    switch find (_._1 eq term) match {  // TODO implicit Scope unneeded here?
      case Some(sw) => preserveBoth(term, sw._2)
      case _ => preserve(term, new Tree(term.root, term.subtrees map (replaceDescendants(_, switch))))
    }

  // This is actually just like "Tree.split" but it skips ":" nodes.
  def split(term: Term, sep: Identifier): List[Term] =
    if (term =~ (":", 2)) split(term.subtrees(1), sep)
    else if (term.root == sep) term.subtrees flatMap (split(_, sep))
    else List(term)

  // Likewise, "eq" that skips ":"
  def eq(termA: Term, termB: Term): Boolean =
    if (termA =~ (":", 2)) eq (termA.subtrees(1), termB)
    else if (termB =~ (":", 2)) eq (termA, termB.subtrees(1))
    else termA eq termB

  def preserve(term: Term, newterm: Term) = typeOf(term) match {
    case Some(typ) => TypedTerm(newterm, typ)
    case _ => newterm
  }
  
  def preserveBoth(term: Term, newterm: Term)(implicit scope: Scope) = (term, newterm) match {
    case (typed: TypedTerm, newtyped: TypedTerm) => 
      TypedTerm(newterm, TypePrimitives.intersection(scope, List(typed.typ, newtyped.typ)))
    case (typed: TypedTerm, _) => TypedTerm(newterm, typed.typ)
    case _ => newterm
  }

  def raw(t: Term)(implicit scope: Scope): Term = typeOf(t) match {
    case Some(typ) => TypedTerm(T(t.root, t.subtrees map raw), TypePrimitives.shape(typ))
    case _ => T(t.root, t.subtrees map raw)
  }

}


object TypedScheme {
  import AstSugar._
  
  class Template(vars: List[Identifier], template: Term) extends Scheme.Template(vars, template) {
    override def apply(args: Term*): Term = {
      val subst = new TypedSubstitution(vars map (T(_)) zip args)
      subst(template)
    }
  }

  class TermWithHole(template: Term) extends TypedScheme.Template(List(TermWithHole.hole.leaf), template) {
  
    val hole = template.nodes find (_ == TermWithHole.hole) get
    
    def x̅ = TypedLambdaCalculus.enclosure(template, hole) get
  }
  
  
  object TermWithHole {
    import AstSugar._
    val hole = TI("□")
    
    def puncture(term: Term, subterm: Term)(implicit scope: Scope) =
      new TermWithHole(TypedTerm.replaceDescendant(term, (subterm, hole)))
  }
}


class TypedSubstitution(substitutions: List[(Term, Term)]) extends TreeSubstitution[Identifier](substitutions) {
  override def preserve(old: Term, new_ : Term) = TypedTerm.preserve(old, new_)
}

class ProgressiveTypedSubstitution(substitutions: List[(Term, Term)])(implicit scope: Scope)
    extends TreeSubstitution[Identifier](substitutions) {
  override def preserve(old: Term, new_ : Term) = TypedTerm.preserveBoth(old, new_)
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
    if (phi.root == "∧") {
      val nontrue = sub filter (_ != TRUE)
      nontrue match {
        case Nil => TRUE
        case List(x) => x
        case _ => T(phi.root, nontrue)
      }
    }
    else if (phi.root == "∨") {
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
      val body = sub.last
      if (body == TRUE) TRUE
      else T(phi.root, sub)
    }
    else T(phi.root, sub)
  }
  
  class Trivial
  case object Identity extends Trivial
  case class Constant(term: Term) extends Trivial
  
  def expandTrivials(theory: Iterable[Term]) = {
    def collect(phi: Term)(implicit vars: List[Term]): Map[Identifier, Trivial] = {
      if (phi.root == "∧") phi.subtrees flatMap collect toMap
      else if (phi =~ ("=", 2) || phi =~ ("<->", 2)) {
        val List(lhs, rhs) = phi.subtrees
        if (lhs.subtrees == vars) {
          if (rhs == TRUE || rhs == FALSE) Map(lhs.root -> Constant(rhs))
          else if (vars.length == 1 && rhs == vars(0)) Map(lhs.root -> Identity)
          else Map()
        }
        else Map()
      }
      if (phi =~ ("∀", 2)) collect(phi.subtrees(1))(vars :+ phi.subtrees(0))
      else Map()
    }
    val macros = theory flatMap (collect(_)(List())) map { 
      case (id, Constant(term)) => (id -> ((x:Term) => Some(term) )) 
      case (id, Identity) => (id -> ((x:Term) => Some(x.subtrees(0))))
    } toSeq
    
    new Expansion( MacroMap(macros:_*) )
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
  
  def ++(that: Trench[T]) = new Trench[T](el ++ that.el)
  
  def applyToLeaves(l: List[Tree[T]], f: T => List[T])(implicit rewrap: (T, List[Tree[T]]) => List[Tree[T]]): List[Tree[T]] = 
    l flatMap {t =>
      if (t.isLeaf) rewrap(t.root, f(t.root) map (x => new Tree(x)))
      else List(new Tree(t.root, applyToLeaves(t.subtrees, f)))
    }
  
  def filterLeaves(t: Tree[T], p: T => Boolean): Option[Tree[T]] = 
    if (t.isLeaf) (if (p(t.root)) Some(t) else None)
    else t.subtrees flatMap (filterLeaves(_, p)) match {
      case Nil => None
      case subs => Some(new Tree(t.root, subs))
    }
  
  def keep(root: T, sub: List[Tree[T]]) = List(new Tree(root, sub))
  def drop(root: T, sub: List[Tree[T]]) = sub
  
  def map(f: T => T) = new Trench[T]( applyToLeaves(el, x => List(f(x)))(drop) )
  def flatMap(f: T => Seq[T]) = new Trench[T]( applyToLeaves(el, x => f(x).toList)(drop) )

  def map_/(f: T => T) = new Trench[T]( applyToLeaves(el, x => List(f(x)))(keep) )
  def flatMap_/(f: T => Seq[T]) = new Trench[T]( applyToLeaves(el, x => f(x).toList)(keep) )
  
  def filter(p: T => Boolean) = new Trench[T]( el flatMap (filterLeaves(_, p)))
  
  def /:(newRoot: T) = new Trench[T](List(new Tree(newRoot, el)))
  
  def toList = el flatMap (_.leaves map (_.root))
}

object Trench {
  
  import AstSugar._

  def display(tr: Trench[Term], ● : String = "•", indent: String = "  ", level: String = " ") = {
    val fmta = new NestedListTextFormat[Term](●, indent)((_.untype.toPretty))
    for (a <- tr.el) fmta.layOut(a, level)
  }
  
  def displayRich(tr: Trench[Term], bullet: String = "•") = {
    import report.{ObjectTree,ObjectVBox,BulletDecorator}
    new ObjectVBox(tr.el map (t => 
      new ObjectTree(t map (_.toPrettyTape))
        with BulletDecorator { override val ● = bullet }))
  }
}
    
