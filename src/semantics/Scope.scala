
package semantics

import syntax.{Tree, Identifier, AstSugar}
import syntax.transform.TreeSubstitution
import semantics.TypeTranslation.TypedIdentifier
import semantics.TypeTranslation.Declaration



object Domains {
  val TOP = new Identifier("⊤", "set")
  val BOT = new Identifier("⊥", "set")
  
  val ⊤ = TOP
  val ⊥ = BOT
  
  class Extends(val sub: Identifier, val sup: Identifier) {}
  
  implicit class SubsortAssoc(private val sup: Identifier) extends AnyVal {
    def :<: (sub: Identifier) = new Extends(sub, sup)
  }
}



class Domains {

  import Domains._
  import AstSugar.{T,TreeBuild,Term}
  import Scope.TypingException

  var hierarchy = new Tree(⊤, List(new Tree(⊥)))

  def findSortHie(sort: Identifier) = hierarchy.nodes find (_.root == sort)
  
  private def hei_⊥ = findSortHie(⊥) getOrElse {assert(false, "⊥ is missing!") ; null}
  
  def declare(ext: Extends) {
    findSortHie(ext.sup) match {
      case Some(hie) =>
        val hie0 = if (hie.subtrees exists (_.root == ⊥)) T(hie.root)(T(ext.sub)(hei_⊥))
          else hie(T(ext.sub)(hei_⊥))
        hierarchy = new TreeSubstitution[Identifier](List(hie -> hie0))(hierarchy)
      case None =>
        throw new TypingException(s"undefined supertype '${ext.sup}'")
    }
  }

  def declare(id: Identifier) {
    declare(id :<: ⊤)
  }
  
  def contains(sort: Identifier) = findSortHie(sort).isDefined
  
  def masters = hierarchy.subtrees
  
  def getMastersOf(sort: Identifier) =
    if (sort == ⊤) List(⊤)
    else
      for (s <- hierarchy.subtrees if s.nodes exists (_.root == sort)) yield s.root

  def getMasterOf(sort: Identifier) = getMastersOf(sort) match {
      case List() => throw new TypingException(s"undefined sort '$sort'")
      case List(x) => x
      case multi => throw new TypingException(s"ambiguous top-level sort for '$sort': $multi")
    }
  
  def supers(sort: Identifier) = {
    def f(t: Tree[Identifier]): List[Identifier] = 
      if (t.root == sort) List(t.root)
      else t.subtrees flatMap f match {
        case Nil => Nil
        case l => t.root :: l
      }
    f(hierarchy)
  }
  
  def subs(sort: Identifier) = findSortHie(sort) match {
    case Some(hie) => hie.bfs map (_.root)
    case None => throw new TypingException(s"undefined sort '$sort'")
  }
  
  def join(sort1: Identifier, sort2: Identifier) = {
    val (supers1, supers2) = (supers(sort1), supers(sort2))
    supers1.reverseIterator find supers2.contains _ getOrElse 
      { assert(false, s"$sort1 and $sort2 do not have any common supertype!") ; null }
  }

  def meet(sort1: Identifier, sort2: Identifier) = {
    val (subs1, subs2) = (subs(sort1), subs(sort2))
    subs1 find subs2.contains _ getOrElse
      { assert(false, s"$sort1 and $sort2 do not have any common subtype!") ; null }
  }
  
}

/**
 * A cheating techniques to reason about second-order functions.
 * The function type is represented by a first-order sort that reflects it.
 */
class FunctionType(val args: List[Identifier], val ret: Identifier) {
  import AstSugar._

  val faux = new Identifier((args :+ ret) mkString "→", "set", this)
  val app = new Declaration(
      List(TypedIdentifier( new Identifier("@", "function", this), 
                            TI("->")(faux +: args :+ ret map (T(_))).foldRight ),
           TypedIdentifier( new Identifier("|@|", "predicate", this),
                            TI("->")(faux +: args :+ S("") map (T(_))).foldRight )), List() )
                                 
  def abs(f: Declaration) = {
    import TypeTranslation.{In,Out}
    import TypeTranslation.TypingSugar._
    val f_abs = TypedIdentifier( new Identifier(s"${f.head.untype}#", "function", new Uid), T(faux) )
    val f_abs_supp = TypedIdentifier( new Identifier(s"|${f.head.untype}#|", "predicate", new Uid), T(S("")) )
    val micro = (args map ((x) => In(T(x)))) :+ Out(T(ret))
    val (varids, _, _) = TypeTranslation.contract(f_abs, micro)
    val vars = varids map (T(_))
    val assumptions = List(
        T(f_abs_supp) ,
        ∀(vars)( (T(app.head)(T(f_abs) :: vars) =:= T(f.head)(vars)) &
                 (T(app.support)(T(f_abs) :: vars) <-> T(f.support)(vars))  )
      )
    new Declaration(List(f_abs, f_abs_supp), assumptions)
  }
  
  def abs(f: Identifier) =
    TypedIdentifier( new Identifier(s"${f.literal}#", "function", new Uid), T(faux) )

}

class Scope {
  
  import AstSugar._
  
  val sorts = new Domains
  val functypes = collection.mutable.Map[Term, FunctionType]()
  //var signature = Map[Identifier,Term]()
  
  def declFunctionType(rawType: Term): FunctionType = {
    def arg(e: Term) = if (e.isLeaf) e.root else declFunctionType(e).faux
    functypes get rawType match {
      case Some(functype) => functype
      case _ =>
        val functype = new FunctionType(TypePrimitives.args(rawType) map arg, arg(TypePrimitives.ret(rawType)))
        functypes += ((rawType, functype))
        functype
    }
  }
}

object Scope {
  class TypingException(msg: String) extends Exception(msg) {}
}



object `package` {
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