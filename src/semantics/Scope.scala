
package semantics

import syntax.{Tree, Identifier, AstSugar}
import syntax.transform.TreeSubstitution



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


class Scope {
  
  import Domains._
  import AstSugar.{T,TreeBuild,Term}
  import Scope.TypingException
  
  var sorts = new Tree(⊤, List(new Tree(⊥)))
  var signature = Map[Identifier,Term]()
  
  def findSortHie(sort: Identifier) = sorts.nodes find (_.root == sort)
  
  private def hei_⊥ = findSortHie(⊥) getOrElse {assert(false, "⊥ is missing!") ; null}
  
  def declareSort(ext: Extends) {
    findSortHie(ext.sup) match {
      case Some(hie) =>
        val hie0 = if (hie.subtrees exists (_.root == ⊥)) T(hie.root)(T(ext.sub)(hei_⊥))
          else hie(T(ext.sub)(hei_⊥))
        sorts = new TreeSubstitution[Identifier](List(hie -> hie0))(sorts)
      case None =>
        throw new TypingException(s"undefined supertype '${ext.sup}'")
    }
  }

  def declareSort(id: Identifier) {
    declareSort(id :<: ⊤)
  }
  
  def containsSort(sort: Identifier) = findSortHie(sort).isDefined
  
  def getDomainsOf(sort: Identifier) =
    for (s <- sorts.subtrees if s.nodes exists (_.root == sort)) yield s.root

  def getDomainOf(sort: Identifier) = getDomainsOf(sort) match {
      case List() => throw new TypingException(s"undefined sort '$sort'")
      case List(x) => x
      case multi => throw new TypingException(s"ambiguous top-level sort for '$sort': $multi")
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
  }
  
}