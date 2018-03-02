package semantics.pattern

import scala.collection.mutable

import syntax.Identifier
import syntax.AstSugar._
import semantics.{Id, TypedTerm}



object `package` {

  type MacroMap = FunctorMap[Identifier, Contextual, Term]
  object MacroMap {
    def apply(seq: (Identifier, Term ⇒ Option[Term])*) = FunctorMap(seq map {case (i,f) => i->((x:Contextual) => f(x.term))} :_*)
    def +(seq: (Identifier, Contextual ⇒ Option[Term])*) = FunctorMap(seq:_*)
    def empty: MacroMap = FunctorMap.empty
  }

  case class Contextual(term: Term, was: Superposition=Superposition.empty)

  type Superposition = mutable.Map[Id[Term], Term]
  object Superposition { val empty = mutable.Map.empty[Id[Term], Term] }

}


class Expansion(val macros: MacroMap) {
  
  def apply(term: Term) = expand(term)(mutable.Map.empty)

  def expand(term: Term)(implicit was: Superposition): Term = {
    val eterm = TypedTerm.preserve(term, T(term.root, term.subtrees map expand))
    macros get head(eterm) flatMap (_(Contextual(eterm, was))) match {
     case Some(newTerm) => was += ((newTerm, eterm)) ; newTerm
     case _ => eterm
    }
  }

  def head(term: Term): Identifier =
    if (term =~ ("@", 2)) head(term.subtrees(0)) else term.root

}


trait FunctorMap[A,B,C] extends Map[A, B ⇒ Option[C]] {
  
  import FunctorMap.make
  
  def impl: Map[A, B => Option[C]]
  
  def liftedOrElse[A,B,C,B1 >: B ⇒ Option[C]](m1: Map[A, B ⇒ Option[C]], m2: TraversableOnce[(A, B ⇒ Option[C])]) = {
    m1 ++ (m2 map { case(k,v2) =>
        m1 get k match {
          case Some(v1) => (k, { (b: B) => v1(b) orElse { v2(b) } })
          case _ => (k, v2)
        }
      })
  }
  
  def ++(that: FunctorMap[A,B,C]): FunctorMap[A,B,C] =
    liftedOrElse(impl, that impl) 
  def ++(that: Map[A,B ⇒ Option[C]]): FunctorMap[A,B,C] =
    liftedOrElse(impl, that) 
  
  /*
  override def ++[B1 >: B => Option[B]](that: GenTraversableOnce[(A, B1)]) = {
    liftedOrElse(this, that seq)
  }
  */
  def +[B1 >: B ⇒ Option[C]](kv: (A, B1)): scala.collection.immutable.Map[A,B1] = ???
  def -(key: A): scala.collection.immutable.Map[A,B ⇒ Option[C]] = ???
  def get(key: A): Option[B ⇒ Option[C]] = impl get key
  def iterator: Iterator[(A, B ⇒ Option[C])] = impl iterator
}

object FunctorMap {
  implicit def make[A, B, C](map0: Map[A, B ⇒ Option[C]]): FunctorMap[A, B, C] = new FunctorMap[A, B, C] { def impl = map0 }
  
  def apply[A,B,C](seq: (A, B ⇒ Option[C])*): FunctorMap[A,B,C] = make(seq toMap)
  def empty[A,B,C]: FunctorMap[A,B,C] = make(Map())
}


