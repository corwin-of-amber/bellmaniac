package semantics.pattern

import syntax.Identifier
import syntax.AstSugar.Term


object `package` {
  type MacroMap = FunctorMap[Identifier, Term]
  object MacroMap {
    def apply(seq: (Identifier, Term ⇒ Option[Term])*) = FunctorMap(seq:_*)
    def empty: MacroMap = FunctorMap.empty
  }
}


trait FunctorMap[A,B] extends Map[A, B ⇒ Option[B]] {
  
  import FunctorMap.make
  
  def impl: Map[A, B => Option[B]]
  
  def liftedOrElse[A,B,C,B1 >: B ⇒ Option[C]](m1: Map[A, B ⇒ Option[C]], m2: TraversableOnce[(A, B ⇒ Option[C])]) = {
    m1 ++ (m2 map { case(k,v2) =>
        m1 get k match {
          case Some(v1) => (k, { (b: B) => v1(b) orElse { v2(b) } })
          case _ => (k, v2)
        }
      })
  }
  
  def ++(that: FunctorMap[A,B]): FunctorMap[A,B] =
    liftedOrElse(impl, that impl) 
  def ++(that: Map[A,B ⇒ Option[B]]): FunctorMap[A,B] =
    liftedOrElse(impl, that) 
  
  /*
  override def ++[B1 >: B => Option[B]](that: GenTraversableOnce[(A, B1)]) = {
    liftedOrElse(this, that seq)
  }
  */
  def +[B1 >: B ⇒ Option[B]](kv: (A, B1)): scala.collection.immutable.Map[A,B1] = ???  
  def -(key: A): scala.collection.immutable.Map[A,B ⇒ Option[B]] = ??? 
  def get(key: A): Option[B ⇒ Option[B]] = impl get key
  def iterator: Iterator[(A, B ⇒ Option[B])] = impl iterator
}

object FunctorMap {
  implicit def make[A, B](map0: Map[A, B ⇒ Option[B]]): FunctorMap[A, B] = new FunctorMap[A, B] { def impl = map0 }
  
  def apply[A,B](seq: (A, B ⇒ Option[B])*): FunctorMap[A,B] = make(seq toMap)
  def empty[A,B]: FunctorMap[A,B] = make(Map())
}


