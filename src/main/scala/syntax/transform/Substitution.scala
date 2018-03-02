
package syntax.transform

import syntax.{Tree,Identifier}



class GenTreeSubstitution[A](substitutions: List[(Tree[A], (Tree[A] => Tree[A]))]) extends Eq[Tree[A]] {
    
  def apply(t: Tree[A]): Tree[A] =
    substitutions find (s => eq(t, s._1)) match {
    case Some((x,y)) => preserve(t, y(x))
    case _ => preserve(t, new Tree(t.root, t.subtrees map apply))
  }
  
  def preserve(old: Tree[A], new_ : Tree[A]) = new_
  
  //def eq(a: Tree[A], b: Tree[A]) = a == b
}

class TreeSubstitution[A](substitutions: List[(Tree[A], Tree[A])])
  extends GenTreeSubstitution[A](substitutions.map (kv => (kv._1, (x:Tree[A]) => kv._2)))


trait Eq[X] { def eq(a: X, b: X) = a == b }
trait EqByRef[X <: AnyRef] extends Eq[X]/*GenTreeSubstitution[A]*/ { override def eq(a: X, b: X) = a eq b }
