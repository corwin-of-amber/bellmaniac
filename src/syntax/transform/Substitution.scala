
package syntax.transform

import syntax.{Tree,Identifier}



class GenTreeSubstitution[A](substitutions: List[(Tree[A], (Tree[A] => Tree[A]))]) {
  
  def apply(t: Tree[A]): Tree[A] =
    substitutions find (t == _._1) match {
    case Some((x,y)) => y(x)
    case _ => new Tree(t.root, t.subtrees map (this(_)))
  }
}

class TreeSubstitution[A](substitutions: List[(Tree[A], Tree[A])])
  extends GenTreeSubstitution[A](substitutions.map (kv => (kv._1, (x:Tree[A]) => kv._2)))