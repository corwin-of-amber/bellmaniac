
package syntax.transform

import syntax.{Tree,Identifier}



class TreeSubstitution[A](substitutions: List[(Tree[A], Tree[A])]) {
  
  def apply(t: Tree[A]): Tree[A] =
    substitutions find (t == _._1) match {
    case Some((x,y)) => y
    case _ => new Tree(t.root, t.subtrees map (this(_)))
  }
}

