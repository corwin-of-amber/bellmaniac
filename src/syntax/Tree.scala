package syntax

import scala.util.hashing.Hashing

class Tree[T] (val root: T, val subtrees: List[Tree[T]] = List()) {
  
  def isLeaf = subtrees.isEmpty
  
  override def equals(other: Any) = other match {
    case other: Tree[T] => other.root == root && other.subtrees == subtrees
    case _ => false
  }
  
  def nodes: Stream[Tree[T]] = this #:: {subtrees.toStream flatMap (x => x.nodes)}
  
  def map[S](op: T => S) : Tree[S] =
    new Tree(op(root), subtrees map (_ map op))
  
  def foldLeft = subtrees reduceLeft ((x,y) => new Tree(root, List(x, y)))
  def foldRight = subtrees reduceRight ((x,y) => new Tree(root, List(x, y)))
  
  def unfold: Tree[T] = new Tree(root, subtrees flatMap { 
      t => if (t.root == root) t.unfold.subtrees else List(t)
    })
  
  override def toString(): String = {
    if (subtrees.isEmpty) root.toString
    else {
      val children = subtrees mkString ", "
      s"$root{$children}"
    }
  }
}

class Identifier (val literal: Any, val kind: String = "?", val ns: AnyRef = null) {
  override def toString() = literal.toString
  
  override def equals(other: Any) = other match {
    case other: Identifier => 
      literal == other.literal && 
        (kind == "?" || other.kind == "?" || kind == other.kind) &&
        ns == other.ns
      
    case x => literal == x
  }

  override def hashCode = 0 
  // (literal, kind, ns).hashCode  
  //TODO: for some reason the commented version causes unification to run much slower??
}
