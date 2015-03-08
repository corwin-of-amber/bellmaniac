package syntax

import scala.util.hashing.Hashing

class Tree[T] (val root: T, val subtrees: List[Tree[T]] = List()) {
  
  def isLeaf = subtrees.isEmpty
  def leaf = { assume(isLeaf); root }
  
  override def equals(other: Any) = other match {
    case other: Tree[T] => other.root == root && other.subtrees == subtrees
    case _ => false
  }
  
  override def hashCode = root.hashCode
  
  def nodes: Stream[Tree[T]] = this #:: {subtrees.toStream flatMap (x => x.nodes)}
  
  def bfs: Stream[Tree[T]] = {
    def tbf(l: Stream[Tree[T]]): Stream[Tree[T]] = 
      if (l.isEmpty) Stream.empty else l ++ tbf(l flatMap (_.subtrees))
    tbf(Stream(this))
  }
  
  override def clone = map (x => x)
  
  def map[S](op: T => S) : Tree[S] =
    new Tree(op(root), subtrees map (_ map op))
  
  def foldLeft = subtrees reduceLeft ((x,y) => new Tree(root, List(x, y)))
  def foldRight = subtrees reduceRight ((x,y) => new Tree(root, List(x, y)))
  
  def unfold: Tree[T] = new Tree(root, subtrees flatMap { 
      t => if (t.root == root) t.unfold.subtrees else List(t)
    })
  
  def unfoldRight = unfoldRightN(1)
  def unfoldRightN(N: Int): Tree[T] = new Tree(root, (subtrees dropRight N) ++ 
      (subtrees takeRight N) flatMap { 
      t => if (t.root == root) t.unfoldRightN(N).subtrees else List(t)
    })
  
  def split = unfold.subtrees
  def split(sep: T): List[Tree[T]] = if (root == sep) split else List(this)
  
  def replaceDescendant(switch: (Tree[T], Tree[T])): Tree[T] =
    if (switch._1 eq this) switch._2
    else new Tree(root, subtrees map (_.replaceDescendant(switch))) 
  
  def replaceDescendants(switch: List[(Tree[T], Tree[T])]): Tree[T] =
    switch find (_._1 eq this) match {
      case Some(sw) => sw._2
      case _ => new Tree(root, subtrees map (_.replaceDescendants(switch)))
    }
  
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
