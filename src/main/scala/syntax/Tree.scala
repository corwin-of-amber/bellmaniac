package syntax

import com.mongodb.{BasicDBObject}
import report.data.{SerializationContainer, AsJson}



class Tree[T](val root: T, val subtrees: List[Tree[T]] = List()) extends AsJson {
  
  def isLeaf = subtrees.isEmpty
  def leaf = { assume(isLeaf); root }
  
  override def equals(other: Any) = other match {
    case other: Tree[T] => other.root == root && other.subtrees == subtrees
    case _ => false
  }
  
  override def hashCode = root.hashCode
  
  def nodes: Stream[Tree[T]] = this #:: {subtrees.toStream flatMap (x => x.nodes)}
  
  def leaves = nodes filter (_.isLeaf)
  def terminals = leaves map (_.root)
  
  def size: Int = 1 + (0 /: (subtrees map (_.size)))(_ + _)
  
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
  
  def unfoldLeft = unfoldLeftN(1)
  def unfoldLeftN(N: Int): Tree[T] = new Tree(root, 
    ((subtrees take N) flatMap {
      t => if (t.root == root) t.unfoldLeftN(N).subtrees else List(t)
    }) ++ (subtrees drop N))
  
  def split = unfold.subtrees
  def split(sep: T): List[Tree[T]] = if (root == sep) split else List(this)
  
  def splitLeft = unfoldLeft.subtrees
  def splitLeft(sep: T): List[Tree[T]] = if (root == sep) splitLeft else List(this)
  
  def hasDescendant(descendant: Tree[T]) = nodes exists (_ eq descendant)
  
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

  override def asJson(container: SerializationContainer) =
    new BasicDBObject("$", "Tree") append ("root", container.any(root)) append
      ("subtrees", container.list(subtrees))
}


object Tree {
  def unapply[T](t: Tree[T]) = Some(t.root, t.subtrees)
}