package syntax

import scala.collection.mutable.HashMap
import scala.collection.mutable.ListMap



abstract class Resolve {
  
  def conflict(x: Tree[Identifier], y: Tree[Identifier], key: Identifier): Option[Map[Identifier, Tree[Identifier]]] = None
  def alternatives(term: Tree[Identifier]): List[Tree[Identifier]] = List()
  def isUnitary(term: Tree[Identifier]) = true
  
}

object Resolve { object NULL extends Resolve{ } }


class Unify(implicit resolve: Resolve = Resolve.NULL) {
  
  private val assignment = new HashMap[Identifier, Tree[Identifier]];
  
  def isVar(x: Tree[Identifier]) = x.isLeaf && x.root.kind == "variable"
  
  def isFreeVar(x: Tree[Identifier]) : Boolean = 
    isVar(x) &&  (assignment get x.root match {
      case None => true
      case Some(y) => assert(x != y, s"$x is mapped back to $y") ; isFreeVar(y)
    })
    
  def canonicalize: Map[Identifier,Tree[Identifier]] = canonicalize(assignment.toMap)
    
  def canonicalize(assignment: Map[Identifier,Tree[Identifier]]): Map[Identifier,Tree[Identifier]] = {
    for ((k, v) <- assignment) yield (k -> (canonicalize(v)))
  }
  
  def canonicalize(term: Tree[Identifier]): Tree[Identifier] = {
    (isVar(term), (assignment get term.root)) match {
      case (true, Some(x)) => canonicalize(x)
      case (true, _) => term
      case _ => new Tree(term.root, term.subtrees map canonicalize)
    }
  }
  
  def makeMgu(x: Tree[Identifier], y: Tree[Identifier], key: Identifier) {
    try {
      makeMgu0(x, y, key)
    }
    catch {
      case e: Unify.CannotUnify =>
        /* try some alternatives before giving up */
        if (!attemptAlternatives(x, y, key)) throw e
    }
  }
  
  def attemptAlternatives(x: Tree[Identifier], y: Tree[Identifier], key: Identifier): Boolean = {
    val altxs = resolve.alternatives(x);
    val altys = resolve.alternatives(y);
    val altxys = (for (altx <- altxs) yield (altx,y)) ++ (for (alty <- altys) yield (x,alty)) ++
      (for {altx <- altxs; alty <- altys} yield (altx, alty))
    for ((altx, alty) <- altxys) try {
      val subunify = fork
      subunify.makeMgu0(altx, alty, key)
      for ((k,v) <- subunify.assignment) assignment += k->v
      return true
    } catch { case _: Unify.CannotUnify => }
    return false
  }
  
  def fork = {
    val c = new Unify
    for ((k,v) <- assignment) c.assignment += k->v
    c
  }
    

  def makeMgu0(x: Tree[Identifier], y: Tree[Identifier], key: Identifier) {
    println(s"makeMgu    $x     $y     ($key)")
    if (isVar(y) && !isVar(x))
      makeMgu(y, x, key)
    else if (isFreeVar(x)) {
      matchUp(x.root, y)
    }
    else if (isVar(x)) {
      assignment get x.root match {
        case Some(v) => makeMgu(v, y, if (key != null) key else x.root)
        case _ => assert(false) /* should not happen since ! isFreeVar(x) */
      }
    }
    else if (x.root == y.root && x.subtrees.length == y.subtrees.length) {
      for ((sx, sy) <- x.subtrees zip y.subtrees)
        makeMgu(sx, sy, null)
    }
    else conflict(x, y, key)
  }
  
  def makeMgu(x: Map[Identifier, Tree[Identifier]], y: Map[Identifier, Tree[Identifier]]) {
    for ((k, vx) <- x) 
      assignment += (k -> vx)
    for ((k, vy) <- y) assignment get k match {
      case None => assignment += (k -> vy)
      case Some(vx) => makeMgu(vx, vy, k)
    }
  }
  
  def rootVar(freeVar: Identifier): Identifier = assignment get freeVar match {
    case None => freeVar
    case Some(y) => rootVar(y.root)
  }
  
  def matchUp(freeVar: Identifier, term: Tree[Identifier]) {
    if (term.isLeaf && term.root == freeVar) return  // do nothing
    if (!resolve.isUnitary(term))
      throw new Unify.CannotUnify(s"cannot assign non-unitary $term to $freeVar")
    assignment += (rootVar(freeVar) -> term)
  }
  
  def conflict(x: Tree[Identifier], y: Tree[Identifier], key: Identifier) {
    resolve.conflict(x,y,key) match { 
      case Some(u) => for ((k,v)<-u) assignment += (k->v)
      case None =>
        throw new Unify.CannotUnify(s"cannot unify $x and $y")
    }
  }
}

object Unify {
  
  class CannotUnify(e: String) extends Exception(e) { }
  
  def mgu(x: Tree[Identifier], y: Tree[Identifier])(implicit resolve: Resolve) = {
    val uni = new Unify
    uni.makeMgu(x, y, null)
    uni.canonicalize
  }
  
  def mgu(x: Map[Identifier, Tree[Identifier]], y: Map[Identifier, Tree[Identifier]])(implicit resolve: Resolve) = {
    println(s"mgu   $x   ~   $y")
    val uni = new Unify
    uni.makeMgu(x, y)
    uni.canonicalize
  }
}