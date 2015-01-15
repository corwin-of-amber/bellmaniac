package syntax

import scala.collection.mutable.HashMap
import scala.collection.mutable.ListMap
import semantics.Namespace



abstract class Resolve {
  
  def conflict(x: Tree[Identifier], y: Tree[Identifier], keys: List[Identifier]): Option[Map[Identifier, Tree[Identifier]]] = None
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
  
  def makeMgu(x: Tree[Identifier], y: Tree[Identifier], keys: List[Identifier]) {
    try {
      makeMgu0(x, y, keys)
    }
    catch {
      case e: Unify.CannotUnify =>
        /* try some alternatives before giving up */
        if (!attemptAlternatives(x, y, keys)) throw e
    }
  }
  
  def attemptAlternatives(x: Tree[Identifier], y: Tree[Identifier], keys: List[Identifier]): Boolean = {
    val altxs = resolve.alternatives(x);
    val altys = resolve.alternatives(y);
    val altxys = (for (altx <- altxs) yield (altx,y)) ++ (for (alty <- altys) yield (x,alty)) ++
      (for {altx <- altxs; alty <- altys} yield (altx, alty))
    for ((altx, alty) <- altxys) try {
      val subunify = fork
      subunify.makeMgu0(altx, alty, keys)
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
    

  def makeMgu0(x: Tree[Identifier], y: Tree[Identifier], keys: List[Identifier]) {
    //println(s"makeMgu    $x     $y     (${keys mkString ","})")
    if (isVar(y) && !isVar(x))
      makeMgu(y, x, keys)
    else if (isFreeVar(y) && !isFreeVar(x))
      makeMgu(y, x, keys)
    else if (isFreeVar(x)) {
      /*if (isFreeVar(y))
        tie(x.root, y.root)
      else*/
        matchUp(x.root, y)
    }
    else if (isVar(x)) {
      assignment get x.root match {
        case Some(v) => makeMgu(v, y, x.root :: keys)
          //if (key != null && x.root != key) assignment += (x.root -> new Tree(key))
        case _ => assert(false) /* should not happen since ! isFreeVar(x) */
      }
    }
    else if (x.root == y.root && x.subtrees.length == y.subtrees.length) {
      for ((sx, sy) <- x.subtrees zip y.subtrees)
        makeMgu(sx, sy, List())
    }
    else conflict(x, y, keys)
  }
  
  def makeMgu(x: Map[Identifier, Tree[Identifier]], y: Map[Identifier, Tree[Identifier]]) {
    for ((k, vx) <- x) 
      assignment += (k -> vx)
    for ((k, vy) <- y) assignment get k match {
      case None => assignment += (k -> vy)
      case Some(vx) => makeMgu(vx, vy, List(k))
    }
  }
  
  def digest(x: Map[Identifier, Tree[Identifier]]) {
    for ((k,v) <- x) assignment get k match {
      case None => assignment += (k -> v)
      case Some(vx) => makeMgu(vx, v, List(k))
    }
  }
  
  def rootVar(freeVar: Identifier): Identifier = assignment get freeVar match {
    case None => freeVar
    case Some(y) => rootVar(y.root)
  }
  
  def matchUp(freeVar: Identifier, term: Tree[Identifier]) {
    val key = rootVar(freeVar)
    if (term.isLeaf && term.root == key) return  // do nothing
    if (!resolve.isUnitary(term))
      throw new Unify.CannotUnify(s"cannot assign non-unitary $term to $freeVar")
    assignment += (rootVar(freeVar) -> term)
  }
  
  def tie(x: Identifier, y: Identifier) {
    val (rx, ry) = (rootVar(x), rootVar(y))
    if (rx != ry) {
      val fresh = new Tree(new Identifier(Unify.uniq, "variable", new Namespace))
      Unify.uniq += 1
      assignment += (rx -> fresh) += (ry -> fresh)
    }
  }
  
  def conflict(x: Tree[Identifier], y: Tree[Identifier], keys: List[Identifier]) {
    resolve.conflict(x,y,keys) match { 
      case Some(u) => for ((k,v)<-u) assignment += (k->v)
      case None =>
        throw new Unify.CannotUnify(s"cannot unify $x and $y")
    }
  }
}

object Unify {
  
  var uniq: Int = 0;
  
  class CannotUnify(e: String) extends Exception(e) { }
  
  def mgu(x: Tree[Identifier], y: Tree[Identifier])(implicit resolve: Resolve) = {
    val uni = new Unify
    uni.makeMgu(x, y, List())
    uni.canonicalize
  }
  
  def mgu(x: Map[Identifier, Tree[Identifier]], y: Map[Identifier, Tree[Identifier]])(implicit resolve: Resolve) = {
    println(s"mgu   $x   ~   $y")
    val uni = new Unify
    uni.makeMgu(x, y)
    uni.canonicalize
  }

  // does not canonicalize
  def mgu0(x: Map[Identifier, Tree[Identifier]], y: Map[Identifier, Tree[Identifier]])(implicit resolve: Resolve) = {
    println(s"mgu   $x   ~   $y")
    val uni = new Unify
    uni.makeMgu(x, y)
    uni.assignment.toMap
  }

}