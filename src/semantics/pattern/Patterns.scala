package semantics.pattern

import syntax.{Identifier, Tree}
import syntax.AstSugar._
import semantics.TypeTranslation.Environment
import semantics.TypeTranslation.TypedTerm


class ExactMatch(val pattern: Term) {
  def matchInclTypes(symbol1: Identifier, symbol2: Identifier, rebinds: Map[Identifier, Identifier]): Boolean = 
    rebinds.getOrElse(symbol1, symbol1) == symbol2
  
  def matchInclTypes(term1: Term, term2: Term, rebinds: Map[Identifier, Identifier]=Map())(implicit env: Environment): Boolean = {
    if      (term1 =~ (":", 2)) matchInclTypes(term1.subtrees(1), term2, rebinds)
    else if (term2 =~ (":", 2)) matchInclTypes(term1, term2.subtrees(1), rebinds)
    else if (matchInclTypes(term1.root, term2.root, rebinds) && env.typeOf(term1) == env.typeOf(term2) &&
      (term1.subtrees.length == term2.subtrees.length)) {
      val rebinds0 = rebinds ++ (if (term1 =~ ("↦", 2)) Map(term1.subtrees(0).leaf -> term2.subtrees(0).leaf) else Map())
      (term1.subtrees zip term2.subtrees forall { case (x,y) => matchInclTypes(x, y, rebinds0) })
    }
    else false
  }
  
  def find(term: Term)(implicit env: Environment=Environment.Empty) =
    term.nodes filter (matchInclTypes(pattern, _))
}

class SimplePattern(val pattern: Term) {
    
  def find(term: Term) = {
    term.nodes collect { n => apply(n) match {
      case Some(x) => new Matched(n, x)
    }}
  }
    
  def apply(term: Term): Option[Map[Identifier, Term]] = apply(pattern, term, true)
  
  def apply(pattern: Term, term: Term, top: Boolean=false): Option[Map[Identifier, Term]] = {
    if      (pattern =~ (":", 2)) apply(pattern.subtrees(1), term, top) map (_ + (key(pattern) -> term))
    else if (term =~ (":", 2) && !top) apply(pattern, term.subtrees(1))
    else if (term =~ ("::", 2) && !top) apply(pattern, term.subtrees(0))
    else if (pattern =~ ("?", 0) && filter(pattern, term)) Some(Map())
    else if (pattern.root.literal == term.root.literal && filter(pattern, term)) {
      if (pattern.subtrees == List(`...`)) 
        Some(Map())
      else if (pattern.subtrees.length == term.subtrees.length) {
        val sub = pattern.subtrees zip term.subtrees map { case (x,y) => apply(x,y) }
        val init: Option[Map[Identifier, Term]] = Some(Map())
        (init /: sub){
          case (Some(m1), Some(m2)) => Some(m1 ++ m2)
          case _ => None
        }
      }
      else None
    }
    else None
  }
  
  def key(pattern: Term) = {
    /**/ assume(pattern =~ (":", 2)) /**/
    pattern.subtrees(0).leaf
  }
  
  def filter(pattern: Term, term: Term) = true
}

object SimplePattern {
  def apply(pattern: Term) = new SimplePattern(pattern)
}


class SimpleTypedPattern(pattern: Term) extends SimplePattern(pattern) {
  override def filter(pattern: Term, term: Term) = (pattern, term) match {
    case (typat: TypedTerm, tyterm: TypedTerm) => typat.typ == tyterm.typ
    case (_: TypedTerm, _) => false
    case _ => true
  }
}

object SimpleTypedPattern { def apply(pattern: Term) = new SimpleTypedPattern(pattern); }

/**
 * Represents a successful match.
 */
class Matched(val subterm: Term, val groups: Map[Identifier, Term]) {
  override def toString = subterm.toString
  def toPretty = 
    if (groups.isEmpty) subterm.toPretty
    else s"${subterm.toPretty} 〔${groups map {case(x,y)=>s"$x=${y.toPretty}"} mkString ", "}〕"
    
  def apply(label: Identifier) = groups get label getOrElse
    { throw new Exception(s"no matched label '$label' (in ${toPretty})") }
  def apply(label: Term): Term = apply(label.leaf)
  def apply(label: Any) = groups find (_._1 == label) map (_._2) getOrElse 
    { throw new Exception(s"no matched label '$label' (in ${toPretty})") }
}
  
