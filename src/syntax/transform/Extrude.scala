package syntax.transform

import syntax.{Tree, Identifier}
import syntax.AstSugar._
import semantics.TypedSubstitution
import semantics.TypedTerm
import semantics.Scope


class Extrude(val ops: Set[Identifier]) {
  
  val labelStrip = syntax.Strip.boxedAbcThenUnderbar
  
  def apply(term: Term): ExtrudedTerms = {
    extrude0(term).renumber(labelStrip)
  }
  
  def extrude0(term: Term): ExtrudedTerms = {
    def xoperands(term: Term): Option[List[Term]] =
      if (ops contains term.root) Some(term.subtrees)
      else if (term =~ ("@", 2)) {
        val f :: args = term.subtrees
        if (f.isLeaf && (ops contains f.root)) Some(args)
        else if (f =~ ("@", 2)) xoperands(term.subtrees(0)) map (_ ++ (term.subtrees drop 1))
        else None
      }
      else None
    val subterms = xoperands(term) match {
        case Some(operands) => operands map { x => (x, 
          smallEnough(x) map (x => new ExtrudedTerms(new Tree(x), Map.empty)) getOrElse {
          if (xoperands(x) isDefined) extrude0(x)
          else {
            val X = $TV("🅇")
            def applyRoot[T](op: T=>T, tree: Tree[T]) = new Tree(op(tree.root), tree.subtrees)
            def label(t: Term) = TypedTerm.preserve(t, X :- t)
            val ex = extrude0(x)
            new ExtrudedTerms(new Tree(X, List(applyRoot[Term](label, ex.terms))), ex.labels + (X.root -> x))
          }}) }
        case _ => term.subtrees map (x => (x, extrude0(x)))
      }
    val xtr = new TypedSubstitution(subterms map (x => (x._1, x._2.terms.root)))(term, (_ eq _))
    new ExtrudedTerms(new Tree(xtr, subterms flatMap (_._2.terms.subtrees)), subterms flatMap (_._2.labels) toMap)
  }
  
  def smallEnough(e: Term) = {
    if (e.isLeaf) Some(e)
    else if (e =~ ("↦", 2) && e.subtrees.forall(_.isLeaf) && e.subtrees(0).root == "?") Some(T(dotAbove(e.subtrees(1).root)))
    else None
  }

  def dotAbove(id: Identifier) =
    new Identifier(id.literal + "̇", id.kind, id.ns)

}

object Extrude {
  def apply(ops: Set[Identifier]) = new Extrude(ops)
}


class ExtrudedTerms(val terms: Tree[Term], val labels: Map[Identifier, Term]) {
  
  def :/(label: Any) = labels get I(label) getOrElse {
    throw new Scope.TypingException(s"no sub-term '${label}' in current set")
  }
  
  def terminals = terms.terminals map { x => assume (x =~ (":", 2)); x.subtrees(1) }
  
  def renumber(strip: PartialFunction[Int, String]) = {
    val ph = terms.nodes flatMap (_.root.nodes collect { case x if (x.root == "🅇") => x.root }) distinct
    val mne = ph.zipWithIndex map { case (x, i) => (x, V(strip(i) toString)) } toMap
    val subst = new TypedSubstitution(mne map { case (k,v) => (T(k), T(v)) } toList)
    new ExtrudedTerms(terms map (subst(_)), labels map { case (k,v) => (mne.getOrElse(k, k), v) })
  }
}