package syntax.transform

import syntax.{Tree, Identifier}
import syntax.AstSugar._


class Extrude(val ops: Set[Identifier]) {
  
  def apply(term: Term): Tree[Term] = {
    import syntax.Strip.boxedAbc
    val ext = extrude0(term)
    val ph = ext.nodes flatMap (_.root.nodes collect { case x if (x.root == "🅇") => x.root }) distinct
    val mne = ph.zipWithIndex map { case (x, i) => (x, V(boxedAbc(i) toString)) } toMap
    
    ext map (_ map (x => mne.getOrElse(x, x)))
  }
  
  def extrude0(term: Term): Tree[Term] = {
    def xoperands(term: Term): Option[List[Term]] =
      if (ops contains term.root) Some(term.subtrees)
      else if (term =~ ("@", 2)) {
        if (term.subtrees(0).isLeaf && (ops contains term.subtrees(0).root))
          Some(term.subtrees drop 1)
        else xoperands(term.subtrees(0)) map (_ ++ (term.subtrees drop 1))
      }
      else None
    val subterms = xoperands(term) match {
        case Some(operands) => operands map { x => (x, 
          if (x.isLeaf) new Tree(x)
          else if (xoperands(x) isDefined) extrude0(x)
          else {
            val X = $TV("🅇")
            def applyRoot[T](op: T=>T, tree: Tree[T]) = new Tree(op(tree.root), tree.subtrees)
            new Tree(X, List(applyRoot[Term]((X :- _), extrude0(x))))
          }) }
        case _ => term.subtrees map (x => (x, extrude0(x)))
      }
    val xtr = term.replaceDescendants(subterms map (x => (x._1, x._2.root)))
    new Tree(xtr, subterms flatMap (_._2.subtrees))
  }
}

object Extrude {
  def apply(ops: Set[Identifier]) = new Extrude(ops)
}
