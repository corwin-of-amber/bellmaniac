package syntax.transform

import syntax.Identifier
import syntax.AstSugar._
import syntax.Strip



class RenumberLiterals {
  
  val mne = new Mnemonics {
    override def normalize(s: String) = s
    override def indexed(lit: String, index: Int) = lit + Strip.subscriptDecimal(index)
  }
  
  val spare: Set[Any] = Set("<", "?")
  
  def apply(term: Term): Term = {
    val newRoot = if (spare contains term.root.literal) term.root
      else new Identifier(mne.get(term.root), term.root.kind, term.root.ns)
    try T(newRoot, term.subtrees map apply)
    finally mne --= bound(term)
  }
  
  def bound(term: Term) =
    if (term =~ ("↦", 2)) Some(term.subtrees(0).root)
    else None
  
}
