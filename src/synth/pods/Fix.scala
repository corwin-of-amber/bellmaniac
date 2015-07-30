package synth.pods

import syntax.AstSugar._
import syntax.Identifier
import semantics.Prelude
import semantics.Prelude._
import semantics.TypedTerm
import semantics.Scope
import syntax.Scheme
import semantics.TypedLambdaCalculus



/**
 * fix h = fix f » ψ ↦ fix (g ψ)
 */
class StratifyFixPod(val h: Term, val f: Term, val g: Term) extends Pod {
  
  val ψ = $TV("ψ")
  
  override val program = 
      fix(h) =:= (TI("let") :- ((ψ ↦ fix (g:@ψ)):@fix(f)))
    
  
  val θ = $TV("θ")
  val ζ = $TV("ζ")
    
  val obligations = Prelude.program(
      (g:@(f:@θ, θ)) =:= (f:@θ),
      (f:@(g:@(ζ,θ))) =:= f:@ζ
    )
}

object StratifyFixPod {
  def apply(h: Term, f: Term, g: Term) = new StratifyFixPod(h, f, g)
}


class StratifySlashPod(val h: Term, val quadrant: Term, val ψ: Term)(implicit scope: Scope) extends Pod {
  
  import TypedTerm.{replaceDescendant,replaceDescendants}
  
  val quadrants = splitSkip(h, I("/"))
  
  val f = replaceDescendants(h, (quadrants filter (_ ne quadrant) map ((_, $TV ↦ ψ))))
  val g = ψ ↦ replaceDescendant(h, (quadrant, $TV ↦ ψ))

  val gψ = replaceDescendant(h, (quadrant, $TV ↦ ψ))
  
  //override val program = StratifyFixPod(h, f, g).program
  override val program = 
      fix(h) =:= (TI("let") :- ((ψ ↦ fix (gψ)):@fix(f)))
  
  def splitSkip(term: Term, sep: Identifier): List[Term] = 
    if (term =~ (":", 2)) splitSkip(term.subtrees(1), sep)
    else if (term.root == sep) term.subtrees flatMap (splitSkip(_, sep))
    else List(term)
}

object StratifySlashPod {
  def apply(h: Term, quadrant: Term, ψ: Term)(implicit scope: Scope) = new StratifySlashPod(h, quadrant, ψ)
}


class TermWithHole(template: Term) extends Scheme.Template(List(TermWithHole.hole.leaf), template) {
  import TermWithHole._
  
  def x̅ = TypedLambdaCalculus.enclosure(template, hole) get
}

object TermWithHole {
  val hole = TI("□")
  
  def puncture(term: Term, subterm: Term)(implicit scope: Scope) =
    new TermWithHole(TypedTerm.replaceDescendant(term, (subterm, hole)))
}

class StratifyReducePod(val e: TermWithHole, val reduce: Term, val elements: List[Term], val subelements: List[Term], val ψ: Term) extends Pod {

  import ConsPod.`⟨ ⟩`
  
  val x̅ = e.x̅
  
  val h = e(reduce:@`⟨ ⟩`(elements))
  val f = x̅ ↦: (reduce:@`⟨ ⟩`(subelements))
  val gψ = e(reduce:@`⟨ ⟩`((ψ:@(x̅ drop 1)) +: (elements filter (x => !subelements.exists(_ == x)))))

  override val program = 
      fix(h) =:= (TI("let") :- ((ψ ↦ fix (gψ)):@fix(f)))
}

object StratifyReducePod {
  def apply(e: TermWithHole, reduce: Term, elements: List[Term], subelements: List[Term], ψ: Term) = 
    new StratifyReducePod(e, reduce, elements, subelements, ψ)
}
