package synth.pods

import syntax.AstSugar._
import semantics.Prelude
import semantics.Prelude._
import semantics.TypedTerm
import semantics.Scope
import semantics.TypedScheme.TermWithHole



/**
 * fix h = fix f » ψ ↦ fix (g ψ)
 */
class StratifyFixPod(val h: Term, val f: Term, val g: Term) extends Pod {
  
  val ψ = $TV("ψ")
  
  override val program = 
      fix(h) =:= (TI("let") :- ((ψ ↦ fix (g:@ψ)):@fix(f)))
    
  
  val θ = $TV("θ")
  val ζ = $TV("ζ")
    
  override val obligations = Prelude.program(
      (g:@(f:@θ, θ)) =:= (f:@θ),
      (f:@(g:@(ζ,θ))) =:= f:@ζ
    )
}

object StratifyFixPod {
  def apply(h: Term, f: Term, g: Term) = new StratifyFixPod(h, f, g)
}


class StratifySlashPod(val h: Term, val quadrant: Term, val ψ: Term)(implicit scope: Scope) extends Pod {
  
  import TypedTerm.{split,replaceDescendant,replaceDescendants}
  
  val quadrants = split(h, I("/"))
  
  val f = replaceDescendants(h, quadrants filter (_ ne quadrant) map ((_, $TV ↦ ψ)))
  val g = ψ ↦ replaceDescendant(h, (quadrant, $TV ↦ ψ))

  val gψ = replaceDescendant(h, (quadrant, $TV ↦ ψ))
  
  //override val program = StratifyFixPod(h, f, g).program
  override val program = 
      fix(h) =:= (TI("let") :- ((ψ ↦ fix (gψ)):@fix(f)))

  val θ = $TV("θ")
  val ζ = $TV("ζ")

  override val obligations = &&(
      (g:@(f:@θ, θ)) =:= (h:@θ),
      (f:@(g:@(ζ,θ))) =:= (f:@ζ)
    )

}

object StratifySlashPod {
  def apply(h: Term, quadrant: Term, ψ: Term)(implicit scope: Scope) = new StratifySlashPod(h, quadrant, ψ)
}


class StratifyReducePod(val e: TermWithHole, val reduce: Term, val elements: List[Term], val subelements: List[Term], val ψ: Term) extends Pod {

  import ConsPod.`⟨ ⟩`
  
  val x̅ = e.x̅
  
  val h = e(reduce:@`⟨ ⟩`(elements))
  val f = e(reduce:@`⟨ ⟩`(subelements))
  val g = ψ ↦ e(reduce:@`⟨ ⟩`((ψ:@(x̅ drop 1)) +: (elements filter (x => !subelements.exists(_ eq x)))))

  val gψ = e(reduce:@`⟨ ⟩`((ψ:@(x̅ drop 1)) +: (elements filter (x => !subelements.exists(_ eq x)))))

  override val program = 
      fix(h) =:= (TI("let") :- ((ψ ↦ fix (gψ)):@fix(f)))

  val θ = $TV("θ")
  val ζ = $TV("ζ")

  override val obligations = &&(
    (g:@(f:@θ, θ)) =:= (h:@θ),
    (f:@(g:@(ζ,θ))) =:= (f:@ζ)
  )
}

object StratifyReducePod {
  def apply(e: TermWithHole, reduce: Term, elements: List[Term], subelements: List[Term], ψ: Term) = 
    new StratifyReducePod(e, reduce, elements, subelements, ψ)
}


class LetSlashPod(val h: Term, val quadrant: Term, val ψ: Term)(implicit scope: Scope) extends Pod {

  import TypedTerm.{split,replaceDescendant,replaceDescendants}

  val quadrants = split(h, I("/"))

  val f = replaceDescendants(h, quadrants filter (_ ne quadrant) map ((_, ψ)))
  val g = ψ ↦ replaceDescendant(h, (quadrant, ψ))

  val gψ = replaceDescendant(h, (quadrant, ψ))

  override val program =
    h =:= (TI("let") :- (g:@f))

}

object LetSlashPod {
  def apply(h: Term, quadrant: Term, ψ: Term)(implicit scope: Scope) = new LetSlashPod(h, quadrant, ψ)
}


class LetReducePod(val e: TermWithHole, val reduce: Term, val elements: List[Term], val subelements: List[Term], val ψ: Term) extends Pod {

  import ConsPod.`⟨ ⟩`

  val x̅ = e.x̅

  val h = e(reduce:@`⟨ ⟩`(elements))
  val f = e(reduce:@`⟨ ⟩`(subelements))
  val g = ψ ↦ e(reduce:@`⟨ ⟩`((ψ:@x̅) +: (elements filter (x => !subelements.exists(_ eq x)))))

  val gψ = e(reduce:@`⟨ ⟩`((ψ:@x̅) +: (elements filter (x => !subelements.exists(_ eq x)))))

  override val program =
    h =:= (TI("let") :- (g:@f))

}

object LetReducePod {
  def apply(e: TermWithHole, reduce: Term, elements: List[Term], subelements: List[Term], ψ: Term) =
    new LetReducePod(e, reduce, elements, subelements, ψ)
}


class SynthPod(val h: Term, val subterm: Term, val synthed: Term, val ψ: Term)(implicit scope: Scope) extends Pod {

  val new_h = TypedTerm.replaceDescendant(h, (subterm, synthed))

  override val program =
    fix(h) =:= (new_h :@ ψ)

}

object SynthPod {
  def apply(h: Term, subterm: Term, synthed: Term, ψ: Term)(implicit scope: Scope) = new SynthPod(h, subterm, synthed, ψ)
}


class SynthSlashPod(val h: List[Term], val f: List[Term]) extends Pod {

  override val program =
    fix(/::(h)) =:= /::(f map (fix(_)))

}

object SynthSlashPod {
  def apply(h: List[Term], f: List[Term]) = new SynthSlashPod(h, f)
}
