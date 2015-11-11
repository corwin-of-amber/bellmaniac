package synth.pods

import syntax.AstSugar._
import semantics._
import semantics.Prelude._
import semantics.TypeTranslation.Declaration
import semantics.TypedScheme.TermWithHole
import synth.pods.Pod.TacticalError


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


class StratifySlash2Pod(val e: TermWithHole, val slashes: Term, val subelements: List[Term], val ψ: Term) extends Pod {

  val elements = slashes.split(I("/"))

  val x̅ = e.x̅

  val ψx̅ = if (x̅.isEmpty) $TV ↦ ψ else ψ :@ x̅.tail

  val h = e(slashes)
  val f = e(/::(subelements))
  val g = ψ ↦ e(/::(ψx̅ +: (elements filter (x => !subelements.exists(_ eq x)))))

  val gψ = e(/::(ψx̅ +: (elements filter (x => !subelements.exists(_ eq x)))))

  override val program =
    fix(h) =:= (TI("let") :- ((ψ ↦ fix (gψ)):@fix(f)))

  val θ = $TV("θ")
  val ζ = $TV("ζ")

  override val obligations = &&(
    (g:@(f:@θ, θ)) =:= (h:@θ),
    (f:@(g:@(ζ,θ))) =:= (f:@ζ)
  )
}

object StratifySlash2Pod {
  def apply(e: TermWithHole, slashes: Term, subelements: List[Term], ψ: Term)(implicit scope: Scope) = new StratifySlash2Pod(e, slashes, subelements, ψ)
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


class LetReducePod(val e: TermWithHole, val reduce: Term, val elements: List[Term],
                   val subelements: List[Term], val ψ: Term) extends Pod {

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


class SynthPod(val h: Term, val subterm: Term, val synthed: Term, val impl: Term, val ψ: Term,
               val area: List[Term])(implicit scope: Scope) extends Pod {

  val new_h = TypedTerm.replaceDescendant(h, (subterm, synthed))

  override val program =
    fix(h) =:= (new_h :@ ψ)

  /* The obligations are rather involved */

  import semantics.TypeTranslation.TypingSugar._
  import semantics.TypePrimitives._
  import TypedTerm.typeOf_!

  val indexDomain = shape(area.head)
  val Q = $TyTV("Q", rawtype(scope, area.head ->: B))

  val areaChecks = {
    val vars = qvars(args(typeOf_!(Q)))
    ∀(vars)(Q(vars) <->
      ||(area map (a => &&(TypeTranslation.checks(scope, a -> B, vars)))))
  }

  def equivQuadrant(lhs: Term, rhs: Term) = {
    val y = (indexDomain ∩ Q) -> ?
    &&(
      (lhs :: (? -> y)) =:= (lhs :: (y -> y)),
      (lhs :: (? -> y)) =:= (rhs :: (y -> y))
    )
  }

  def stableQuadrant(lhs: Term, rhs: Term) = {
    val θ = $TV("θ")
    val y = (indexDomain ∩ Q) -> ?
    ((lhs:@(lhs:@θ)) :: y) =:= (rhs :: y)
  }

  override val obligations =
  {
    impl.nodes find (_ =~ ("fix", 1)) match {
      case Some(x) =>
        val u = TypedLambdaCalculus.pullOut(impl, x.subtrees(0)).get
        equivQuadrant(h, u :@ ψ)
      case _ =>
        if (impl.isLeaf) TRUE  /* placeholder; should be deprecated */
        else {
          val u = if (impl.root == Prelude.program.root) impl.subtrees(0) else impl
          stableQuadrant(h, u :@ ψ)
        }
    }
  }

  override val decl = new Declaration(Q) where areaChecks
}

object SynthPod {
  def apply(h: Term, subterm: Term, synthed: Term, impl: Term, ψ: Term,
               area: List[Term])(implicit scope: Scope) = new SynthPod(h, subterm, synthed, impl, ψ, area)
}


class LetSynthPod(val h: Term, val synthed: Term, val impl: Term, val ψ: Term)(implicit scope: Scope) extends Pod {

  import TypedTerm.typeOf_!

  val new_h = TypedTerm(synthed, typeOf_!(ψ) -> typeOf_!(h))

  override val program =
    h =:= (new_h :@ ψ)

  override val obligations = {
    val body = impl match {
      case T(Prelude.program.root, List(body)) => body
      case _ => impl
    }
    h =:= ((body :: (? -> typeOf_!(h))) :@ ψ)
  }
}

object LetSynthPod {
  def apply(h: Term, synthed: Term, impl: Term, ψ: Term)(implicit scope: Scope) = new LetSynthPod(h, synthed, impl, ψ)
}


class SynthSlashPod(val h: List[Term], val f: List[Term]) extends Pod {

  override val program =
    fix(/::(h)) =:= /::(f map (fix(_)))

  override val obligations = TRUE  // for now
}

object SynthSlashPod {
  def apply(h: List[Term], f: List[Term]) = new SynthSlashPod(h, f)
}
