package examples

import syntax.AstSugar._
import semantics.{TypeTranslation, Scope, Prelude}
import semantics.Prelude._
import semantics.TypeTranslation.TypingSugar._
import semantics.Domains.SubsortAssocT
import semantics.pattern.SimplePattern
import synth.engine.TacticApplicationEngine
import synth.pods.Pod
import synth.proof.{Prover, Assistant}
import synth.pods.ConsPod.`⟨ ⟩`
import synth.pods.IndexArithPod
import synth.pods.TotalOrderPod
import report.data.Rich



object Accordion {
 
  val J = TS("J")
  val J0 = TS("J₀")
  val J1 = TS("J₁")
  val K0 = TS("K₀")
  val K1 = TS("K₁")
  val K2 = TS("K₂")
  val K3 = TS("K₃")
  val L0 = TS("L₀")
  val L1 = TS("L₁")
  val L2 = TS("L₂")
  val L3 = TS("L₃")
  val L4 = TS("L₄")
  val L5 = TS("L₅")
  
  val δ = TyTV("δ", J ->: J ->: J ->: R)
  
  import IndexArithPod._1
  val < = TV("<")
  
  case class APod(val J: Term) extends Pod {

    val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), $TV("k"))
    
    override val program = Prelude.program(
        ψ ↦ fix((θ ↦: i ↦: j ↦: (
            max:@ `⟨ ⟩`(
                ψ:@(i,j),
                max:@(k ↦ ((θ:@(j+_1,k)) + (δ:@(i,j,k))))
            )
        )) :: (((J x J) ∩ <) -> R) ->: (((J x J) ∩ <) -> R))
    )
  }

  case class BPod(val J0: Term, val J1: Term) extends Pod {

    val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), $TV("k"))
    
    override val program = Prelude.program(
        (ψ :: ((? x J1) ∩ <) ->: ?) ↦ /::(
            (i ↦: j ↦: (
              max:@ `⟨ ⟩`(
                  ψ:@(i,j),
                  max:@(k ↦ (((ψ :: (J1 x J1) ->: ?):@(j+_1,k)) + (δ:@(i,j,k))))
              ))) :: ((J0 x J1) ∩ <) ->: R,
            ψ :: ((J1 x J1) ∩ <) ->: R
        )
    )
  }

  case class CPod(val J0: Term, val J1: Term) extends Pod {

    val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), $TV("k"))
    
    override val program = Prelude.program(
        (ψ :: ((J0 x ?) ∩ <) ->: ?) ↦ /::(
            ψ :: ((J0 x J1) ∩ <) ->: R,
            (i ↦: j ↦: (
              max:@ `⟨ ⟩`(
                  ψ:@(i,j),
                  max:@((k::J1) ↦ ((ψ:@(j+_1,k)) + (δ:@(i,j,k))))
              ))) :: ((J0 x J0) ∩ <) ->: R
        )
    )
  }

  case class DPod(val J0: Term, val J1: Term, val J2: Term) extends Pod {

    val (ψ, i, j, k) = ($TV("ψ"), $TV("i"), $TV("j"), $TV("k"))
    
    override val program = Prelude.program(
        ψ ↦ /::(
            ψ :: (J1 x J2) ->: R,
            (i ↦: j ↦: (
              max:@ `⟨ ⟩`(
                  ψ:@(i,j),
                  max:@(k ↦ (((ψ::(J1 x J2) ->: ?):@(j+_1,k)) + (δ:@(i,j,k))))
              ))) :: (J0 x J1) ->: R
        )
    )
  }


  import semantics.TypedTerm.typeOf_!

  implicit val scope = new Scope(R, N, J)(J0 :<: J, J1 :<: J,
      K0 :<: J0, K1 :<: J0, K2 :<: J1, K3 :<: J1, 
      L0 :<: K0, L1 :<: K0, L2 :<: K1, L3 :<: K1, L4 :<: K2, L5 :<: K2)

  implicit val env = TypeTranslation.subsorts(scope) ++
      TypeTranslation.decl(scope, Map(δ ~> typeOf_!(δ)))



  def main(args: Array[String]): Unit = {
    ui.Config.tae(args)
    new Interpreter().executeFile(ui.Config.config.filename())
  }


  class Interpreter(implicit scope: Scope) extends TacticApplicationEngine {
    import TacticApplicationEngine._

    override def pods(implicit s: State) = {
      case (L("A"), List(~(j))) => APod(j)
      case (L("B"), List(~(j0), ~(j1))) => BPod(j0, j1)
      case (L("C"), List(~(j0), ~(j1))) => CPod(j0, j1)
      case (L("D"), List(~(j0), ~(j1), ~(j2))) => DPod(j0, j1, j2)
    }

    val A = TV("A")
    val P1 = TV("P₁")
    val P2 = TV("P₂")
    override val prototypes = Map(A → (A:@(? ∩ P1)))

    override lazy val prover: Prover = prover(List())
    
    def prover(pods: List[Pod]) = {
      import synth.pods._

      val toR = TotalOrderPod(R)
      val toJ = TotalOrderPod(J, <)
      val idxJ = IndexArithPod(J, toJ.<)
      val partJ = PartitionPod(J, toJ.<, J0, J1)
      val partJ0 = PartitionPod(J0, toJ.<, K0, K1)
      val partJ1 = PartitionPod(J1, toJ.<, K2, K3)
      val partK0 = PartitionPod(K0, toJ.<, L0, L1)
      val partK1 = PartitionPod(K1, toJ.<, L2, L3)
      val partK2 = PartitionPod(K2, toJ.<, L4, L5)
      val maxJR = MaxPod(J, R, toR.<)
      val maxNR = MaxPod(N, R, toR.<)

      new Prover(List(NatPod, TuplePod, toR, toJ, idxJ, partJ, partJ0, partJ1, partK0, partK1, partK2, maxJR, maxNR) ++ pods, Prover.Verbosity.ResultsOnly)
    }
    
    override def invokeProver(pod: Pod) { invokeProver(List(), pod.obligations.conjuncts, List(pod)) }
    
    def invokeProver(assumptions: List[Term], goals: List[Term], pods: List[Pod]=List()) {
      (new Assistant).invokeProver(assumptions, goals, new SimplePattern(min :@ ?))(prover(pods))
    }
  }  
  
}
