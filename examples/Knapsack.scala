package examples

import semantics.{Trench, TypeTranslation, Scope, Prelude}
import semantics.Prelude._
import semantics.pattern.SimplePattern
import syntax.AstSugar._
import semantics.TypeTranslation.TypingSugar._
import synth.engine.TacticApplicationEngine
import synth.pods.IndexArithPod._1
import synth.pods.Pod
import synth.pods.ConsPod.`⟨ ⟩`
import semantics.Domains._
import synth.proof.{Prover, Assistant}


object Knapsack {

  val I = TS("I")
  val J = TS("J")
  val I0 = TS("I₀")
  val I1 = TS("I₁")
  val J0 = TS("J₀")
  val J1 = TS("J₁")
  val K0 = TS("K₀") ; val K1 = TS("K₁") ; val K2 = TS("K₂") ; val K3 = TS("K₃")

  val v = TyTV("v", I ->: R)
  val w = TyTV("w", I ->: J)

  case class APod(I: Term, J: Term) extends Pod {

    val (ψ, θ, i, j) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"))

    override val program = Prelude.program(
      ψ ↦ fix((θ ↦: i ↦: j ↦: (
        max:@ `⟨ ⟩`(
          ψ:@(i,j),
          θ:@(i-_1,j),
          (θ:@(i-_1,j-(w:@i))) + (v:@i))
        )
      ) :: ((I x J) -> R) ->: ((I x J) -> R))
    )

  }

  case class BPod(I: Term, J0: Term, J1: Term) extends Pod {

    val (ψ, i, j) = ($TV("ψ"), $TV("i"), $TV("j"))

    override val program = Prelude.program(
      ψ ↦: /::(
        ψ :: ((I x J0) -> R),
        (i ↦: j ↦: (max:@ `⟨ ⟩`(
          ψ:@(i,j),
          ((ψ :: ((I x J0) -> R)):@(i-_1,j-(w:@i))) + (v:@i))
        )) :: ((I x J1) -> R)
      )
    )

  }

  implicit val scope = new Scope(R, N, I, J)(I0 :<: I, I1 :<: I, J0 :<: J, J1 :<: J,
      K0 :<: J0, K1 :<: J0, K2 :<: J1, K3 :<: J1)

  implicit val env = TypeTranslation.subsorts(scope)

  def main(args: Array[String]): Unit = {
    ui.Config.tae(args)
    new Interpreter().executeFile(ui.Config.config.filename())
  }

  trait InvokeProver extends TacticApplicationEngine {
    def prover(pods: List[Pod]) = {
      import synth.pods._
      
      val toR = TotalOrderPod(R)
      val toI = TotalOrderPod(I)
      val toJ = TotalOrderPod(J)
      val idxI = IndexArithPod(I, toI.<)
      val idxJ = IndexArithPod(J, toJ.<)
      val partI = PartitionPod(I, toI.<, I0, I1)
      val partJ = PartitionPod(J, toJ.<, J0, J1)
      val partJ0 = PartitionPod(J0, toJ.<, K0, K1)
      val partJ1 = PartitionPod(J1, toJ.<, K2, K3)

      new Prover(List(NatPod, TuplePod, toR, toI, toJ, idxI, idxJ, partI, partJ, partJ0, partJ1) ++ pods, verbose=Prover.Verbosity.ResultsOnly)
    }
    
    override lazy val prover: Prover = prover(List())
    
    override def invokeProver(pod: Pod) { invokeProver(List(), pod.obligations.conjuncts, List(pod)) }
    def invokeProver(assumptions: List[Term], goals: List[Term], pods: List[Pod]=List()) {
      val a = new Assistant
      a.invokeProver(assumptions, goals, new SimplePattern(min :@ ?))(prover(pods))
    }
  }
  
  class Interpreter(implicit scope: Scope) extends TacticApplicationEngine with InvokeProver {
    import TacticApplicationEngine._

    override def pods(implicit s: State) = {
      case (L("A"), List(~(i), ~(j))) => APod(i, j)
      case (L("B"), List(~(i), ~(j0), ~(j1))) => BPod(i, j0, j1)
    }
  }


}
