package examples

import semantics.{Trench, TypeTranslation, Scope, Prelude}
import semantics.Prelude._
import semantics.pattern.SimplePattern
import syntax.AstSugar._
import semantics.TypeTranslation.TypingSugar._
import synth.engine.TacticApplicationEngine
import synth.pods.IndexArithPod.{_1,succ}
import synth.pods.Pod
import synth.pods.ConsPod.`⟨ ⟩`
import semantics.Domains._
import synth.proof.{Prover, Assistant}
import syntax.Subroutine
import syntax.Subroutine.Arity
import scala.collection.immutable.ListMap
import examples.Accordion.PodFactory
import synth.engine.CollectStats
import report.data.Rich



object Bitonic {

  val J = TS("J")
  val J0 = TS("J₀")
  val J1 = TS("J₁")
  val K0 = TS("K₀") ; val K1 = TS("K₁") ; val K2 = TS("K₂") ; val K3 = TS("K₃")

  val < = TV("<")

  val d = TyTV("d", J ->: J ->: R)

  case class APod(J: Term) extends Pod {

    val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), $TV("k"))

    override val program = Prelude.program(
      ψ ↦ fix((θ ↦: i ↦: j ↦: (
        min:@ `⟨ ⟩`(
          ψ:@(i,j),
          (θ:@(i,j-_1)) + (d:@(i,j-_1)),
          (min:@(k ↦ ((θ:@(k,i)) + (d:@(k,i))))) |! (succ:@(i,j))
        )
      )) :: (((J x J) ∩ <) -> R) ->: (((J x J) ∩ <) -> R))
    )

  }

  case class BPod(J0: Term, J1: Term) extends Pod {

    val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), $TV("k"))

    override val program = Prelude.program(
      ψ ↦ fix((θ ↦: i ↦: j ↦: (
        min:@ `⟨ ⟩`(
          ψ:@(i,j),
          (θ:@(i,j-_1)) + (d:@(i,j-_1))//,
          //(min:@(k ↦ ((θ:@(k,i)) + (d:@(k,i))))) |! (succ:@(i,j))
        )
      )) :: (((J0 x J1) ∩ <) -> R) ->: (((J0 x J1) ∩ <) -> R))
    )

  }

  case class CPod(J0: Term, J1: Term) extends Pod {

    val (ψ, i, j, k) = ($TV("ψ"), $TV("i"), $TV("j"), $TV("k"))

    override val program = Prelude.program(
      ψ ↦ /::
        (ψ :: (((J0 x J1) ∩ <) -> R),
        (i ↦: j ↦: (min:@ `⟨ ⟩`(
            ψ:@(i,j),
            (min:@((k :: J0) ↦  ((ψ:@(k,i)) + (d:@(k,i))))) |! (succ:@(i,j))
          )
        )) :: (((J1 x J1) ∩ <) -> R)
      )
    )

  }

  implicit val scope = new Scope(R, N, J)(J0 :<: J, J1 :<: J,
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
      val toJ = TotalOrderPod(J, <)
      val idxJ = IndexArithPod(J, toJ.<)
      val partJ = PartitionPod(J, toJ.<, J0, J1)
      val partJ0 = PartitionPod(J0, toJ.<, K0, K1)
      val partJ1 = PartitionPod(J1, toJ.<, K2, K3)
      val minNR = MinPod(N, R, toR.<)
      val minJR = MinPod(J, R, toR.<)

      new Prover(List(NatPod, TuplePod, toR, toJ, idxJ, partJ, partJ0, partJ1, minNR, minJR) ++ pods, verbose=Prover.Verbosity.ResultsOnly)
    }
    
    override implicit lazy val prover: Prover = prover(List())
    
    override def invokeProver(pod: Pod) { invokeProver(List(), pod.obligations.conjuncts, List(pod)) }
    def invokeProver(assumptions: List[Term], goals: List[Term], pods: List[Pod]=List()) {
      val a = new Assistant
      a.invokeProver(assumptions, goals, new SimplePattern(min :@ ?))
    }
  }
  
  class Interpreter(implicit scope: Scope) extends TacticApplicationEngine with PodFactory with InvokeProver with CollectStats {

    def fac: Map[Any,Subroutine[Term,Pod] with Arity] = ListMap(
        "A" -> Subroutine(APod), 
        "B" -> Subroutine(BPod),
        "C" -> Subroutine(CPod))
  }


}
