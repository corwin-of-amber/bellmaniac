package examples

import semantics.{Trench, TypeTranslation, Scope, Prelude}
import semantics.Prelude._
import syntax.AstSugar._
import semantics.TypeTranslation.TypingSugar._
import synth.engine.TacticApplicationEngine
import synth.pods.IndexArithPod.{_1,succ}
import synth.pods.Pod
import synth.pods.ConsPod.`⟨ ⟩`
import semantics.Domains._
import synth.proof.{Prover, Assistant}


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
          (θ:@(i,j-_1)) + (d:@(i,j-_1)),
          (min:@(k ↦ ((θ:@(k,i)) + (d:@(k,i))))) |! (succ:@(i,j))
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
            (min:@(k ↦ ((ψ:@(k,i)) + (d:@(k,i))))) |! (succ:@(i,j))
          )
        )) :: (((J1 x J1) ∩ <) -> R)
      )
    )

  }

  implicit val scope = new Scope(R, N, J)(J0 :<: J, J1 :<: J,
    K0 :<: J0, K1 :<: J0, K2 :<: J1, K3 :<: J1)

  implicit val env = TypeTranslation.subsorts(scope)

  def main(args: Array[String]): Unit = {
    implicit val scope = env.scope
    new Interpreter().executeFile("/tmp/synopsis.json")
  }

  class Interpreter(implicit scope: Scope) extends TacticApplicationEngine {
    import TacticApplicationEngine._

    override def pods(implicit s: State) = {
      case (L("A"), List(~(j))) => APod(j)
      case (L("B"), List(~(j0), ~(j1))) => BPod(j0, j1)
    }

    override def invokeProver(pod: Pod) { invokeProver(List(), pod.obligations.conjuncts, List(pod)) }
    def invokeProver(assumptions: List[Term], goals: List[Term], pods: List[Pod]=List()) {
      import synth.pods._
      import syntax.Piping._

      for (goal <- goals) extrude(goal)  |-- report.console.Console.display

      val a = new Assistant

      val toR = TotalOrderPod(R)
      val toJ = TotalOrderPod(J, <)
      val idxJ = IndexArithPod(J, toJ.<)
      val partJ = PartitionPod(J, toJ.<, J0, J1)
      val partJ0 = PartitionPod(J0, toJ.<, K0, K1)
      val partJ1 = PartitionPod(J1, toJ.<, K2, K3)
      val minNR = MinPod(N, R, toR.<)
      val minJR = MinPod(J, R, toR.<)

      val p = new Prover(List(NatPod, TuplePod, toR, toJ, idxJ, partJ, partJ0, partJ1, minNR, minJR) ++ pods)

      val commits =
        for (goals <- goals map (List(_))) yield {
          //for (goals <- List(goals)) yield {
          val igoals = goals map a.intros
          import semantics.pattern.SimplePattern
          val t = new p.Transaction
          val switch = t.commonSwitch(new p.CommonSubexpressionElimination(igoals, new SimplePattern(min :@ ?)))

          t.commit(assumptions map a.simplify map t.prop, igoals map (switch(_)) map a.simplify map t.goal)
        }

      val results = commits reduce (_ ++ _)

      println("=" * 80)
      Trench.display(results, "◦")

      if (!(results.toList forall (_.root == "valid"))) System.exit(1)
    }
  }


}
