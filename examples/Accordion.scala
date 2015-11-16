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



object Accordion {
 
  val J = TS("J")
  val J0 = TS("J₀")
  val J1 = TS("J₁")
  
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
                  max:@(k ↦ ((ψ:@(j+_1,k)) + (δ:@(i,j,k))))
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


  import semantics.TypedTerm.typeOf_!

  implicit val scope = new Scope(R, N, J)(J0 :<: J, J1 :<: J)

  implicit val env = TypeTranslation.subsorts(scope) ++
      TypeTranslation.decl(scope, Map(δ ~> typeOf_!(δ)))



  def main(args: Array[String]): Unit = {
    val filename = args.lift(0) getOrElse "/tmp/synopsis.json"

    new Interpreter().executeFile(filename)
  }


  class Interpreter(implicit scope: Scope) extends TacticApplicationEngine {
    import TacticApplicationEngine._

    override def pods(implicit s: State) = {
      case (L("A"), List(~(j))) => APod(j)
      case (L("B"), List(~(j0), ~(j1))) => BPod(j0, j1)
      case (L("C"), List(~(j0), ~(j1))) => CPod(j0, j1)
    }

    val A = TV("A")
    val P1 = TV("P₁")
    val P2 = TV("P₂")
    override val prototypes = Map(A → (A:@(? ∩ P1)))

    override lazy val prover = {
      import synth.pods._

      val toR = TotalOrderPod(R)
      val toJ = TotalOrderPod(J, <)
      val idxJ = IndexArithPod(J, toJ.<)
      val partJ = PartitionPod(J, toJ.<, J0, J1)
      val maxJR = MaxPod(J, R, toR.<)
      val maxNR = MaxPod(N, R, toR.<)

      new Prover(List(NatPod, TuplePod, toR, toJ, idxJ, partJ, maxJR, maxNR), Prover.Verbosity.ResultsOnly)
    }
    
    override def invokeProver(pod: Pod) { invokeProver(List(), pod.obligations.conjuncts, List(pod)) }
    def invokeProver(assumptions: List[Term], goals: List[Term], pods: List[Pod]=List()) {
      import synth.pods._
      import syntax.Piping._

      for (goal <- goals) extrude(goal) |> report.console.Console.display

      println("· " * 25)

      val a = new Assistant

      val toR = TotalOrderPod(R)
      val toJ = TotalOrderPod(J, <)
      val idxJ = IndexArithPod(J, toJ.<)
      val partJ = PartitionPod(J, toJ.<, J0, J1)
      val maxJR = MaxPod(J, R, toR.<)
      val maxNR = MaxPod(N, R, toR.<)

      val p = new Prover(List(NatPod, TuplePod, toR, toJ, idxJ, partJ, maxJR, maxNR) ++ pods, Prover.Verbosity.ResultsOnly)

      val commits =
        for (goals <- goals map (List(_))) yield {
          //for (goals <- List(goals)) yield {
          val igoals = goals map a.intros
          val t = new p.Transaction
          val switch = t.commonSwitch(new p.CommonSubexpressionElimination(igoals, new SimplePattern(min :@ ?)))

          t.commit(assumptions map a.simplify map t.prop, igoals map (switch(_)) map a.simplify map t.goal)
        }

      val results = commits reduce (_ ++ _)

      if (!(results.toList forall (_.root == "valid"))) System.exit(1)

      println("=" * 80)  // QED!
    }
  }  
  
}
