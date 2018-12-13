package examples

import semantics.{TypeTranslation, Scope, Prelude}
import semantics.Prelude._
import syntax.AstSugar._
import synth.engine.TacticApplicationEngine
import synth.pods.Pod
import synth.pods.ConsPod._
import semantics.Domains.SubsortAssocT



object Floyd2D {

  val J = TS("J")
  val J0 = TS("J₀")
  val J1 = TS("J₁")

  import synth.pods.IndexArithPod._1

  case class APod(J: Term) extends Pod {

    val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), $TV("k"))

    override val program = Prelude.program(
      (
        ψ ↦ fix(θ↦:i↦:j↦:k↦:(min:@`⟨ ⟩`(
          ψ:@(i,j,k),
          (θ:@(i,j,k-_1)) ⨁ ((θ:@(i,k,k-_1)) ⨀ (θ:@(k,j,k-_1)))
        )))
      ) :: ((J x J x J) -> R) ->: ((J x J x J) -> R)
    )

  }

  implicit val scope = new Scope(R, N, J)(J0 :<: J, J1 :<: J)

  implicit val env = TypeTranslation.subsorts(scope)


  def main(args: Array[String]): Unit = {
    implicit val scope = env.scope

    new Interpreter().executeFile("/tmp/synopsis.json")
  }

  class Interpreter(implicit scope: Scope) extends TacticApplicationEngine {
    import TacticApplicationEngine._

    override def pods(implicit s: State) = {
      case (L("A"), List(~(j))) => APod(j)
      //case (L("B"), List(~(j), ~(k0), ~(k1))) => BPod(j, k0, k1)
    }
  }

}
