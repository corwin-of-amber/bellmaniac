package examples

import semantics.{TypeTranslation, Scope, Prelude}
import semantics.Prelude._
import syntax.AstSugar._
import synth.pods.ConsPod._
import synth.pods.Pod



object Eggs {

  val I = TS("I")
  val J = TS("J")
  val I0 = TS("I₀")
  val I1 = TS("I₁")
  val J0 = TS("J₀")
  val J1 = TS("J₁")

  val l = TV("l")
  val < = TV("<")

  import synth.pods.IndexArithPod.{_0,_1}

  case class APod(I: Term, J: Term) extends Pod {

    val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), $TV("k"))

    override val program = Prelude.program(
      (
        ψ ↦ fix(θ↦:i↦:j↦:(min:@`⟨ ⟩`(
          ψ:@(i,j),
          min:@(k ↦ ((max:@`⟨ ⟩`(θ:@(k-_1,j-_1), θ:@(i-k,j))) |! ((< :@(_0,k)) & ~(< :@(i,k)))) )
        )))
      ) :: ((I x J) -> R) ->: ((I x J) -> R)
    )

  }

  implicit val env = {
    import semantics.Domains._
    val scope = new Scope

    List(R, N, I, J) foreach scope.sorts.declare
    List(I0 :<: I, I1 :<: I, J0 :<: J, J1 :<: J) foreach scope.sorts.declare

    scope.sorts.cork()

    TypeTranslation.subsorts(scope)
  }

  def main(args: Array[String]): Unit = {
    implicit val scope = env.scope
    //rewriteA
    new Interpreter().executeFile("/tmp/synopsis.json")
  }

  import Paren.BreakDown.Interpreter

  class Interpreter(implicit scope: Scope) extends Paren.BreakDown.Interpreter {
    import Interpreter._
    /* This part is Eggs-specific */
    override def pods(implicit s: State) = {
      case (L("A"), List(~(j), ~(k))) => APod(j, k)
      //case (L("B"), List(~(j), ~(k0), ~(k1))) => BPod(j, k0, k1)
    }
  }

}
