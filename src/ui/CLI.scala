package ui

import semantics.{Prelude, TypedTerm, Trench}

import scala.io.Source
import com.mongodb.DBObject
import com.mongodb.util.JSON

import semantics.Prelude._
import syntax.Formula
import syntax.AstSugar._
import syntax.transform.Extrude
import report.console.Console.display

import examples.Gap
import examples.Gap._
import synth.pods._
import synth.proof.{Assistant, Prover}
import semantics.pattern.{SimpleTypedPattern, MacroMap, SimplePattern}



object CLI {

  class IndexArithPod extends Pod {
    private val X = V("x")
    private val L = V("l")

    val MINUSPAT = SimplePattern((T(X) :- $TV("?")) - (T(L) :- $TV("?")))
    override val macros = MacroMap(I("-") -> { x => MINUSPAT(x) map (_(X)) })
  }

  def invokeProver(goals: List[Term]): Unit = {

    implicit val env = Gap.env
    implicit val scope = env.scope

    val a = new Assistant

    val assumptions = List()

    val toR = TotalOrderPod(R)
    val nilNR = NilPod(N, R)
    val nilJR = NilPod(J, R)
    val consR = ConsPod(R)
    val minJR = MinPod(J, R, toR.<) //, opaque=true)
    val minNR = MinPod(N, R, toR.<) //, opaque=true)

    val adhoc = new IndexArithPod

    val p = new Prover(List(/*NatPod,*/ toR, minJR, minNR, consR, nilNR, adhoc))

    val t = new p.Transaction
    val switch = t.commonSwitch(new p.CommonSubexpressionElimination(goals, new SimplePattern(min :@ ?)))

    val results =
      t.commit(assumptions map a.simplify map t.prop, goals map (switch(_)) map a.simplify map t.goal)

    println("=" * 80)
    Trench.display(results, "◦")
  }

  def main(args: Array[String]) {
    val f = Source.fromFile("/tmp/bell.json")
    for (line <- f.getLines) {
      val json = JSON.parse(line).asInstanceOf[DBObject]
      if (json != null && json.get("$") == "Tree") {
        val term = Formula.fromJson(json)
        println(s"Term: ${term.toPretty}")

        val extrude = new Extrude(Set(I("/"), cons.root))
        display(extrude(term))
        invokeProver(List(term))
      }
    }
  }
}
