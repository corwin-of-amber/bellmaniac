package ui

import java.io.{InputStreamReader, BufferedReader, FileReader}

import report.data.{Rich, DisplayContainer}
import semantics.{TypeInference, Prelude, TypedTerm, Trench}

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

  def invokeTypecheck(term: Term) = {
    implicit val env = Gap.env
    implicit val scope = env.scope
    TypeInference.infer(term)
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

  def getLines(f: BufferedReader): Stream[String] = {
    val line = f.readLine()
    if (line == null) Stream.empty else line #:: getLines(f)
  }

  def splitBlocks(s: Stream[String]): Stream[String] = s match {
    case Stream.Empty => Stream.empty
    case _ => s.span(_ != "") match {
      case (first, rest) =>
        if (first.isEmpty) splitBlocks(rest)
        else first.mkString("") #:: splitBlocks(rest)
    }
  }

  def getBlocks(f: BufferedReader) = splitBlocks(getLines(f))

  def main(args: Array[String]) {
    import syntax.Piping._

    val filename = if (args.length > 0) args(0) else "-"
    val f = new BufferedReader(
      if (filename == "-") new InputStreamReader(System.in) else new FileReader(filename))


    implicit val cc = new DisplayContainer
    val extrude = new Extrude(Set(I("/"), cons.root))

    for (line <- splitBlocks(getBlocks(f))) {
      val json = JSON.parse(line).asInstanceOf[DBObject]
      if (json != null && json.get("$") == "Tree") {
        val term = Formula.fromJson(json)
        //println(s"Term: ${term.toPretty}")

        //val ex = extrude(term) |-- display

        println(Rich.display( extrude(invokeTypecheck(term)._2) ).asJson(cc))
        //invokeProver(List(term))
      }
    }
  }
}
