package ui

import java.io.{InputStreamReader, BufferedReader, FileReader}

import com.mongodb.{BasicDBObject, DBObject}
import com.mongodb.util.JSON

import report.data.{Rich, DisplayContainer}
import semantics._
import syntax.Nullable._
import syntax.Piping._

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

  def invokeTypecheck(term: Term) = {
     val env = Gap.env
    implicit val scope = env.scope
    TypeInference.infer(term)
  }

  def invokeProver(goals: List[Term]): Unit = {

    implicit val env = Gap.env
    implicit val scope = env.scope

    val a = new Assistant

    val assumptions = List()

    val toR = TotalOrderPod(R)
    val toJ = TotalOrderPod(J)
    val idxJ = IndexArithPod(J, toJ.<)
    val partJ = PartitionPod(J, toJ.<, J0, J1)
    val nilNR = NilPod(N, R)
    val consR = ConsPod(R)
    val minJR = MinPod(J, R, toR.<) //, opaque=true)
    val minNR = MinPod(N, R, toR.<) //, opaque=true)

    val p = new Prover(List(NatPod, TuplePod, toJ, idxJ, partJ, toR, minJR, minNR, consR, nilNR))

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
        def splitRest = splitBlocks(rest dropWhile (_ == ""))
        if (first.isEmpty) splitRest
        else first.mkString #:: splitRest
    }
  }

  def getBlocks(f: BufferedReader) = splitBlocks(getLines(f))

  class Session {

    implicit val cc = new DisplayContainer
    val extrude = new Extrude(Set(I("/"), cons.root))

    def interpretElement(json: DBObject): DBObject = {
      try {
        json.get("check") match {
          case check: DBObject =>
            val term = Formula.fromJson(check)
            implicit val scope = json.get("scope") andThen(_.asInstanceOf[DBObject] |> Scope.fromJson, Gap.env.scope)
            Rich.display(extrude(TypeInference.infer(term)._2)).asJson(cc)
          case _ =>
            new BasicDBObject("error", "unrecognized JSON element").append("json", json)
        }
      }
      catch {
        case e: Throwable =>
          new BasicDBObject("error", "exception").append("message", e.toString)
      }
    }

    def repl(blocks: Stream[String]): Unit = {
      for (blk <- blocks) {
        val json = JSON.parse(blk).asInstanceOf[DBObject]
        if (json != null) {
          println(interpretElement(json))
        }
        else {
          println("""{"error": "failed to parse JSON element"}""")
        }

        println("\n")

        /*&& json.get("$") == "Tree") {

          //println(s"Term: ${term.toPretty}")

          //val ex = extrude(term) |-- display

          //invokeProver(List(term))
        }*/
      }
    }
  }

  def main(args: Array[String]) {
    val filename = if (args.length > 0) args(0) else "-"
    val f = new BufferedReader(
      if (filename == "-") new InputStreamReader(System.in) else new FileReader(filename))

    val session = new Session
    session repl getBlocks(f)
  }
}
