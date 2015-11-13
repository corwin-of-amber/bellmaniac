package ui

import java.io.{InputStreamReader, BufferedReader, FileReader}

import com.mongodb.{BasicDBObject, DBObject}
import com.mongodb.util.JSON

import syntax.AstSugar._
import syntax.Formula
import syntax.transform.Extrude
import syntax.Nullable._
import syntax.Piping._

import semantics.Scope
import semantics.Trench
import semantics.TypeInference
import semantics.Prelude._
import semantics.pattern.SimplePattern

import examples.Gap
import examples.Gap._
import synth.engine.TacticApplicationEngine
import synth.pods._
import synth.proof.{Assistant, Prover}

import report.data.{SerializationError, Rich, DisplayContainer}



object CLI {

  def invokeTypecheck(term: Term) = {
     val env = Gap.env
    implicit val scope = env.scope
    TypeInference.infer(term)
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
        implicit val scope = json.get("scope") andThen (_.asInstanceOf[DBObject] |> Scope.fromJson, Gap.env.scope)
        json.get("check") match {
          case check: DBObject =>
            val term = Formula.fromJson(check)
            val result = TypeInference.infer(term)._2
            cc.map(Map("term" -> result,
                       "display" -> Rich.display(extrude(result))))
          case _ => json.get("tactic") match {
            case tactic: DBObject =>
              val term = json.get("term") andThen_ (Formula.fromJson, TI("dry-run"))
                  //{ throw new SerializationError("tactic: missing 'term' key", json) })
              val command = tactic |> Formula.fromJson
              val tae = new TacticApplicationEngine()
              val result = if (term == TI("dry-run")) tae.mkState(command)
                else tae.transform(tae.initial(term), command)
              cc.map(Map("term" -> result.program,
                         "display" -> Rich.display(result.ex)))
            case _ =>
              new BasicDBObject("error", "unrecognized JSON element").append("json", json)
          }
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
          println(Console.withOut(System.err) { interpretElement(json) })
        }
        else {
          println("""{"error": "failed to parse JSON element"}""")
        }

        println()
      }
    }
  }

  def main(args: Array[String]) {
    val filename = args.headOption getOrElse "-"
    try {
      val f = new BufferedReader(
        if (filename == "-") new InputStreamReader(System.in) else new FileReader(filename))

      val session = new Session
      session repl getBlocks(f)
    }
    catch {
      case e: Throwable =>
        println(new BasicDBObject("error", "fatal").append("message", e.toString))
    }
  }
}
