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
import java.io.StringWriter
import java.io.PrintWriter



object CLI {

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

    import collection.JavaConversions._
    
    def interpretElement(json: DBObject): DBObject = {
      try {
        implicit val scope = examples.Paren.env.scope //json.get("scope") andThen_ (Scope.fromJson, examples.Paren.env.scope)
        println(json.get("routines"))
        json.get("check") match {
          case check: DBObject =>
            val term = Formula.fromJson(check)
            val result = TypeInference.infer(term)._2
            cc.map(Map("term" -> result,
                       "display" -> Rich.display(extrude(result))))
          case _ => json.get("tactic") match {
            case tactic: DBObject =>
              val tae = mkTae
              json.get("routines") andThen_ ( (x:DBObject) => x.toMap().foreach { 
                case (name:String, defn:DBObject) => defn.get("body") andThen_ ((x:DBObject) => (Formula.fromJson(x).toPretty |> println), ())
              }, () ) 
              val result =
                if (ui.Config.config.dryRun()) {
                  tae.mkState(tactic |> Formula.fromJson)
                }
                else {
                  json.get("term") andThen_ ((tae.transform(_:DBObject, json)),
                      { throw new SerializationError("tactic: missing 'term' key", json) })
                }
              cc.map(Map("term" -> result.program,
                         "display" -> Rich.display(result.ex)))
            case _ =>
              new BasicDBObject("error", "unrecognized JSON element")append("json", json)
          }
        }
      }
      catch {
        case e: Throwable =>
          cc.map(Map("error" -> "exception", "message" -> e.toString, "stack" -> stack(e)))
      }
    }

    def repl(blocks: Stream[String]): Unit = {
      for (blk <- blocks) {
        val json = JSON.parse(blk).asInstanceOf[DBObject]
        if (json != null) {
          //val (result, outs) = 
            if (ui.Config.config.debug())
              //(Console.withOut(System.err) { interpretElement(json) }, "")
              interpretElement(json)
            else {
              val (result, outs) = report.console.Console.andOut { interpretElement(json) }
              println(result)
            }
        }
        else {
          println(cc.map(Map("error" -> "failed to parse JSON element")))
        }

        println()
      }
    }
    
    def mkTae = new examples.Paren.BreakDown.Interpreter
  }

  def stack(e: Throwable) = {
    val sw = new StringWriter
    e.printStackTrace(new PrintWriter(sw))
    sw.toString
  }
  
  def main(args: Array[String]) {
    ui.Config(new ui.Config.CLIConfig(args toList))
    val filename = ui.Config.config.filename()
    val session = new Session
    try {
      val f = new BufferedReader(
        if (filename == "-") new InputStreamReader(System.in) else new FileReader(filename))

      session repl getBlocks(f)
    }
    catch {
      case e: Throwable =>
        println(session.cc.map(Map("error" -> "fatal", "message" -> e.toString, "stack" -> stack(e))))
    }
  }
}
