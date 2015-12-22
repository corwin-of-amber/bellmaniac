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
import synth.engine.TacticApplicationEngine
import synth.pods._
import synth.proof.{Assistant, Prover}
import report.data.{SerializationError, Rich, DisplayContainer}
import java.io.StringWriter
import java.io.PrintWriter
import semantics.TypeTranslation.Environment
import synth.engine.CollectStats
import report.data.SerializationError
import semantics.SubstituteWithinTypes
import synth.engine.PodFactory
import scala.collection.immutable.ListMap
import report.data.SerializationContainer
import com.mongodb.BasicDBList
import semantics.TypeTranslation
import report.data.SerializationError



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
        implicit val scope = json.get("scope") andThen_ (Scope.fromJson, { throw new SerializationError("scope not found", json) }) // examples.Paren.env.scope)
        implicit val env = TypeTranslation.subsorts(scope) //examples.Paren.env
        val routines = json.get("routines").opt_[DBObject] getOrElse null
          
        json.get("check") match {
          case check: DBObject =>
            val term = Formula.fromJson(check)
            val result = TypeInference.infer(term)._2
            cc.map(Map("term" -> result,
                       "display" -> Rich.display(extrude(result))))
          case _ => json.get("tactic") match {
            case tactic: DBObject =>
              val tae = mkTae(routines)
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
          if (ui.Config.config.debugOnly()) {
            interpretElement(json).get("stack") andThen (System.err.println, ())
          }
          else {
            val (result, outs) =
              if (ui.Config.config.debug())
                (Console.withOut(System.err) { interpretElement(json) }, "")
              else
                report.console.Console.andOut { interpretElement(json) }
            println(result)
          }
        }
        else {
          println(cc.map(Map("error" -> "failed to parse JSON element")))
        }

        println()
      }
    }
    
    def mkTae(routinesJson: DBObject)(implicit scope: Scope, env: Environment) = 
      routinesJson andThen (new Session.Interpreter(_), new Session.Interpreter(Map.empty[Any,Session.DefnSubroutine]))
  }
  
  object Session {
    
    import collection.JavaConversions._
    import syntax.Subroutine
    import syntax.Subroutine.Arity

    class DefnSubroutine(val params: List[Term], val body: Term) extends Subroutine[Term,Pod] with Arity {
      val arity = params.length
      
      def apply(l: Term*) = new Pod {
        override val program = new SubstituteWithinTypes(params zip l)(body)
      }
    }
    
    object DefnSubroutine {
      def fromJson(json: DBObject)(implicit cc: SerializationContainer) = {
        val params = json.get("params") andThen_ ((l: BasicDBList) => l map (x => x andThen_ (Formula.fromJson, { throw new SerializationError("malformed routine parameter", x); })) toList, List())
        val body = json.get("body") andThen_ (Formula.fromJson, { throw new SerializationError("malformed routine body", json); })
        new DefnSubroutine(params, body)
      }
    }
    
    type InvokeProver = examples.Paren.BreakDown.InvokeProver
    
    class Interpreter(routines: Map[Any, DefnSubroutine])(implicit scope: Scope, env: Environment) extends TacticApplicationEngine with PodFactory with InvokeProver with CollectStats {
      import TacticApplicationEngine._
      
      def this(routinesJson: DBObject)(implicit scope: Scope, env: Environment, cc: SerializationContainer) =
        this(
          routinesJson.toMap().toMap map {  // second toMap is to convert to immutable Map
            case (name: String, defn: DBObject) => (name:Any, DefnSubroutine.fromJson(defn))
            case x: AnyRef => throw new SerializationError(s"malformed routine", x);
            case x => throw new SerializationError(s"malformed routine ${x}", routinesJson);
          })
      
      def fac: Map[Any,Subroutine[Term,Pod] with Arity] = routines
    }

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
