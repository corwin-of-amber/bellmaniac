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
import java.io.File
import java.io.PrintStream
import report.AppendLog
import report.FileLog
import synth.engine.OptimizationPass
import org.rogach.scallop.ScallopOption
import ui.Config.overridden



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
  def getBlocks(f: File): Stream[String] = getBlocks(new BufferedReader(new FileReader(f)))

  class Session {

    implicit val cc = new DisplayContainer
    val extrude = new Extrude(Set(I("/"), cons.root))

    var currentState: TacticApplicationEngine.State = null
    
    import collection.JavaConversions._
    import TacticApplicationEngine.State
        
    def interpretElement(json: DBObject, progress: DBObject => Unit): DBObject = {
      try {
        implicit lazy val scope = json.get("scope") andThen_ (Scope.fromJson, { throw new SerializationError("scope not found", json) }) // examples.Paren.env.scope)
        implicit lazy val env = TypeTranslation.subsorts(scope) //examples.Paren.env
        val routines = json.get("routines").opt_[DBObject] getOrElse null

        json.get("check") match {
          case check: DBObject =>
            val term = Formula.fromJson(check)
            val result = TypeInference.infer(term)._2
            json.get("emit") match {
              case emit: DBObject =>
                val tae = mkTae(routines)
                val s = tae.mkState(result)
                tae.display(tae.emit(s, emit.get("name").toString, emit.get("style").toString))
                currentState = s
              case _ =>
            }
            serialize(result)
          case _ => json.get("tactic") match {
            case tactic: DBObject =>
              val tae = mkTae(routines)
              val result =
                if (ui.Config.config.dryRun()) {
                  tae.mkState(tactic |> Formula.fromJson)
                }
                else {
                  json.get("term") andThen_ (tae.transform(_:DBObject, json, progress=(s: State) => progress(serialize(s))),
                      currentState andThen (tae.transform(_, json, progress=(s: State) => progress(serialize(s))),
                      { throw new SerializationError("tactic: missing 'term' key", json) }))
                }
              currentState = result
              serialize(result)
            case _ => json.get("program") match {    /* this is a compiled program; display it */
              case prog: String =>
                val term = json.get("term") andThen_ (Formula.fromJson, { throw new SerializationError("program: missing 'term' key", json) })
                val tae = mkTae(routines)
                println(s"scope: ${scope.sorts}")
                println(s"tag:   ${json.get("tag")}")
                tae.display(tae.mkState(term))
                cc.map()
              case _ => json.get("term") match {    /* this is an uncompiled program; emit it */
                case prog: DBObject =>
                  val term = prog |> Formula.fromJson
                  json.get("emit") match {
                    case emit: DBObject =>
                      val tae = mkTae(routines)
                      val result = tae.emit(tae.mkState(term), emit.get("name").toString, emit.get("style").toString)
                      tae.display(result)
                      serialize(result)
                    case _ =>
                      cc.map()
                  }
                case _ => json.get("section") match {
                  case section: String =>
                    json.get("options") match {
                      case options: BasicDBObject =>
                        // TODO tmpdir is hard-coded; other options?
                        val tmpdirVal = options.getString("tmpdir").opt map (new File(_))
                        println(s"section '$section'  [tmpdir=${tmpdirVal map (x=>s"'$x'")}]")
                        ui.Config.Sources.jsonStream = Some(new ui.Config.JsonStreamConfig {
                          val tmpdir = overridden("tmpdir", tmpdirVal)
                        })
                      case _ =>
                        println(s"section '$section'")
                    }
                    cc.map()
                  case _ =>
                    new BasicDBObject("error", "unrecognized JSON element") append ("json", json)
                }
              }
            }
          }
        }
      }
      catch {
        case e: Throwable =>
          cc.map(Map("error" -> "exception", "message" -> e.toString, "stack" -> stack(e)))
      }
    }
    
    def serialize(state: State) =
      cc.map(Map("term" -> state.program,
                 "display" -> Rich.display(extrude(OptimizationPass.foldAllCalls(state.program)))))

    def serialize(program: Term) =
      cc.map(Map("term" -> program,
                 "display" -> Rich.display(extrude(program))))
    
    def reportProgress(json: DBObject)(implicit out: PrintStream) {
      if (!ui.Config.config.debugOnly()) {
        out.println(cc.map("progress" -> json))
        out.println()
      }
    }
    
    def repl(blocks: Stream[String]): Unit = {
      implicit val out = System.out
      for (blk <- blocks) {
        val json = JSON.parse(blk).asInstanceOf[DBObject]
        if (json != null) {
          if (ui.Config.config.debugOnly()) {
            interpretElement(json, reportProgress).get("stack") andThen (System.err.println, ())
          }
          else {
            val (result, outs) =
              if (ui.Config.config.debug())
                (Console.withOut(System.err) { interpretElement(json, reportProgress) }, "")
              else
                report.console.Console.andOut { interpretElement(json, reportProgress) }
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
    
    type InvokeProver = examples.Accordion.InvokeProver   // TODO generalize prover selection
    
    class Interpreter(routines: Map[Any, DefnSubroutine])(implicit scope: Scope, env: Environment) extends TacticApplicationEngine with PodFactory with InvokeProver with CollectStats {
      import TacticApplicationEngine._
      
      def this(routinesJson: DBObject)(implicit scope: Scope, env: Environment, cc: SerializationContainer) =
        this(
          routinesJson.toMap().toMap map {  // second toMap is to convert to immutable Map
            case (name: String, defn: DBObject) => (name:Any, DefnSubroutine.fromJson(defn))
            case x: AnyRef => throw new SerializationError(s"malformed routine", x);
            case x => throw new SerializationError(s"malformed routine ${x}", routinesJson);
          })
      
      override lazy val outf = Session.outf;  
      override lazy val logf = Session.logf;
          
      def fac: Map[Any,Subroutine[Term,Pod] with Arity] = routines
    }

    /* TODO seems like this should be part of Session class? */
    lazy val outf: AppendLog = new FileLog(new File("/tmp/prog.json"), new DisplayContainer)
    lazy val logf: AppendLog = new FileLog(new File("/tmp/bell.json"), new DisplayContainer)
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
