package synth.engine

import java.io.{FileReader, BufferedReader}

import com.mongodb.util.JSON
import com.mongodb.{BasicDBList, DBObject}

import examples.Gap.BreakDown.Instantiated
import report.FileLog
import report.console.Console._
import report.console.Console.display
import report.data.{Rich, SerializationContainer, DisplayContainer}
import semantics.Prelude._
import semantics.TypedScheme.TermWithHole
import semantics.pattern.SimplePattern
import semantics.transform.Explicate
import semantics.{TypedLambdaCalculus, TranslationError, LambdaCalculus, Scope}
import semantics.TypeTranslation.Environment
import syntax.AstSugar._
import syntax.Piping._
import syntax.{Tree, Formula}
import syntax.transform.{ExtrudedTerms, Extrude}
import synth.pods.ConsPod._
import synth.pods._
import synth.tactics.Rewrite._
import ui.CLI



class TacticApplicationEngine(implicit scope: Scope, env: Environment) {
  import TacticApplicationEngine._

  val extrude = Extrude(Set(I("/"), cons.root))

  val outf = new FileLog(new java.io.File("/tmp/prog.json"), new DisplayContainer)
  val logf = new FileLog(new java.io.File("/tmp/bell.json"), new DisplayContainer)

  /*
   * Eval part
   */

  def evalTerm(expr: Term)(implicit s: State): Term = {
    if (expr.isLeaf) {
      val label = expr.root.literal
      try s.ex :/ label catch { case x: Exception => try s.program :/ label subtrees 1 catch { case x: Exception => expr } }
    } else LambdaCalculus.isApp(expr) match {
      case Some((L("fixer"), List(~(t)))) => fixer(s.program, t)
      case Some((L("fixee"), List(~(t)))) => fixee(s.program, t)
      case Some((L("ctx"), List(~(t), T(symbol, Nil)))) => ctx(s.program, t)(symbol.literal)
      case Some((L("slasher"), List(~(t)))) => slasher(s.program, t)
      case Some((L("find"), List(pat))) => (new SimplePattern(pat) findOne_! s.program).subterm
      case Some((L("find"), List(~(t), pat))) => (new SimplePattern(pat) findOne_! t).subterm
      case Some((L("find"), List(pat, #:(n)))) => (new SimplePattern(pat) find s.program get (n-1)).subterm
      case Some((L("find"), List(~(t), pat, #:(n)))) => (new SimplePattern(pat) find t get (n-1)).subterm
      // TODO error checking: index out of range

      case Some(x) => (pods andThen (_.program |> instapod)) applyOrElse (x,
          { case _ => expr }: PartialFunction[(Term, List[Term]), Term] )

      case _ => expr
    }
  }

  def evalList(expr: Term)(implicit s: State): List[Term] = ConsPod.`⟨ ⟩?`(expr) match {
    case Some(l) => l map evalTerm
    case _ => expr match {
      case T(@:.root, List(~~(l1), ~~(l2))) => for (a <- l1; b <- l2) yield a x b
      case _ =>
        val eexpr = evalTerm(expr)
        ConsPod.`⟨ ⟩?`(eexpr) match {
          case Some(l) => l
          case _ => List(eexpr)  // singleton
        }
    }
  }

  def resolvePatterns(command: Term)(implicit s: State) = {
    command.nodes map (c => (c, LambdaCalculus.isAppOf(c, TI("findAll")))) find (_._2.isDefined) match {
      case Some((node, Some(List(pat)))) => SimplePattern(pat) find s.program map { mo =>
        command.replaceDescendant(node, mo.subterm)
      }
      case Some((node, Some(List(~(subterm), pat)))) => SimplePattern(pat) find subterm map { mo =>
        command.replaceDescendant(node, mo.subterm)
      }
      case _ => Stream(command)
    }
  }

  def pods(implicit s: State): PartialFunction[(Term, List[Term]), Pod] = PartialFunction.empty

  def encaps(t: Term) = LambdaCalculus.isApp(t) match {
    case Some((f,args)) => $TV(s"${f toPretty}[${args map (_.toPretty) mkString ","}]")
    case _ => $TV(t.toPretty)
  }

  object ~ { def unapply(expr: Term)(implicit s: State) = Some(evalTerm(expr)) }
  object ~~ { def unapply(expr: Term)(implicit s: State) = Some(evalList(expr)) }
  object #: { def unapply(expr: Term) = expr match {
    case L(n : Int) => Some(n)  case _ => None
  } }
  object ++ { def unapply(expr: Term) = expr match {
    case L("min") | L("max") => Some(expr)  case _ => None
  } }

  val * = TI("*")

  def transform(s: State, command: Term) = {
    implicit val st = s
    var cert = false
    def pods(command: Term): Iterable[Pod] =
      ConsPod.`⟨ ⟩?`(command) match {
        case Some(commands) => commands flatMap pods
        case _ => LambdaCalculus.isApp(command) match {
          case Some((L("Slice"), List(~(f), ~~(domains)))) =>
            List(SlicePod(f, domains))
          case Some((L("StratifySlash"), List(~(h), ~(quadrant), ~(ψ)))) =>
            List(StratifySlashPod(h, quadrant, ψ))
          case Some((L("StratifyReduce"), List(reduce, ~(h), ~~(subelements), ~(ψ)))) =>
            SimplePattern(reduce:@(* :- ?)) find h flatMap (x => `⟨ ⟩?`(x(*)) map (elements =>
              StratifyReducePod(TermWithHole.puncture(h, x.subterm), reduce, elements, subelements, ψ)))

          case Some((L("Stratify"), List(L("/"), ~(h), ~~(subelements), ~(ψ)))) =>
            val slashes = slasher(h, subelements.head)
            //cert = true
            if (subelements.length == 1 && (slashes eq h))
              List(StratifySlashPod(h, subelements.head, ψ))
            else
              List(StratifySlash2Pod(TermWithHole.puncture(h, slashes), slashes, subelements, ψ))
          case Some((L("Stratify"), List(++(reduce), ~(h), ~~(subelements), ~(ψ)))) =>
            SimplePattern(reduce:@(* :- ?)) find h flatMap (x => `⟨ ⟩?`(x(*)) map (elements =>
              StratifyReducePod(TermWithHole.puncture(h, x.subterm), reduce, elements, subelements, ψ)))
          case Some((L("Synth"), List(~(h), ~(subterm), synthed, ~(ψ), ~~(areaTypes)))) =>
            cert = true
            List(SynthPod(h, subterm, encaps(synthed), evalTerm(synthed), ψ, areaTypes))
          case Some((L("LetSlash"), List(~(h), ~(quadrant), ~(ψ)))) =>
            List(LetSlashPod(h, quadrant, ψ))
          case Some((L("LetReduce"), List(reduce, ~(h), ~~(subelements), ~(ψ)))) =>
            SimplePattern(reduce:@(* :- ?)) find h flatMap (x => `⟨ ⟩?`(x(*)) map (elements =>
              LetReducePod(TermWithHole.puncture(h, x.subterm), reduce, elements, subelements, ψ)))
          case Some((L("Synth"), List(~(h), synthed, ~(ψ)))) =>
            List(LetSynthPod(h, encaps(synthed), ψ))
          case Some((L("Distrib"), List(++(reduce)))) =>
            SimplePattern(reduce :@ (* :- /::(`...`))) find s.program map
                (x => ReduceDistribPod(reduce, x(*).split))
          case Some((L("Assoc"), List(++(reduce)))) =>
            SimplePattern(reduce :@ (* :- ?)) find s.program flatMap (_(*) |> `⟨ ⟩?`) map
                (ReduceAssocPod(reduce, _)) filterNot (_.isTrivial)
          case Some((L("Distrib"), List(L("/"), ~(f), ~(box)))) =>
            List(SlashDistribPod(f, box))
          case Some((L("SlashToReduce"), List(reduce, ~~(elements)))) =>
            List(SlashToReducePod(elements, reduce))

          case Some((L("SaveAs"), List(prog, L(style)))) =>
            val sout = emit(s)
            outf += Map("program" -> encaps(prog).toString, "style" -> style.toString, "text" -> sdisplay(sout.ex), "term" -> sout.program)
            List()

          case Some((cmd, l)) => throw new TranslationError(s"unknown command '${cmd}' (with ${l.length} arguments)") at command
          case _ =>
            throw new TranslationError("not a valid command syntax") at command
        }
      }

    val derivatives = resolvePatterns(command) flatMap pods map instapod

    if (derivatives.isEmpty) s
    else {
      if (cert) derivatives filter (_.obligations != TRUE) foreach invokeProver

      Rewrite(derivatives)(s.program) match {
        case Some(rw) => mkState(rw)
        case _ => throw new TranslationError("rewrite failed?") at command
      }
    }
  }

  def mkState(term: Term) = State(term, extrude(term))

  def invokeProver(pod: Pod) { }

  /*
   * Output part
   */

  def emit(s: State) = mkState(Explicate.explicateHoist(s.program))

  /*
   * JSON part
   */

  import scala.collection.JavaConversions._
  import syntax.Nullable._

  def initial(json: DBObject)(implicit sc: SerializationContainer): State = json.get("check") andThen ({ check =>
    implicit val empty = State.empty
    val A = evalTerm( Formula.fromJson(check.asInstanceOf[DBObject]) )
    State(A, extrude(A) |-- display)
  }, { throw new TranslationError("not a valid start element") })

  def transform(s: State, json: DBObject)(implicit sc: SerializationContainer): State = json match {
    case l: BasicDBList =>  (s /: (l map (_.asInstanceOf[DBObject])))(transform)
    case _ => json.get("check") andThen ({ check =>
      transform(s, Formula.fromJson(check.asInstanceOf[DBObject])) |-- {
        new_s => if (new_s ne s) { display(new_s.ex) ; logf += Rich.display(new_s.ex) }
      }
    }, s)
  }

  def execute(reader: BufferedReader)(implicit sc: SerializationContainer=new DisplayContainer) {
    val head #:: blocks = sc.flatten(CLI.getBlocks(reader) map
        JSON.parse map (_.asInstanceOf[DBObject]))
    (initial(head) /: blocks) { (s, json) => transform(s, json) }
  }

  def executeFile(filename: String)(implicit sc: SerializationContainer=new DisplayContainer) {
    execute(new BufferedReader(new FileReader(filename)))
  }

}

object TacticApplicationEngine {
  case class State(program: Term, ex: ExtrudedTerms)
  object State { val empty = State(program, new ExtrudedTerms(new Tree(program), Map.empty)) }

  object L { def unapply(t: Term) = if (t.isLeaf) Some(t.root.literal) else None }

  /* navigator functions */
  def instapod(it: Term)(implicit scope: Scope) = instantiate(it)._2
  def instapod(it: Pod)(implicit scope: Scope) = new Instantiated(it)

  def fixer(A: Term, q: Term) = SimplePattern(fix(?)) find A map (_.subterm) filter (_.hasDescendant(q)) head
  def fixee(A: Term, q: Term) = fixer(A, q).subtrees(0)
  def ctx(A: Term, t: Term) = TypedLambdaCalculus.context(A, t)

  def slasher(A: Term, q: Term) = A.nodes find (n => n.root == "/" && (n.split(I("/")) exists (_ eq q))) get
}
