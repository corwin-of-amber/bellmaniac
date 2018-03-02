package synth.engine

import java.io.{File, FileReader, BufferedReader}
import com.mongodb.util.JSON
import com.mongodb.{BasicDBList, DBObject}
import report.{AppendLog, FileLog}
import report.console.Console._
import report.console.Console.display
import report.data.{Rich, SerializationContainer, DisplayContainer}
import semantics.Prelude._
import semantics.TypedScheme.TermWithHole
import semantics.pattern.SimplePattern
import semantics.transform.Explicate
import semantics._
import semantics.TypeTranslation.Environment
import syntax.AstSugar._
import syntax.Piping._
import syntax.{Tree, Formula}
import syntax.transform.{ExtrudedTerms, Extrude}
import synth.pods.ConsPod._
import synth.pods.TacticalError
import synth.pods._
import synth.proof.Prover
import synth.tactics.Rewrite._
import synth.tactics.{SliceAndDicePod, SlicePod, Synth}
import synth.engine.OptimizationPass.DependencyAnalysis
import synth.engine.OptimizationPass.FixpointLoopAnalysis
import ui.CLI
import syntax.transform.TreeSubstitution
import syntax.transform.GenTreeSubstitution



class TacticApplicationEngine(implicit val scope: Scope, val env: Environment) {
  import TacticApplicationEngine._

  implicit val extrude = Extrude(Set(I("/"), cons.root))

  // Override to redirect
  lazy val          outf: AppendLog = new FileLog(new File("/tmp/prog.json"), new DisplayContainer)
  implicit lazy val logf: AppendLog = new FileLog(new File("/tmp/bell.json"), new DisplayContainer)

  /*
   * Eval part
   */

  def evalTerm(expr: Term)(implicit s: State): Term = {
    if (expr =~ (".", 0)) s.cursor
    else if (expr.isLeaf) {
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
      case T(`@:`, List(~~(l1), ~~(l2))) => for (a <- l1; b <- l2) yield a x b
      case _ =>
        val eexpr = evalTerm(expr)
        ConsPod.`⟨ ⟩?`(eexpr) match {
          case Some(l) => l
          case _ => List(eexpr)  // singleton
        }
    }
  }

  def list(expr: Term): List[Term] = ConsPod.`⟨ ⟩?`(expr) getOrElse List(expr)

  def ctx_?(subterm: Term, expr: Term)(implicit s: State) =
    if (expr.isLeaf && TypedTerm.typeOf(expr).isEmpty)
      ctx(s.program, subterm) getOrElse (expr.root.literal, throw new Exception(s"undefined variable ${expr}"))//expr)
    else expr

  def subterm_?(term: Term, expr: Term) =
    if (term.nodes exists (_ eq expr)) expr else (new SimplePattern(expr) findOne_! term).subterm

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

  val prototypes: Map[Term, Term] = Map.empty

  def encaps(t: Term) = LambdaCalculus.isApp(t) match {
    case Some((f,args)) => $TV(s"${f toPretty}[${args map (_.toPretty) mkString ","}]")
    case _ => $TV(t.toPretty)
  }

  object ~ { def unapply(expr: Term)(implicit s: State) = Some(evalTerm(expr)) }
  object ~~ { def unapply(expr: Term)(implicit s: State) = Some(evalList(expr)) }
  object `⟨⟩` { def unapply(expr: Term) = Some(list(expr)) }
  object #: { def unapply(expr: Term) = expr match {
    case L(n : Int) => Some(n)  case _ => None
  } }
  object ++ { def unapply(expr: Term) = expr match {
    case L("min") | L("max") => Some(expr)  case _ => None
  } }

  val @: = I("@")
  val * = TI("*")

  def commandArgs(command: Term) =
    if (command.isLeaf) Some(command, List()) else LambdaCalculus.isApp(command)

  def command(command: Term)(implicit s: State): Iterable[Pod] = commandArgs(command) match {
    case Some((L("Slice"), List(~(f), ~~(domains)))) =>
      List(new SlicePod(f, domains) with PodOrigin { override val tactic = command })

    case Some((L("Slice"), List(~(h), ~(θ), ~~(domains)))) =>
      val f = subterm_?(h, θ)
      List(new SliceAndDicePod(h, f, domains, (l: Iterable[Term]) => /::(l.toList)) with PodOrigin { override val tactic = command })
    case Some((L("Slice"), List(~(h), ~(θ), ~~(domains), ++(reduce)))) =>
      val f = subterm_?(h, θ)
      List(new SliceAndDicePod(h, f, domains, (l: Iterable[Term]) => reduce:@`⟨ ⟩`(l)) with PodOrigin { override val tactic = command })

    /* deprecated 
    case Some((L("StratifySlash"), List(~(h), ~(quadrant), ~(ψ_)))) =>
      val ψ = ctx_?(h, ψ_)
      List(StratifySlashPod(h, quadrant, ψ))
    case Some((L("StratifyReduce"), List(reduce, ~(h), ~~(subelements), ~(ψ_)))) =>
      val ψ = ctx_?(h, ψ_)
      SimplePattern(reduce:@(* :- ?)) find h flatMap (x => `⟨ ⟩?`(x(*)) map (elements =>
        StratifyReducePod(TermWithHole.puncture(h, x.subterm), reduce, elements, subelements, ψ)))
    case Some((L("LetSlash"), List(~(h), ~(quadrant), ~(ψ_)))) =>
      val ψ = ctx_?(h, ψ_)
      List(LetSlashPod(h, quadrant, ψ))
    case Some((L("LetReduce"), List(reduce, ~(h), ~~(subelements), ~(ψ_)))) =>
      val ψ = ctx_?(h, ψ_)
      SimplePattern(reduce:@(* :- ?)) find h flatMap (x => `⟨ ⟩?`(x(*)) map (elements =>
        LetReducePod(TermWithHole.puncture(h, x.subterm), reduce, elements, subelements, ψ)))
		*/
    case Some((L("Stratify"), List(L("/"), ~(h), ~~(subelements), ~(ψ_)))) =>
      val slashes = slasher(h, subelements.head)
      val ψ = ctx_?(subelements.head, ψ_)
      if (subelements.length == 1 && TypedTerm.eq(slashes, h))
        List(new StratifySlashPod(h, subelements.head, ψ) with PodOrigin { override val tactic = command })
      else
        List(new StratifySlash2Pod(TermWithHole.puncture(h, slashes), slashes, subelements, ψ) with PodOrigin { override val tactic = command })
    case Some((L("Stratify"), List(++(reduce), ~(h), ~~(subelements), ~(ψ_)))) =>
      val ψ = ctx_?(subelements.head, ψ_)
      SimplePattern(reduce:@(* :- ?)) find h flatMap (x => `⟨ ⟩?`(x(*)) map (elements =>
        new StratifyReducePod(TermWithHole.puncture(h, x.subterm), reduce, elements, subelements, ψ) with PodOrigin { override val tactic = command }))
    case Some((L("Synth"), List(~(h), ~(subterm), synthed, ~(ψ_), ~~(areaTypes)))) =>
      val ψ = ctx_?(subterm, ψ_)
      val impl = Synth.Alignment.stripProg(evalTerm(synthed))
      List(new SynthPod(h, subterm, encaps(synthed) :- impl, impl, ψ, areaTypes) with PodOrigin { override val tactic = command })
    case Some((L("Let"), List(L("/"), ~(h), ~(quadrant), ~(ψ_)))) =>
      val ψ = ctx_?(quadrant, ψ_)
      List(new LetSlashPod(h, quadrant, ψ) with PodOrigin { override val tactic = command })
    case Some((L("Let"), List(++(reduce), ~(h), ~~(subelements), ~(ψ_)))) =>
      val ψ = ctx_?(subelements.head, ψ_)
      SimplePattern(reduce:@(* :- ?)) find h flatMap (x => `⟨ ⟩?`(x(*)) map (elements =>
        new LetReducePod(TermWithHole.puncture(h, x.subterm), reduce, elements, subelements, ψ) with PodOrigin { override val tactic = command }))
    case Some((L("Synth"), List(~(h), synthed, ~(ψ_)))) =>
      val ψ = ctx_?(h, ψ_)
      val impl = Synth.Alignment.stripProg(evalTerm(synthed))
      List(new LetSynthPod(h, encaps(synthed) :- impl, impl, ψ) with PodOrigin { override val tactic = command })

    case Some((L("SynthAuto"), List(~(h), ~(subterm), `⟨⟩`(templates), ~(ψ_)))) =>
      val ψ = ctx_?(h, ψ_)
      val (synthed, footprint) = invokeSynthesis(h, subterm, templates, fix=true)
      val impl = Synth.Alignment.stripProg(evalTerm(synthed))
      def fillin(command: Term) = command.replaceDescendants(command.nodes collect { case t if t =~ (".",0) => (t,s.cursor) case t if t =~ ("...",0) => (t,encaps(synthed)) }  toList)
      List(new SynthPod(h.subtrees(0), subterm, encaps(synthed) :- impl, impl, ψ, footprint) with PodOrigin { override val tactic = fillin(command) })
    case Some((L("SynthAuto"), List(~(h), `⟨⟩`(templates), ~(ψ_)))) =>
      val ψ = ctx_?(h, ψ_)
      fixer_?(s.program, h) match {
        case Some(fx) =>  // @@@ repeating code from previous case...
          List(new SynthPod.Placeholder(fx.subtrees(0), h, ψ) {
            def compute() = {
              val (synthed, footprint) = invokeSynthesis(fx, h, templates, fix=true)
              val impl = Synth.Alignment.stripProg(evalTerm(synthed))
              def fillin(command: Term) = command.replaceDescendants(command.nodes collect { case t if t =~ (".",0) => (t,s.cursor) case t if t =~ ("...",0) => (t,encaps(synthed)) }  toList)
              new SynthPod(fx.subtrees(0), h, encaps(synthed) :- impl, impl, ψ, footprint) with PodOrigin { override val tactic = fillin(command) }
            }
          })
        case _ =>
          List(new LetSynthPod.Placeholder(h, ψ) {
            def compute() = {
              val (synthed, _) = invokeSynthesis(h, h, templates, fix=false)
              val impl = Synth.Alignment.stripProg(evalTerm(synthed))
              def fillin(command: Term) = command.replaceDescendants(command.nodes collect { case t if t =~ (".",0) => (t,s.cursor) case t if t =~ ("...",0) => (t,encaps(synthed)) }  toList)
              new LetSynthPod(h, encaps(synthed) :- impl, impl, ψ) with PodOrigin { override val tactic = fillin(command) }
            }
          })
      }

    case Some((L("Distrib"), List(L("/"), ~(f)))) =>
      val box = SimplePattern(? /: ?) findOne_! f
      List(new SlashDistribPod(f, box.subterm) with PodOrigin { override val tactic = command })
    case Some((L("Distrib"), List(L("/"), ~(f), ~(box)))) =>
      List(new SlashDistribPod(f, box) with PodOrigin { override val tactic = command })
    case Some((L("Distrib"), List(++(reduce)))) =>
      SimplePattern(reduce :@ (* :- /::(`...`))) find s.program map
          (x => new ReduceDistribPod(reduce, x(*).split) with PodOrigin { override val tactic = command })
    case Some((L("Assoc"), List(++(reduce)))) =>
      SimplePattern(reduce :@ (* :- ?)) find s.program flatMap (_(*) |> `⟨ ⟩?`) map
          (new ReduceAssocPod(reduce, _) with PodOrigin { override val tactic = command }) filterNot (_.isTrivial)
    case Some((L("SlashToReduce"), List(reduce, ~~(elements)))) =>
      List(new SlashToReducePod(elements, reduce) with PodOrigin { override val tactic = command })

    case Some((L("SaveAs"), List(prog, L(style)))) =>
      emit(s, encaps(prog).toString, style.toString)
      List()

    case Some((L("Opt"), Nil)) =>
      // TODO move call to invokeOptimize in here somehow
      List()

    case Some((cmd, l)) => throw new TranslationError(s"unknown command '${cmd}' (with ${l.length} arguments)") at command
    case _ =>
      throw new TranslationError("not a valid command syntax") at command
  }
  
  def initial(term: Term): State = {
    implicit val empty = State.empty
    val A = evalTerm(term) match {
      case prg @ T(program.root, _) => prg
      case x => program(instapod(x))
    }
    mkState(A)
  }

  def transform(s: State, command: Term, progress: (State => Unit) = (s) => {}): State = {

    if (command =~ ("Opt", 0)) return invokeOptimize(s) |> mkState

    var within = List(s.program)
    var opt_withDownCast = Rewrite.Options.default.withDownCast
    def pods(command: Term)(implicit s: State): Iterable[Pod] =
      ConsPod.`⟨ ⟩?`(command) match {
        case Some(commands) => commands flatMap pods
        case _ => LambdaCalculus.isAbs(command) match {
          case Some((locs, body)) => locs flatMap (loc => pods(body)(s -> evalTerm(loc)))
          case _ => command match {
            case T(`@:`, List(T(`@:`, List(cmd, L("in"))), ~~(terms))) => within = terms ; pods(cmd)
            case T(`@:`, List(cmd, L("exactly"))) => opt_withDownCast = false ; pods(cmd)
            case _ => this.command(command)
          }
        }
      }

    
    val derivatives = resolvePatterns(command)(s) flatMap (pods(_)(s)) map instapod
    val opts = Rewrite.Options(withDownCast=opt_withDownCast)
    
    if (derivatives.isEmpty) s
    else {
      derivatives filter (_.it |> cert_?) filter (_.obligations != TRUE) foreach invokeProver

      val outcome =
        zipWithIsLast(fulfill(derivatives)) map { case (derivatives, isLast) =>
          Rewrite(derivatives, opts)(s.program, within) match {
            case Some(rw) => mkState(rw) |-- (if (isLast) noop else progress)
            case _ => /* ignore if not last? */
              throw new TranslationError("rewrite failed?") at command
          }
        }
      
      outcome.last
    }
  }
  
  def fulfill(pod: Instantiated[Pod]) = {
    pod.it match {
      case promise: PromisePod => 
        try {
          val pod = promise.compute() |> instapod
          if (cert_?(pod.it) && pod.obligations != TRUE) invokeProver(pod)
          pod
        }
        catch { case e: Exception => println(e); new Instantiated(new Pod { }) }
      case _ => pod
    }
  }
  
  def fulfill(pods: Iterable[Instantiated[Pod]]): Stream[Iterable[Instantiated[Pod]]] = {
    pods find (_.it.isInstanceOf[PromisePod]) match {
      case Some(pod) => pods #:: fulfill(pods map ((x) => if (x eq pod) fulfill(pod) else x))
      case None => Stream(pods).force  // - make sure stream has definite size = 1
    }
  }
  
  def zipWithIsLast[X](s: Stream[X]): Stream[(X, Boolean)] = s match {
    case Stream.Empty => Stream.empty
    case _ => (s.head, s.hasDefiniteSize && s.size == 1) #:: zipWithIsLast(s.tail)
    // note: not using pattern matching for second case;
    // this would force computation of s.tail.
  }
  
  def cert_?(p: Pod) = {
    val cert = ui.Config.config.cert()
    if (cert contains "all") true
    else p match {
      case _: SynthPod | _: LetSynthPod => cert contains "Synth"
      case _: StratifySlashPod | _: StratifySlash2Pod | _: LetSlashPod => cert contains "/"
      case _: StratifyReducePod | _: LetReducePod => cert contains "reduce"
      case _: SlicePod | _: SliceAndDicePod => cert contains "Slice"
      case _: SlashDistribPod => cert contains "Distrib"
      case _ => false
    }
  }
  
  def mkState(term: Term) = State(term, extrude(term))
  
  def mkState[Tag](tagged: (Term, Tag)) = {
    val (term, tag_) = tagged
    new State(term, extrude(term)) with Tagged[Tag] { override val tag = tag_ }
  }

  def display(program: Term) { display(extrude(program)) }
  def display(ex: ExtrudedTerms) { report.console.Console.display(ex) }
  def display(s: State) {
    display(s.ex) ; logf += Map("term" -> s.program, "display" -> Rich.display(s.ex))
  }
  
  /*
   * Services part
   */

  implicit lazy val prover: Prover = new Prover(List.empty)(Environment.empty)
  def prover(forProgram: Term): Prover = prover
  
  def invokeProver(pod: Pod) { }
  
  def invokeSynthesis(h: Term, subterm: Term, templates: List[Term], fix: Boolean)(implicit s: State) = {

    val expandedTemplates = templates flatMap { template =>
      if (template =~ ("...", 0)) prototypes.values
      else if (template.isLeaf)
        Some(prototypes getOrElse (template, { throw new TacticalError("no such subprogram") at template }))
      else Some(template)
    }

    val ipods = expandedTemplates flatMap { template =>
      LambdaCalculus.isApp(template) match {
        case Some((name, args)) => Some(pods apply (name, args))  // note: do not typecheck yet
        case _ => throw new Exception("invalid synth template")
      }
    }

    val solution = (if (fix) Synth.synthesizeFixPodSubterm(h, subterm, ipods)
                        else Synth.synthesizeFlatPodSubterm(h, subterm, ipods)).run()
    println(solution mapValues (_.toPretty))

    val selected = expandedTemplates(solution("selected").root.literal.asInstanceOf[Int])
    def param(t: Term) = `⟨ ⟩?`(t) match {
      case None => t
      case Some(List(j0, T(`∩`, List(j, p)))) => j ∩ T(I(s"${j0}∪${p}", "predicate"))
      case _ => throw new TacticalError(s"internal error: something unexpected returned from Sketch: ${t.toPretty}")
    }
    val synthed = selected.replaceDescendants(
      selected.nodes collect { case n@T(`∩`, List(L("?"), L(k:String))) => (n, param(solution(k))) } toList)
    val paramSubst = new GenTreeSubstitution(solution map { case (k,v) => (TI(k), ((_:Term) => param(v))) } toList)
    val quadrant = TypePrimitives.curry(TypedTerm.typeOf_!(subterm))._2
    val footprint = TypePrimitives.dom(quadrant) :: evalList(paramSubst(solution.getOrElse("Q", nil)))

    (synthed, footprint)
  }

  /**
   * Called by the "Opt" command; should be deperecated.
   */
  def invokeOptimize(implicit s: State) = {
    if (ui.Config.config.opt()) {
      val prover = this.prover(s.program)
      val rec = new OptimizationPass.Recorder()(prover.env)
      s.program |> (new DependencyAnalysis()(rec, prover) apply)
    }
    else s.program
  }

  /*
   * Output part
   */

  def emit(s: State) = {
    if (ui.Config.config.opt()) {
      val prover = this.prover(s.program)
      val rec = new OptimizationPass.Recorder()(prover.env)
      val fpe = new FixpointLoopAnalysis()(rec, prover)
      val opt =
        invokeOptimize(s)/*.program*/ |> OptimizationPass.foldAllCalls |> (fpe.apply_+)
      mkState(opt)
    }
    else s
  }

  def emit(s: State, name: String, style: String): State = {
    val sout = emit(s)
    val m = Map("program" -> name, "style" -> style,
                "text" -> sdisplay(sout.ex), "term" -> sout.program, "scope" -> scope)
    sout match {
      case sout: State with Tagged[_] => outf += m + ("tag" -> sout.tag.asInstanceOf[AnyRef])
      case _ => outf += m
    }
    sout
  }

  /*
   * JSON part
   */

  import scala.collection.JavaConversions._
  import syntax.Nullable._

  def initial(json: DBObject)(implicit sc: SerializationContainer): State = json.get("check") orElse json.get("term") andThen ({ check =>
    initial( Formula.fromJson(check.asInstanceOf[DBObject]) ) |-- display
  }, { throw new TranslationError("not a valid start element") })

  def transform(s: State, cmd: DBObject)(implicit sc: SerializationContainer): State =
    transform(s, cmd, (_: State) => {})
    
  def transform(s: State, cmd: DBObject, progress: State => Unit)(implicit sc: SerializationContainer): State = {
    val disp_!= = (`s'`: State) => if (`s'` ne s) { display(`s'`) }
    cmd match {
      case l: BasicDBList =>  (s /: (l map (_.asInstanceOf[DBObject])))(transform(_, _, disp_!= +| progress))
      case _ => cmd.get("check") orElse cmd.get("tactic") andThen_ (
        (_:DBObject) |> Formula.fromJson |> (transform(s, _, disp_!= +| progress)) |-- disp_!=
      , s)
    }
  }
  
  def transform(s: DBObject, cmd: DBObject)(implicit sc: SerializationContainer): State =
    transform(s, cmd, (_: State) => {})
    
  def transform(s: DBObject, cmd: DBObject, progress: State => Unit)(implicit sc: SerializationContainer): State =
    transform(mkState(s |> Formula.fromJson |> Binding.prebind), cmd, progress)
  
  def finalize(s: State) {
    val prog = s.program |> OptimizationPass.foldAllCalls
    if (prog != s.program) {
      println("=" * 80)
      display(prog)
    }
  }
  
  def execute(reader: BufferedReader)(implicit sc: SerializationContainer=new DisplayContainer) {
    val head #:: blocks = sc.flatten(CLI.getBlocks(reader) map
        JSON.parse map (_.asInstanceOf[DBObject]))
    (initial(head) /: blocks) { (s, json) => transform(s, json) } |> finalize
  }

  def executeFile(filename: String)(implicit sc: SerializationContainer=new DisplayContainer) {
    execute(new BufferedReader(new FileReader(filename)))
  }

}

object TacticApplicationEngine {
  case class State(program: Term, ex: ExtrudedTerms, cursor: Term=program) {
    def ->(loc: Term) = State(program, ex, loc)
  }
  object State { val empty = State(program, new ExtrudedTerms(new Tree(program), Map.empty)) }

  trait Tagged[A] extends State { val tag: A }
  
  object L { def unapply(t: Term) = if (t.isLeaf) Some(t.root.literal) else None }

  /* Pod instantiation */
  class Instantiated[RawPod <: Pod](val it: RawPod)(implicit scope: Scope) extends Pod {
    override val program = instantiate(it.program)._2
    override val obligations = if (it.obligations == semantics.Prelude.program) program else instantiate(it.obligations)._2
    override val decl = it.decl
  }
  def instapod(it: Term)(implicit scope: Scope) = instantiate(it)._2
  def instapod(it: Pod)(implicit scope: Scope) = new Instantiated(it)

  trait PodOrigin { val tactic: Term }
  
  /* navigator functions */
  def fixer_?(A: Term, q: Term) = SimplePattern(fix(?)) find A map (_.subterm) filter (_.hasDescendant(q)) headOption

  def fixer(A: Term, q: Term) = fixer_?(A, q) getOrElse { throw new TacticalError("no surrounding fix() found") at q }
  def fixee(A: Term, q: Term) = fixer(A, q).subtrees(0)
  def ctx(A: Term, t: Term) = TypedLambdaCalculus.context(A, t)

  def slasher(A: Term, q: Term) = A.nodes find (n => n.root == "/" && (TypedTerm.split(n, I("/")) exists (_ eq q))) get
}


/* Pod manufacturing */
trait PodFactory extends TacticApplicationEngine {
  import syntax.Subroutine
  import syntax.Subroutine.Arity
  import syntax.Strip
  import TacticApplicationEngine._

  def fac: Map[Any,Subroutine[Term,Pod] with Arity]
  
  override def pods(implicit s: State) = {
    case (L(name), args) if fac.contains(name) => fac(name)(args)
  }

  val ph = Strip.subscriptIndexed("P").andThen(TV(_))

  override val prototypes = fac map { case (name, sr) => TV(name) → (TV(name):@(1 to sr.arity map ph map (? ∩ _) toList)) } toMap
}
  
