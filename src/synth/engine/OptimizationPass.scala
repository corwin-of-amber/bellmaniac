package synth.engine

import java.io.{FileReader, BufferedReader}
import com.mongodb.DBObject
import com.mongodb.util.JSON
import examples.Paren.BreakDown.Interpreter
import report.DevNull
import semantics.TypeTranslation.{TypingSugar, Environment}
import syntax.AstSugar._
import syntax.Formula
import syntax.Piping._
import syntax.Nullable._
import semantics._
import semantics.TypedTerm.typeOf_!
import report.data.DisplayContainer
import synth.engine.TacticApplicationEngine.L
import synth.proof.{Prover, Assistant}
import scala.collection.immutable.ListMap
import semantics.smt.Sequent
import semantics.Reflection.Compound
import syntax.Identifier
import semantics.transform.Explicate
import semantics.pattern.Expansion
import semantics.pattern.MacroMap



/**
 * Transforms generated program and adds meta-data that aids code generation.
 */
object OptimizationPass {

  class Config(args: List[String]) extends ui.Config.BaseCommandLineConfig(args) {
    val filename = trailArg[String](required=false, default=Some("/tmp/prog.json"))
  }
  
  def cfg(args: Array[String]) = { ui.Config.Sources.commandLine = Some[ui.Config.CommandLineConfig](new Config(args.toList)) }


  def main(args: Array[String]) {
    cfg(args)
    val inf = new BufferedReader(new FileReader(ui.Config.config.filename()))

    implicit val cc = new DisplayContainer

    implicit val a = new Recorder()(examples.Paren.env)
    implicit val p = examples.Paren.BreakDown.prover

    ui.CLI.getBlocks(inf) /**/ take 1 /**/ map
        (_ |> JSON.parse |> (_.asInstanceOf[DBObject].get("term")) andThen_
            (Formula.fromJson, { throw new Exception("not a program") })) foreach { program =>
      println(program toPretty)
      //val deps = new DependencyAnalysis() apply program
      //println(foldAllCalls(deps) toPretty)
              
      //inferLoopDirections(program)
      
      val fpan = new FixpointLoopAnalysis
      fpan.inferReadGuards(program)
    }
  }
 
  
  import semantics.smt.Z3Gate.ProverStatus


  def surroundingGuards(term: Term, subterm: Term): Option[List[Term]] = {
    if (subterm eq term) Some(List())
    else if (term =~ ("|!", 2)) surroundingGuards(term.subtrees(0), subterm) map (term.subtrees(1) +: _)
    else term.subtrees map (surroundingGuards(_, subterm)) find (_.isDefined) map (_.get)
  }

  class Recorder(implicit env: Environment) extends Assistant
  {
    // maps *original* program nodes to *transformed* (e.g. simplified) program nodes
    var mapped = new collection.mutable.HashMap[Id[Term], Term]

    override def simplify(term: Term)(implicit argpat: Term=>Boolean) = {
      super.simplify(term) |-- { x => mapped += ((term, x)) }
    }

    def reassoc(program: Term, subterm: Term) =
      program.nodes filter (n => mapped(n).nodes exists (subterm eq)) last
    def reassoc[X](program: Term, subterm: (Term, X)): (Term, X) =
      (reassoc(program, subterm._1), subterm._2)

  }

  import TypedTerm.preserve
  val `:` = I(":")

  def foldAllCalls(t: Term): Term = t match {
    case T(`:`, List(lbl@L(txt), x)) if txt.toString contains '[' => preserve(t, lbl)
    case _ => preserve(t, T(t.root, t.subtrees map foldAllCalls))
  }

  class DependencyAnalysis(implicit rec: Recorder, prover: Prover) {

    import DependencyAnalysis._

    def apply(program: Term) = {
      chain(rec.simplify(program)(_.isLeaf)) |> readWriteSets |> (_.toList) |> layer |>
          (_ map (rec.reassoc(program, _))) |>
          (annotate(program, _)(rec.scope))
    }

    def annotate(program: Term, layering: Iterable[(Term, Int)])(implicit scope: Scope) =
      TypedTerm.replaceDescendants(program, layering map {
        case (x, i) => (x, bazinga(TI(i)) :- x) })

    def layer(rw: List[(Term, (Term, Term))]) = {
      val layers = dagify(rw).layers map (_ map (_.get))

      layers.zipWithIndex flatMap { case (t, i) => t map ((_, i)) } toIterable
    }

    def dagify(rw: List[(Term, (Term, Term))]) = {
      println("~" * 60)
      rw foreach { case (_, (wr, rd)) => println(s"       ${wr toPretty}   /   ${rd toPretty}") }

      def suffixes[A](l: List[A]): Stream[List[A]] = l match {
        case Nil => Stream.empty case x :: xs => l #:: suffixes(xs) }

      def ascpairs[A](l: List[A]) = suffixes(l) flatMap { case x :: xs => xs map ((x, _)) case _ => List() }

      val queries =
        ascpairs(rw.zipWithIndex) flatMap {
          case (((t1, (wr1, rd1)), i1), ((t2, (wr2, rd2)), i2)) =>
            List( ("!!", Id(t1), Id(t2), (rd1 -> ~wr2) & (rd2 -> ~wr1)),
                  ("~>", Id(t1), Id(t2), rd2 -> ~wr1) )
        } toList

      val respect = new prover.Transaction(Prover.Verbosity.None).commit(List(), queries map (_._4))
          .toList map (_.root == "valid")

      new Dag(vertices = rw map (x => Id(x._1)),
         !! = queries zip respect collect { case (("!!", u, v, _), false) => (u, v) },
         ~> = queries zip respect collect { case (("~>", u, v, _), false) => (u, v) } ) |-- (_.toPretty |> println)
    }

    def readWriteSets(chain: ListMap[Id[Term], List[Var]]) = {
      val head = chain.head._1.get
      val va = TypeTranslation.contract($v, TypeTranslation.emit(rec.scope, typeOf_!(head)))._1 map (T(_))

      chain map { case (term, readVars) =>
        val writeChecks = TypeTranslation.checks(rec.scope, typeOf_!(term.get), va)
        val readChecks =
          readVars map (x => TypeTranslation.checks(rec.scope, typeOf_!(x.term), va))

        (term.get, (&&(writeChecks), ||(readChecks map &&)))
      }
    }

    def chain(program: Term)(implicit ctx: Context=Context.empty): ListMap[Id[Term], List[Var]] = {

      val `:` = I(":")
      val `↦` = I("↦")
      val `@` = @:.root
      val `/` = I("/")
      val `|!` = I("|!")

      program match {
        case T(Prelude.program.root, List(t)) => chain(t)
        case T(`↦`, List(v, t)) if ctx.vars.length < ctx.maxlen => chain(t)(ctx + intro(v))
        case T(`@`, List(T(`↦`, List(v, t)), a)) =>   // notice that we count on Assistant.simplify to throw away labels
          chain(a) ++
          chain(t)(Context(List(Input(v))))
        case T(`:`, List(lbl, t)) => assert(false, "labels should have been cleared by now") ; ???
        case T(Prelude.fix.root, List(f)) =>
          chain(f)(ctx + 1)
        case T(`/`, s) => s map chain reduce (_ ++ _)
        case T(`|!`, List(t, cond)) => chain(t)(ctx & cond)
        case _ =>
          link(program)
      }
    }

    def intro(v: Term)(implicit ctx: Context) = if (ctx.vars.isEmpty) Input(v) else Fix(v)
    
    def link(expr: Term)(implicit ctx: Context): ListMap[Id[Term], List[Var]] = 
      if (ctx.vars contains expr) ListMap.empty else nonleaf(expr)
    
    def nonleaf(expr: Term)(implicit ctx: Context): ListMap[Id[Term], List[Var]] = {
      ListMap((expr,
        expr.nodes flatMap (n => ctx.vars.find(_.term == n) map (_/n)) toList
      ))
    }

  }


  object DependencyAnalysis {

    abstract class Var(val term: Term)                   { def /(term: Term): Var }
    case class Input(term_ : Term) extends Var(term_)    { def /(term: Term) = Input(term) }
    case class Fix(term_ : Term) extends Var(term_)      { def /(term: Term) = Fix(term) }
    
    case class Context(vars: List[Var], maxlen: Int=1, guards: List[Term]=List.empty) {
      def +(v: Var) = Context(vars :+ v, maxlen, guards)
      def +(n: Int) = Context(vars, maxlen + n, guards)
      def &(c: Term) = Context(vars, maxlen, guards :+ c)
    }
    object Context { val empty = Context(List.empty) }

    /**
     * Intermediate data structure for computed dependencies.
     * @param vertices list of computation terms
     * @param !! conflicting computations
     * @param ~> dependant computations
     * @tparam A type of vertex
     */
    class Dag[A](vertices: List[A], !! : List[(A, A)], ~> : List[(A, A)]) {

      def nextLayer(chosen: List[A], notchosen: List[A], vertices: List[A]): List[A] = vertices match {
        case Nil => chosen
        case v :: vs =>
          if (chosen.forall(u => ! !!.contains(u,v)) && notchosen.forall(u => ! ~>.contains(u,v)))
            nextLayer(chosen :+ v, notchosen, vs)
          else
            nextLayer(chosen, notchosen :+ v, vs)
      }

      lazy val gen =
        Iterator.iterate(List.empty[A], vertices) { case (_, unused) =>
          val nxt = nextLayer(List(), List(), unused)
          (nxt, unused filterNot nxt.contains)
        }

      lazy val layers = gen drop 1 map (_._1) takeWhile (_.nonEmpty) toIterable

      def toPretty =
        layers flatMap (s =>
          List(" " * (40 - s.length) + " ▢" * s.length,
               " " * 41 + (if (s.length > 1) "┬" else "│"))) dropRight 1 mkString "\n"
    }

    val bazinga = TI("bazinga")
  }


  class FixpointLoopAnalysis(implicit rec: Recorder, prover: Prover) extends DependencyAnalysis {
    import FixpointLoopAnalysis._
    import DependencyAnalysis.{Context,Input,Fix}
    import TypePrimitives.{dom,ret}
    
    implicit val scope = rec.scope
    
    //------------------
    // Read-Guards Part
    //------------------

    def inferReadGuards(program: Term) {
      val sprogram = rec.simplify(program)(_.isLeaf)

      val chain = this.chain(sprogram)
      chain.foreach { case (at, accesses) =>
        println(s"${at.get toPretty}   |   ${accesses map (_.term.toPretty)}")
      }
      val (qdefs, qswitches) =
        sprogram.nodes.collect { case T(Prelude.fix.root, List(f)) =>
          // Compute read-set region formula scheme Q
          // e.g.
          //   Q(i,j) := (J₀(i) ∧ J₀(j)) ∨ (J₀(i) ∧ J₁(j)) ∨ (J₁(i) ∧ J₁(j))
          val accesses = f.nodes flatMap (chain.get(_)) flatten
          val accessTypes = accesses collect { case Input(v) => typeOf_!(v) }
          val Q = $TI("Q", "predicate")
          val Qdef = Q ~> ((x: Term) => Some(argumentsInRegion(x.subtrees, accessTypes)))
          // Add qualifier Q to any occurrence of the fix variable
          val Qswitch =
            f.nodes.collect { 
              case v if v.isLeaf && accesses.contains(Fix(v)) => 
                (v, TypedTerm(v, qualifyRegion(typeOf_!(v), Q)))
            }
          (Qdef, Qswitch)
        } unzip
      // Turn qualifiers into guards using Explicate, and expand the definition
      val explicate = new Explicate()
      val guarded = explicate(TypedTerm.replaceDescendants(sprogram, qswitches.flatten.toIterable)) |-- (_.toPretty |> println)
      val expansion = new Expansion( MacroMap(qdefs:_*) )
      explicate.hoist(expansion(guarded) |-- (_.toPretty |> println)) |-- (_.toPretty |> println)
    }
    
    def argumentsInRegion(args: List[Term], regionTypes: Seq[Term]) =
      ||(regionTypes map (typ => &&(TypeTranslation.checks(scope, typ, args))) toList)

    def qualifyRegion(typ: Term, Q: Term) = (dom(typ) ∩ Q) -> ret(typ)
      
    //---------------------
    // Loop Direction Part
    //---------------------

    // TODO currently just prints the results
    def inferLoopDirections(program: Term) {
      val < = TV("<")
      
      program.nodes find (_ =~ ("fix", 1)) map (_.subtrees.head) map LambdaCalculus.isAbs foreach {
        case Some((theta :: vars, body)) => 
          println(s"$theta    $vars")
          val queries =
          body.nodes map (LambdaCalculus.isAppOf(_, theta)) collect {
            case Some(args) if args.length == vars.length =>
              println(args)
              val aenv = 
                TypeTranslation.decl(rec.scope, args flatMap (TypedLambdaCalculus.contextDecl(program, _)) toMap)
              val dirAttempts = args zip vars flatMap { 
                case (x,y) => List((Dir.FWD, ~(< :@(y,x))), (Dir.BWD, ~(< :@(x,y)))) map {
                 case (dir, goal) => Attempt(y, dir, Compound(surroundingGuards(program, x).get, goal)) 
                } 
              }
              (aenv, dirAttempts)
          }
  
          val pa = prover ++ (queries map (_._1))
          val attempts = queries flatMap (_._2)
  
          val results =
            new pa.Transaction().commit(List(), attempts map (_.goal) toList).toList zip 
              attempts map { case (status, attempt) => attempt ! (status.root == "valid") }
  
          for (v <- vars; dir <- List(Dir.FWD, Dir.BWD)) {
            if (results filter (r => r.v == v && r.dir == dir) forall (_.success==Some(true)))
              println(s"${v}   ${dir} ")
          }
          
        case _ =>
      }
    }
    
    override def link(expr: Term)(implicit ctx: Context) = nonleaf(expr)
  }
  
  object FixpointLoopAnalysis {
    
    //---------------------
    // Loop Direction Part
    //---------------------

    object Dir extends Enumeration {
      type Dir = Value
      val FWD, BWD = Value
    }
    import Dir._
    
    case class Attempt(v: Term, dir: Dir, goal: Compound, success: Option[Boolean]=None) {
      def !(status: Boolean) = Attempt(v, dir, goal, Some(status))
    }
  }
  
}
