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


/**
 * Transforms generated program and adds meta-data that aids code generation.
 */
object OptimizationPass {

  def main(args: Array[String]) {
    val filename = args.headOption getOrElse "/tmp/prog.json"
    val inf = new BufferedReader(new FileReader(filename))

    implicit val cc = new DisplayContainer

    implicit val a = new Recorder()(examples.Paren.env)
    implicit val p = examples.Paren.BreakDown.prover

    ui.CLI.getBlocks(inf) map
        (_ |> JSON.parse |> (_.asInstanceOf[DBObject].get("term")) andThen_
            (Formula.fromJson, { throw new Exception("not a program") })) foreach { program =>
      println(program toPretty)
      val deps = new DependencyAnalysis() apply program
      println(foldAll(deps) toPretty)
    }
  }


  class Recorder(implicit env: Environment) extends Assistant
  {
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

  def foldAll(t: Term): Term = t match {
    case T(`:`, List(lbl@L(txt), x)) if txt.toString contains '[' => preserve(t, lbl)
    case _ => preserve(t, T(t.root, t.subtrees map foldAll))
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

      val respect = new prover.Transaction().commit(List(), queries map (_._4))
          .toList map (_.root == "valid")

      new Dag(vertices = rw map (x => Id(x._1)),
         !! = queries zip respect collect { case (("!!", u, v, _), false) => (u, v) },
         ~> = queries zip respect collect { case (("~>", u, v, _), false) => (u, v) } )
    }

    def readWriteSets(chain: ListMap[Id[Term], List[Term]]) = {
      val head = chain.head._1.get
      val va = TypeTranslation.contract($v, TypeTranslation.emit(rec.scope, typeOf_!(head)))._1 map (T(_))

      chain map { case (term, readSet) =>
        val writeChecks = TypeTranslation.checks(rec.scope, typeOf_!(term.get), va)
        val readChecks =
          readSet map (x => TypeTranslation.checks(rec.scope, typeOf_!(x), va))

        (term.get, (&&(writeChecks), ||(readChecks map &&)))
      }
    }

    def chain(program: Term)(implicit ctx: Context=Context.empty): ListMap[Id[Term], List[Term]] = {

      val `:` = I(":")
      val `↦` = I("↦")
      val `@` = @:.root
      val `/` = I("/")
      val `|!` = I("|!")

      program match {
        case T(Prelude.program.root, List(t)) => chain(t)
        case T(`:`, List(lbl, t)) => chain(t)
        case T(`↦`, List(v, t)) if ctx.vars.length < ctx.maxlen => chain(t)(ctx + v)
        case T(`@`, List(T(`↦`, List(v, t)), a)) =>
          chain(a) ++
          chain(t)(Context(List(v)))
        case T(Prelude.fix.root, List(f)) =>
          chain(f)(ctx + 1)
        case T(`/`, s) => s map chain reduce (_ ++ _)
        case T(`|!`, List(t, cond)) => chain(t)(ctx & cond)
        case _ =>
          if (ctx.vars contains program) ListMap.empty
          else
            bullet(program)
      }
    }

    def bullet(expr: Term)(implicit ctx: Context): ListMap[Id[Term], List[Term]] = {
      ListMap((expr,
        expr.nodes filter ctx.vars.contains toList
      ))
    }

  }


  object DependencyAnalysis {

    case class Context(vars: List[Term], maxlen: Int=1, guards: List[Term]=List.empty) {
      def +(v: Term) = Context(vars :+ v, maxlen, guards)
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

      lazy val layers = gen drop 1 map (_._1) takeWhile (_.nonEmpty)

    }

    val bazinga = TI("bazinga")
  }

}
