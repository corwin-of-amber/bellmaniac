package synth.tactics

import syntax.AstSugar._
import syntax.Identifier
import syntax.Piping._
import synth.proof.Assistant

import semantics._

import scala.collection.immutable.HashSet


object Synth {

  def main(args: Array[String]) {

    implicit val env = examples.Paren.env
    implicit val scope = env.scope

    val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), TV("k"))

    import semantics.Prelude.{R, min, ?}
    import examples.Paren.{J, J0, <}
    import examples.Paren.BreakDown.APod

    val a = new Assistant()

    println("-" * 50)

    val A = APod(J).program
    val f = (A :-/ "f") :: (? ->: ? ->: (J0 x J0) ->: ?) |> a.compile

    val A0 = APod(J0).program
    val f0 = (A0 :-/ "f") :: (? ->: ? ->: (J0 x J0) ->: ?) |> a.compile

    val AP = APod(J ∩ TV("P")).program
    val fP = (AP :-/ "f") :: (? ->: ? ->: (J0 x J0) ->: ?) |> a.compile

    val ir0 = TypedTerm.raw(Explicate.explicate(f))

    println(ir0 toPretty)

    val code0 = CodeGen.codegen(ir0)

    println(code0 toPretty)

    val ir1 = TypedTerm.raw(Explicate.explicate(fP))

    println(ir1 toPretty)

    val code1 = CodeGen.codegen(ir1)

    println(code1 toPretty)

    val sketch = new SketchOutput

    println(sketch(code0))
    println(sketch(code1))
  }

  class Explicate(implicit scope: Scope) {

    import TypedTerm.{preserve, typeOf_!}
    import LambdaCalculus.{isApp, isAbs}

    val @: = I("@")

    def apply(t: Term) = explicate0(t)(collate(t)(List()))

    def explicate0(t: Term)(implicit map: Map[Id[Term], List[Term]]): Term = map get t match {
      case None => preserve(t, T(t.root, t.subtrees map explicate0))
      case Some(Nil) => preserve(t, T(t.root, t.subtrees map explicate0))
      case Some(guard) => preserve(t, preserve(t, T(t.root, t.subtrees map explicate0)) |! &&(guard))
    }

    def collate(t: Term)(implicit assumptions: List[Term]): Map[Id[Term], List[Term]] = isApp(t) match {
      case Some((f, args)) =>
        val precond = nontriv(TypeTranslation.checks(scope, typeOf_!(f), args))
        accumulate(args flatMap collate toMap, t, precond)
      case _ => isAbs(t) match {
        case Some((vars, body)) =>
          val precond = vars filter isScalar flatMap (v => TypeTranslation.checks(scope, v.typedLeaf, List()))
          accumulate(collate(body)(assumptions ++ precond), body, precond)
        case _ =>
          t.subtrees flatMap collate toMap
      }
    }

    def accumulate[A, B](map: Map[A, List[B]], key: A, values: List[B]) = map get key match {
      case None => map + (key -> values)
      case Some(existing) => map + (key -> (existing ++ values))
    }

    def isScalar(t: Term) = typeOf_!(t).root != "->"

    def nontriv(asserts: List[Term])(implicit assumptions: List[Term]) =
      asserts filterNot assumptions.contains
  }

  object Explicate {
    def explicate(t: Term)(implicit scope: Scope) = new Explicate apply t
  }


  class CodeGen {

    import TypedTerm.{preserve, typeOf_!}
    import LambdaCalculus.{isApp, isAbs}
    import synth.pods.ConsPod.`⟨ ⟩?`
    import CodeGen._

    case class Context(vars: List[Term], innerFuncs: collection.mutable.Map[Identifier, (List[Term], Term)])

    def apply(t: Term) = {
      implicit val ctx = Context(List(), collection.mutable.Map.empty)
      try toplevel(expr(t))
      catch {
        case e: TranslationError => throw e at t
      }
    }

    def expr(t: Term)(implicit ctx: Context): Term = {
      if (t.isLeaf) {
        if (!typeOf_!(t).isLeaf || (ctx.vars contains t)) t else TypedTerm(t, scalar)
      }
      else if (t =~ ("|!", 2)) {
        val v = expr(t.subtrees(0))
        TypedTerm((if (typeOf_!(v) == scalar) only else when)(t.subtrees(1), v), scalar)
      }
      else if (t =~ (":", 2)) expr(t.subtrees(1))
      else isApp(t) match {
        case Some((f, args)) =>
          if (!typeOf_!(t).isLeaf) throw new TranslationError(s"high-order return value for '${f}'") at t
          if (args exists (`⟨ ⟩?`(_).isDefined)) reduction(f, args)
          else app(f, args)
        case _ =>
          isAbs(t) match {
            case Some((vars, body)) => preserve(t, abs(vars, body))
            case _ =>
              throw new TranslationError(s"don't quite know what to do with '${t.root}'") at t
          }
      }
    }

    def app(f: Term, args: List[Term])(implicit ctx: Context) = {
      val vals = args map expr
      if (vals forall (x => typeOf_!(x) != scalar))
        TypedTerm(f(vals), scalar)
      else
        TypedTerm(@:(f)(vals), scalar)
    }

    def abs(vars: List[Term], body: Term)(implicit ctx: Context) = {
      val subctx = Context(ctx.vars ++ vars, collection.mutable.Map.empty)
      val defn = expr(body)(subctx)
      val retType = typeOf_!(body)
      val f = TypedIdentifier($I("f", "function"), if (retType.isLeaf) scalar else retType)
      ctx.innerFuncs += (f -> (vars, emit(defn)(subctx)))
      T(f)
    }

    def reduction(f: Term, args: List[Term])(implicit ctx: Context) = {
      if (args.length != 1) throw new TranslationError("unimplemented") at f(args)
      `⟨ ⟩?`(args(0)) match {
        case Some(elements) => elements map expr reduce ((x,y) => TypedTerm(f(x,y), scalar))
        case _ => app(f, args)
      }
    }

    def defn(f: Term, vars: List[Term], body: Term) =  def_(f)(`()`(vars))(body)
    def defn(entry: (Identifier, (List[Term], Term))): Term = entry match { case (f, (vars, body)) => defn(T(f), vars, body) }

    def emit(t: Term)(implicit ctx: Context) = {
      val defns = ctx.innerFuncs map defn
      if (defns.isEmpty) ret(t)
      else `;`(defns toList)(ret(t))
    }

    def toplevel(t: Term)(implicit ctx: Context) = {
      if (!(t.isLeaf && ctx.innerFuncs.size == 1 && ctx.innerFuncs.contains(t.root)))
        throw new TranslationError("top-level expression must be a function") at t
      ctx.innerFuncs.head match { case (f, (vars, body)) => defn(T(f), TypedTerm(TV("n"), Prelude.N) +: vars, body) }
    }
  }

  object CodeGen {
    val scalar = TS("scalar")
    val when = TI("when")
    val only = TI("only")
    val def_ = TI("def")
    val `()` = TI("()")
    val `;` = TI(";")
    val ret = TI("ret")

    def codegen(t: Term) = new CodeGen apply t
  }



  class SketchOutput {

    import CodeGen._
    import TypedTerm.typeOf_!

    val mnemonics = new Mnemonics {
      override def isIdentifierPart(c: Character) = c < 0x100 && super.isIdentifierPart(c)
    }

    def mne(id: Identifier) = mnemonics.get(id)
    def mne(t: Term) = mnemonics.get(t.leaf)

    def apply(code: Term): String = code match {
      case T(def_.root, List(f, T(`()`.root, params), body)) =>
        try s"${typ(typeOf_!(f))} ${mne(f)}(${params map param mkString ", "}) {\n${indent(apply(body))}\n}"
        finally mnemonics release (params map (_.leaf))
      case T(`;`.root, stmts) => stmts map apply mkString "\n"
      case T(@:.root, f :: args) => s"apply(${mne(f)}, ${args map apply mkString ", "})"
      case T(ret.root, List(r)) => s"return ${apply(r)};"
      case T(v, Nil) => s"${mne(v)}"
      case T(InfixOp(op), List(a, b)) => s"(${apply(a)} $op ${apply(b)})"
      case T(Reduction(f), args) => args match {
          case List(T(fn, Nil)) => s"$f(n, ${mne(fn)})"
          case List(T(`f`, List(T(fn, Nil))), b) => s"${f}_acc(${apply(b)}, n, ${mne(fn)})"  // this is an
          case List(a, T(`f`, List(T(fn, Nil)))) => s"${f}_acc(${apply(a)}, n, ${mne(fn)})"  // optimization
          case List(a, b) => s"${f}2(${apply(a)}, ${apply(b)})"
          case _ => throw new TranslationError(s"invalid usage of 'min'") at code
        }
      case T(f, args) => s"${mne(f)}(${args map apply mkString ", "})"
    }

    val INFIX = Map(I("+") -> "+", I("-") -> "-", I("=") -> "==", I("<") -> "<", I(">") -> ">", I("&") -> "&&")

    object InfixOp { def unapply(id: Identifier) = INFIX get id }

    val REDUCT = HashSet(Prelude.min.root)

    object Reduction { def unapply(id: Identifier) = if (REDUCT contains id) Some(id) else None }

    def typ(typ: Term) =
      if (typ == scalar) "|scalar|"
      else if (typ.isLeaf) "int"
      else "fun"

    def param(t: Term) = s"${typ(typeOf_!(t))} ${mne(t)}"

    def indent(block: String) = block split "\n" map ("    " + _) mkString "\n"
  }
}

