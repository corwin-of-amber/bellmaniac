package synth.tactics

import java.io._
import semantics.Prelude._
import semantics.TypePrimitives._
import semantics.TypedLambdaCalculus._
import semantics.TypedTerm._
import scala.collection.mutable.ListMap
import scala.collection.JavaConversions._
import com.mongodb.util.JSON
import com.mongodb.BasicDBList
import semantics.TranslationError
import semantics.TypeTranslation.TypingSugar
import semantics.pattern.SimplePattern
import syntax.AstSugar._
import syntax.{Unify, Strip, Identifier}
import syntax.Piping._
import syntax.transform.{Extrude, Mnemonics}
import semantics._
import semantics.TypeTranslation.TypingSugar._
import semantics.transform.{Escalate, Explicate}
import synth.proof.Assistant
import synth.pods.{ConsPod, Pod}
import synth.pods.TacticalError
import report.data.Cached
import syntax.Scheme
import syntax.Scheme.SimplePredicateSymbol
import semantics.TypedScheme.Template



object Synth {

  val extrude = new Extrude(Set(I("/"), Prelude.cons.root, Prelude.fix.root))

  def main(args: Array[String]) {

    implicit val env = examples.Paren.env
    implicit val scope = env.scope

    val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), TV("k"))

    import semantics.Prelude.{R, min, ?, fix}
    import examples.Paren.{J, J0, J1, K1, K2}
    import examples.Paren.BreakDown.{APod, BPod, CPod}
    import TypedTerm.typeOf_!
    import TypedLambdaCalculus.pullOut

    val a = new Assistant()

    println("-" * 50)

    val * = TI("*")

    val scopegen = new ScopeGen(examples.LCS.scope)
    val out = new SketchOutput
    val scopedecl = scopegen() map (out(_)) mkString "\n"
    
    println(scopedecl)
    
    if (false)
    {
      val prog = APod(J).program |> a.compile
      val f = (SimplePattern(fix(* :- ?)) findOne_! prog)(*)
      val ψ = TypedLambdaCalculus.context(prog, f)("ψ")

      val A = fix(/::(
        f :: ((? x J0 x J0) -> R),
        ($TV ↦ ψ) :: ((? x J0 x J1) -> R),
        ($TV ↦ ψ) :: ((? x J1 x J1) -> R)
      )) |> a.compile
      
      val AP = APod(? ∩ TV("P"))
      val BP = BPod(J ∩ TV("P1"), J ∩ TV("P2"))
      val CP = CPod(J ∩ TV("P1"), J ∩ TV("P2"), J ∩ TV("P3"))

      val X = J0 x J0

      report.console.Console.display(extrude(A))
      report.console.Console.display(extrude(AP.program))

      val solution = synthesizeFixPod(A, List(AP, BP, CP), X -> R).run()

      println(solution mapValues (_.toPretty))
    }

    if (false)
    {
      val B = (SimplePattern(* :- fix(?)) findOne_! BPod(J0, J1).program)(*) |> a.compile
      val BP = BPod(? ∩ TV("P1"), ? ∩ TV("P2")).program |> a.compile

      val X = K1 x K2

      val solution = synthesizeFix(B, List(BP), X -> R).run()

      println(solution mapValues (_.toPretty))
    }
  }

  class Sketch(val skfile: File, val incdirs: List[String]=Sketch.INCPATH) {
    import Sketch._
    import syntax.Nullable._
    
    val baseDir = new File(System.getenv("BELLMANIA_HOME").opt getOrElse ".")
    val fe_inc = incdirs flatMap (x => Seq("--fe-inc", new File(baseDir, x).getPath))
    val fe_codegen = Seq("--fe-custom-codegen", new File(baseDir, CODEGEN).getPath)
    val slv = Seq("--slv-lightverif", "--slv-simiters", "50", "--beopt:simstopsize", "200")
    
    val command =
      Seq(SKETCH) ++ slv ++ fe_inc ++ fe_codegen ++ Seq(skfile.getPath)

    def run()(implicit scope: Scope) = {
      cached getOrElse (hash, {
        import scala.sys.process._
        println("# Sketch...")
        try {
          (new ReadSketchResults() apply command.lineStream) |-- save
        }
        catch { case e: RuntimeException => throw new TacticalError(s"Sketch failed (${e})") }
      })
    }

    def incdir(dir: String) = new Sketch(skfile, dir :: incdirs)
      
    def hash = {
      // Can someone explain to me why it is so cumbersome to compute MD5 sum of a file in Java
      import java.security._
      import javax.xml.bind.DatatypeConverter
      val md = MessageDigest.getInstance("MD5")
      val dis = new DigestInputStream(new FileInputStream(skfile), md)
      while (dis.read(new Array[Byte](1 << 12)) != -1) {}
      dis.close()
      DatatypeConverter.printHexBinary(md.digest())
    }
    def save(results: Map[String, Term]) = cached += hash -> results
  }

  object Sketch {
    val SKETCH = "sketch"
    val INCPATH = List("src/synth/tactics/sketch", "examples/intermediates/sketch/generic")
    val CODEGEN = "ccg.jar"

    import report.data.Deserialize._
    
    val cached = ui.Config.config.cache() match { 
      case true => new Cached[Term]("cache.json") 
      case false => collection.mutable.Map.empty[String, Map[String,Term]] 
    }
    
    // --------------
    // Benchmark part
    // --------------
    var benchmarkCounter = 0
    def benchmarkNext = 
      new File(s"/tmp/synth-autogened-$benchmarkCounter.sk") |-- { _ => benchmarkCounter += 1 }
    
  }

  def synthesizeFixPod(term: Term, pods: Iterable[Pod], quadrant: Term)(implicit scope: Scope) = {
    val intendedShape = shape(typeOf_!(term))
    val θ = $TV("θ")

    val instances = pods flatMap (
        Alignment.refit(_, intendedShape, intendedShape, (term, body) =>
          if (body.nodes exists (_ =~ ("fix", 1))) term
          else term.replaceDescendant((body, fix(θ ↦ body)))
        )
      )

    for (instance <- instances) {
      extrude(instance) |-- report.console.Console.display
    }

    synthesizeFix(term, instances, quadrant)
  }

  def synthesizeFlatPod(term: Term, pods: Iterable[Pod], quadrant: Term)(implicit scope: Scope) = {
    import Alignment.θ_↦

    val intendedShape = shape(typeOf_!(term))
    val θ = $TV("θ")

    val instances = pods flatMap (
        Alignment.refit(_, intendedShape, intendedShape -> intendedShape,
          (term, body) =>
          if (body =~ ("fix", 1)) term.replaceDescendant(body, body.subtrees(0))
          else term.replaceDescendant((body, θ ↦ body))
        )
      )

    for (instance <- instances) {
      extrude(instance) |-- report.console.Console.display
    }

    synthesizeFlat(θ_↦(term), instances, quadrant)
  }

  object Alignment {

    import Prelude.program
    val * = TI("*")
    val ↦ = I("↦")
    val `:` = I(":")
    val :: = I("::")

    def refit(pod: Pod, shape: Term, reshape: Term, hack: (Term, Term) => Term)(implicit scope: Scope) = {
      val shallow = TypeInference.inferShallow(Binding.prebind(pod.program))._2
      findBodyWithType(stripProg(shallow), shape) map { body =>
        val inputs = enclosure(shallow, body) get
        val intendedType = (inputs :\ reshape)((x,y) => ? -> y)
        val refitted = hack(shallow, body)
        stripProg(refitted.untype :: intendedType) |> (TypeInference.infer(_)._2)
      }
    }

    def findBodyWithType(prog: Term, typ: Term): Option[Term] = prog match {
      case typed: TypedTerm if Unify.?(typed.typ, typ) => Some(typed)
      case T(`↦`, List(v, body)) => findBodyWithType(body, typ)
      case T(`:`, List(_, term)) => findBodyWithType(term, typ)
      case T(`::`, List(term, _)) => findBodyWithType(term, typ)
      case _ => None
    }

    def stripProg(prog: Term) = prog match {
      case T(program.root, List(p)) => p
      case T(`::`, List(T(program.root, List(p)), typ)) => p :: typ
      case _ => prog
    }

    def θ_↦(t: Term) = typecheck0($TyTV("θ", typeOf_!(t)) ↦ t)

  }


  def synthesizeFixPodSubterm(term: Term, subterm: Term, pods: Iterable[Pod])(implicit scope: Scope) = {
    val quadrant = TypePrimitives.curry(TypedTerm.typeOf_!(subterm))._2

    synthesizeFixPod(term, pods, quadrant)
  }

  def synthesizeFlatPodSubterm(term: Term, subterm: Term, pods: Iterable[Pod])(implicit scope: Scope) = {
    val quadrant = TypedTerm.typeOf_!(subterm)

    synthesizeFlatPod(term, pods, quadrant)
  }

  def synthesizeFix(h: Term, hP: Iterable[Term], quadrant: Term)(implicit scope: Scope) = {
    import Prelude.{fix,?}
    val * = TI("*")
    val `fix(?)` = SimplePattern(fix(* :- ?))

    val f = try pullOut(h, (`fix(?)` find h).head(*)) get
            catch { case _: NoSuchElementException => throw new TacticalError("not a recursive term") at h }
    val fP = hP flatMap (hP => pullOut(hP, (`fix(?)` find hP).head(*))) filter
                        (fP => shape(typeOf_!(fP)).nodes contains shape(typeOf_!(f)))

    if (fP.isEmpty) throw new TacticalError("no suitable candidates for given type") at f :: typeOf_!(f)

    synthesizeFlat(f, fP, quadrant)
  }

  def synthesizeFlat(f: Term, fP: Iterable[Term], quadrant: Term)(implicit scope: Scope) = {
    val escalate = new Escalate
    val explicate = new Explicate
    val codegen = new CodeGen
    val scopegen = new ScopeGen(scope)

    val ir0 = f |> escalate.apply |> explicate.apply |> TypedTerm.raw |> TypedLambdaCalculus.simplify

    println(ir0 toPretty)

    val code0 = codegen(ir0, "h")  |--  { code0 => println(code0 toPretty) }

    val ir1 = fP map (_ |> escalate.apply |> explicate.apply |> TypedTerm.raw |> TypedLambdaCalculus.simplify)

    val code1 = for ((ir1,i) <- ir1.zipWithIndex) yield {
      println(ir1 toPretty)

      codegen(ir1, s"f_$i")  |--  { code1 => println(code1 toPretty) }
    }

    import Prelude._
    val builtin = Set(min, max, cons, nil, TV("+"), TV("-"))
    val decl = codegen.decl(LambdaCalculus.uncurry(ir0)._1 ++ (((ir0 :: ir1.toList) flatMap LambdaCalculus.freevars toSet) -- builtin) map TypedTerm.raw)

    val codeX = codegen.pred(quadrant, "X")//, sized=false)
    println(codeX toPretty)

    /* Sketch file generation */
    val sketch = new SketchOutput

    val outf = Sketch.benchmarkNext
    val outfw = new FileWriter(outf)
    def fprintln(s: String) = outfw.write(s + "\n");

    scopegen() foreach (pre => fprintln(sketch(pre)))
    
    fprintln(s"""include "scalar.skh";\ninclude "scope.sk";\n\n""")
    fprintln(sketch(code0))
    code1 foreach (code1 => fprintln(sketch(code1)))

    /* @@@ this part is the hackiest @@@ */
    {
      for ((_, i) <- code1.zipWithIndex)
        fprintln(s"""@Param("selected: $i") int _${i}_(int n) { return n; }""")
      fprintln("generator int nparams() { return 3; }");

      val alts = code1.zipWithIndex map { case (_, i) => s"f_$i(_${i}_(n), Context_JJR, theta, i, j)" }

      fprintln(s"generator |scalar| f_i(int n, fun theta, int i, int j) { return {| ${alts mkString " | "} |}; }")
    }

    fprintln("\n" + sketch(codeX) + "\n")

    fprintln("\n/* -- harness -- */\n")
    fprintln(sketch.harness(decl))

    outfw.close()

    new Sketch(outf)
  }


  class CodeGen(implicit scope: Scope) {

    import TypedTerm.{preserve, typeOf_!}
    import LambdaCalculus.{isApp, isAbs}
    import TypePrimitives.{args=>targs,ret=>tret,shape}
    import semantics.TypeTranslation.TypingSugar.qvars
    import TraceableException.trace
    import synth.pods.ConsPod.`⟨ ⟩?`
    import CodeGen._

    case class Context(vars: List[Term], innerFuncs: ListMap[Identifier, (List[Term], Term)])

    object Context {
      def empty = Context(List(), ListMap.empty)
    }

    def apply(t: Term, sized: Boolean=true) = {
      implicit val ctx = Context.empty
      trace(t) { toplevel(expr(t), sized) }
    }

    def apply(t: Term, name: String): Term = apply(t, name, true)
    def apply(t: Term, name: String, sized: Boolean): Term = rename(apply(t, sized), name)

    def expr(t: Term)(implicit ctx: Context): Term = {
      if (t.isLeaf) {
        if (!typeOf_!(t).isLeaf || (ctx.vars contains t) || t.root.literal.isInstanceOf[Int]) t
        else TypedTerm(t, scalar)
      }
      else if (t =~ ("|!", 2)) {
        val v = expr(t.subtrees(0))
        val cond = expr(t.subtrees(1))
        TypedTerm((if (typeOf_!(v) == scalar) only else when)(cond, v), scalar)
      }
      else if (t =~ (":", 2)) expr(t.subtrees(1))
      else if (t =~ ("/", 2)) {
        assert(typeOf_!(t).isLeaf)
        TypedTerm(slash(t.subtrees map expr), scalar)
      }
      else if (t.root.kind == "connective") TypedTerm(T(t.root, t.subtrees map expr), B)
      else if (t.root.kind == "set" || t.root.kind == "variable") app(TypedTerm(T(t.root), B), t.subtrees) /* assume it's a predicate */
      else isApp(t) match {
        case Some((f, args)) =>
          if (!typeOf_!(t).isLeaf) throw new TranslationError(s"high-order return value for '${f}'") at t
          val ff = expr(f)
          if (args exists (`⟨ ⟩?`(_).isDefined)) reduction(ff, args)
          else app(ff, args)
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
      val retval = tret(typeOf_!(f))
      if (vals forall (x => typeOf_!(x) != scalar)) {
        //if (f.root == "-") TypedTerm(f(vals), tret(typeOf_!(f)))
        TypedTerm(f(vals), scalar)
      }
      else
        TypedTerm(@:(f)(vals map (x => if (typeOf_!(x) == scalar) x else some(x))),
          if (retval == B) retval else scalar)
    }

    def abs(vars: List[Term], body: Term)(implicit ctx: Context) = {
      val subctx = Context(ctx.vars ++ vars, ListMap.empty)
      val defn = expr(body)(subctx)
      val retType = typeOf_!(body)
      val f = TypedIdentifier($I("f", "function"), if (retType.isLeaf && retType != Prelude.B) scalar else retType)
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

    def decl(vars: List[Term]) = vars map { va =>
      val typ = shape(typeOf_!(va))(new Scope)  // scope is irrelevant
      val args = targs(typ)
      if (args.isEmpty)
        def_(va)
      else {
        val vars = qvars(args, Strip.lower)
        val retval = tret(typ)
        if (retval == Prelude.B)
          def_(TypedTerm(va, retval), `()`(vars))
        else {
          val (f_val, f_supp) = ($TV(s"${va.root.literal}_val"),$TV(s"${va.root.literal}_supp"))
          `;`(
            def_(TypedTerm(f_val, retval), `()`(vars)),
            def_(TypedTerm(f_supp, Prelude.B), `()`(vars)),
            def_(TypedTerm(va, scalar), `()`(vars), ret(when(f_supp(vars), f_val(vars))))
          )
        }
      }
    }

    def pred(typ: Term) = {
      val args = TypingSugar.qvars(targs(shape(typ)), Strip.lower)
      val body = TypedTerm(&&(TypeTranslation.checks(scope, typ, args)), Prelude.B)

      apply(TI("↦")(args)(body)>>, sized=false)
    }

    def pred(typ: Term, name: String): Term = rename(pred(typ), name)

    def rename(defTerm: Term, name: String) = defTerm match {
      case T(def_.root, f :: xs) => def_(preserve(f, TI(name)) :: xs)
      case _ => throw new TranslationError("not a def() term") at defTerm
    }

    def emit(t: Term)(implicit ctx: Context) = {
      val defns = ctx.innerFuncs map defn
      if (defns.isEmpty) ret(t)
      else `;`(defns toList)(ret(t))
    }

    def toplevel(t: Term, sized: Boolean)(implicit ctx: Context) = {
      if (!(t.isLeaf && ctx.innerFuncs.size == 1 && ctx.innerFuncs.contains(t.root)))
        throw new TranslationError("top-level expression must be a function") at t
      val n = TypedTerm(TV("n"), Prelude.N)
      val sz = if (sized) Some(n) else None
      ctx.innerFuncs.head match { case (f, (vars, body)) => defn(T(f), sz ++: vars, body) }
    }
  }

  object CodeGen {
    val scalar = TS("scalar")
    val void = TS("void")
    val some = TI("some")
    val when = TI("when")
    val only = TI("only")
    val slash = TI("slash")
    val def_ = TI("def")
    val `()` = TI("()")
    val `;` = TI(";")
    val ret = TI("ret")

    def codegen(t: Term)(implicit scope: Scope) = new CodeGen apply t
  }
  
  
  class ScopeGen(scope: Scope) {
    import ScopeGen._
    import CodeGen._
    import Domains.{⊤,isEmptySort}
    
    val masters = scope.sorts.masters filterNot isBuiltinSort 
    val sorts =  (scope.sorts.hierarchy.bfs map (_.root) filterNot   /* notice BFS order */
                  (s => s == ⊤ || isEmptySort(s) || isBuiltinSort(s)) toList) 
    val sortsByMaster = sorts groupBy scope.sorts.getMasterOf
    val leaves = scope.sorts.leaves filterNot isBuiltinSort toList
    val leavesByMaster = leaves.toList groupBy scope.sorts.getMasterOf

    val partitions = scope.sorts.hierarchy.nodes collect {
      case T(sup, List(sub1, sub2)) => (sup, sub1.root, sub2.root)
    }
    
    def apply() = {
      (sorts map decl) ++
      List(sortsSelector("Scope_subsort", sorts.toList.reverse, List()), //List((i) => TI("+")(i, TI(1)), (i) => TI("-")(i, TI(1)))),
           sortsSelector("Scope_leaf", leaves, List()),
           facts("Scope_facts"),
           def_(TypedTerm(TV("N"), N), TI(0)),  /* must be initialized by harness */
           def_(TypedTerm(TV("W"), N), TI(leaves.length)))
    }
    
    def isBuiltinSort(sort: Identifier) = List(N, R, B) exists (_.root == sort)
    
    def nonnegative(i: Int) = if (i >= 0) Some(i) else None
    def nonnegative_!(i: Int) = assume(i >= 0)
    
    def decl(sort: Identifier) = {
      val i = TyTV("i", N)

      val master = scope.sorts.getMasterOf(sort)
      val parts = leavesByMaster(master)
      val masterIdx = masters.indexOf(master) |-- nonnegative_!
      val leafIdx = leaves.indexOf(sort) |> nonnegative
      val partIdx = parts.indexOf(sort) |> nonnegative
      
      val head = def_(TypedTerm(T(sort), B), `()`(i))
      val body = if (scope.sorts.isMaster(sort)) TI(1)
        else partIdx match {
          case Some(idx) => &&(
            ((idx > 0)               -->  TI("≥")(i, d(TI(masterIdx), TI(idx))))  ++
            ((idx < parts.length-1)  -->  TI("<")(i, d(TI(masterIdx), TI(idx+1)))) ++
            ((idx == parts.length-1) -->  TI("<")(i, sizeCutoffExpr))
          )
          case _ => scope.sorts.findSortHie(sort) match {
            case Some(hie) => ||(hie.subtrees map (_.root) map (T(_)(i)))
            case None => void
          }
        }
      
      val fundef = head(ret(body))

      `@_`(TI("Sort")(`""`(T(sort))), leafIdx match {
        case Some(idx) => `@_`(TI("Leaf")(`""`(TI(idx))), fundef)
        case _ => fundef
      })
    }
    
    def sortsSelector(name: String, sorts: Iterable[Identifier], shiftops: List[Term => Term]) = {
      val i = TypedTerm(TI("i"), N)
      val b = TypedTerm(TI("b"), `[]`(B, TI(shiftops.length)))   // |shiftop| bits
      val params = (if (shiftops.nonEmpty) List(b) else List()) ++ List(i)
      def `b[]`(idx: Int) = `[]`(b, TI(idx))
      def offset(sort: Identifier, op: Term=>Term) = TypedTerm(@:(T(sort), TypedTerm(op(i), N)), B)
      def offsets(sort: Identifier) = shiftops.zipWithIndex map { case (op, idx) => `b[]`(idx) & offset(sort, op) }
      selector(name, params, sorts map (sort => TypedTerm(||(T(sort)(i) +: offsets(sort)), B)))
    }
    
    def selector(name: String, params: List[Term], exprs: Iterable[Term]) = {
      val rettype = typeOf_!(exprs.head)
      /**/ assume(exprs forall (typeOf_!(_) == rettype)) /**/
      val fid = TypedTerm(TI(name), rettype) 
      val ι = TypedTerm(TI("ι"), N)
      val body = (exprs.zipWithIndex :\ assert_(FALSE)) { 
        case ((head, idx), tail) => if_(ι =:= TI(idx), ret(head), tail) 
      }
      generator(def_(fid, `()`(ι +: params), body))
    }
    
    def facts(name: String): Term = {
      val i = TyTV("i", N)
      val j = TyTV("j", N)
      val < = TV("<")
      facts(name, partitions map {
        case (sup, sub1, sub2) =>
          new Template( List(i.leaf), T(sup)(i) =:= (T(sub1)(i) | T(sub2)(i)) )
      } toList, partitions map {
        case (sup, sub1, sub2) =>
          new Template( List(i.leaf, j.leaf), TypedTerm((T(sub1)(i) & T(sub2)(j)) -> <(i, j), B) )
      } toList)
    }
    
    def facts(name: String, unary: List[Scheme], binary: List[Scheme]) = {
      val n = TyTV("n", N)
      val p = TyTV("p", N)
      val q = TyTV("q", N)
      val assumeUnary = unary map (s => assume_(s(p)))
      val assumeBinary = binary map (s => assume_(s(p, q)))
      generator(
          def_(TypedTerm(TI(name), N), `()`(n),
              ret(sizeCutoffExpr)
              /*
              `;`(
                  for_(p, `()`(TI(0), n), `;`(assumeUnary :+
                      for_(q, `()`(TI(0), n), `;`(assumeBinary) ))
                  ),
                  ret(n)
              )
              */
          )
      )
    }
    
    def sizeCutoffExpr = {
      val max2i = TyTV("max2i", N ->: N ->: N)
      (leavesByMaster map {
        case (master, leaves) => d(TypedTerm(TI(masters.indexOf(master)), N), TypedTerm(TI(leaves.length), N))
      }
      reduce (max2i(_, _)))
    }
  }
  
  object ScopeGen {
    val if_ = TI("if")
    val for_ = TI("for")
    val assert_ = TI("assert")
    val assume_ = TI("assume")
    val generator = TI("generator")
    val `@_` = TI("@_")
    val `""` = TI("\"\"")
    val `[]` = TI("[]")
    val -> = TI("->")
    
    val d = $TyTV("d", N ->: N ->: N)
    
    implicit class -->(private val cond: Boolean) extends AnyVal {
      def -->[A](a: A) = if (cond) List(a) else List.empty
    }
  }



  class SketchOutput {

    import CodeGen._
    import ScopeGen._
    import TypedTerm.typeOf_!

    val mnemonics = new Mnemonics {
      override def isIdentifierPart(c: Character) = c < 0x100 && super.isIdentifierPart(c)
    }

    mnemonics.reserve(ScopeGen.d ~> "d")
    
    def mne(id: Identifier) = mnemonics.get(id)
    def mne(t: Term) = mnemonics.get(t.leaf)

    def suf(code: Term, f: Term, args: List[Term]) =
      (if (typeOf_!(code) == B) "b" else "") + args.length
        
    def apply(code: Term): String = code match {
      case T(def_.root, List(f, T(`()`.root, params))) =>                                    // type f(params);
        try s"${typ(typeOf_!(f))} ${mne(f)}(${params map param mkString ", "});"
        finally mnemonics release (params map (_.leaf))
      case T(def_.root, List(f, T(`()`.root, params), body@T(ret.root, List(_)))) =>         // type f(params) { return expr; }
        try s"${typ(typeOf_!(f))} ${mne(f)}(${params map param mkString ", "}) { ${apply(body)} }"
        finally mnemonics release (params map (_.leaf))
      case T(def_.root, List(f, T(`()`.root, params), body)) =>                              // type f(params) {↵ -block- ↵}
        try s"${typ(typeOf_!(f))} ${mne(f)}(${params map param mkString ", "}) {\n${indent(apply(body))}\n}"
        finally mnemonics release (params map (_.leaf))
      case T(def_.root, List(v, init)) =>                                                    // type v = init;
        s"${typ(typeOf_!(v))} ${mne(v)} = ${apply(init)};"
      case T(`;`.root, stmts) => stmts map apply mkString "\n"
      case T(@:.root, f :: args) => s"apply${suf(code, f, args)}(${mne(f)}, ${args map apply mkString ", "})"
      case T(ret.root, List(r)) => s"return ${apply(r)};"
      case T(if_.root, List(cond, th)) => s"if (${apply(cond)}) ${apply(th)}"
      case T(if_.root, List(cond, th, el)) => s"if (${apply(cond)}) ${apply(th)}\nelse ${apply(el)}"
      case T(for_.root, List(va, T(`()`.root, List(from, to)), stmt)) =>
        try s"for (${typ(typeOf_!(va))} ${mne(va)} = ${apply(from)}; ${mne(va)} < ${apply(to)}; ${mne(va)}++) {\n${indent(apply(stmt))}\n}"
        finally mnemonics release List(va.leaf)
      case T(assert_.root, List(prop)) => s"assert(${apply(prop)});"
      case T(assume_.root, List(prop)) => s"assume(${apply(prop)});"
      case T(generator.root, List(defn)) => s"generator ${apply(defn)}"
      case T(IntConst(n), Nil) => s"$n"
      case T(v, Nil) => s"${mne(v)}"
      case T(InfixOp(op), List(a, b)) => s"(${apply(a)} $op ${apply(b)})"
      case T(PrefixOp(op), List(a)) => s"($op${apply(a)})"
      case T(Reduction(f), args) => args match {
          case List(T(fn, Nil)) => s"$f(n, ${mne(fn)})"
          case List(T(`f`, List(T(fn, Nil))), b) => s"${f}_acc(${apply(b)}, n, ${mne(fn)})"  // this is an
          case List(a, T(`f`, List(T(fn, Nil)))) => s"${f}_acc(${apply(a)}, n, ${mne(fn)})"  // optimization
          case List(a, b) => s"${f}2(${apply(a)}, ${apply(b)})"
          case _ => throw new TranslationError(s"invalid usage of 'min'") at code
        }
      case T(`@_`.root, List(annotation, decl)) => s"@${apply(annotation)} ${apply(decl)}"
      case T(`""`.root, List(string)) => "\"" + string.leaf.literal.toString + "\""
      case T(`[]`.root, List(arr,  idx)) => s"${apply(arr)}[${apply(idx)}]"
      case T(`->`.root, List(a, b)) => apply(~(a) | b)
      case T(f, args) => s"${mne(f)}(${args map apply mkString ", "})"
    }

    def harness(decl: Iterable[Term]) = {
      val (prologue, proto) = decl partition { case T(def_.root, List(v)) => false case _ => true }
      //val main = def_(TypedTerm($TV("main"), $TV("void")), `()`(proto flatMap (_.subtrees) toList))
      s"""${prologue map apply mkString "\n\n"}\n\ninclude "harness.sk";\n"""
    }

    val INFIX = Map(I("=") -> "==", I("<") -> "<", I(">") -> ">", I("≥") -> ">=", I("≤") -> "<=", 
                    I("∧") -> "&&", I("∨") -> "||")
    val PREFIX = Map(I("¬") -> "!")

    object InfixOp { def unapply(id: Identifier) = INFIX get id }
    object PrefixOp { def unapply(id: Identifier) = PREFIX get id }
    object IntConst { def unapply(id: Identifier) = id.literal match { case x: Int => Some(x) case _ => None } }

    val REDUCT = Set(Prelude.min.root, Prelude.max.root)

    object Reduction { def unapply(id: Identifier) = if (REDUCT contains id) Some(id) else None }

    def typ(typ: Term): String =
      if (typ == scalar) "|scalar|"
      else if (typ == Prelude.B) "bit"
      else if (typ == void) "void"
      else if (typ.root == `[]`.root) s"${this.typ(typ.subtrees.head)}[${typ.subtrees.tail map apply mkString ","}]"
      else if (typ.isLeaf) "int"
      else "fun"

    def param(t: Term) = s"${typ(typeOf_!(t))} ${mne(t)}"

    def indent(block: String) = block split "\n" map ("    " + _) mkString "\n"
  }


  class ReadSketchResults(implicit scope: Scope) {

    val re = raw"/\* \{(.*?): (.*?)\} \*/".r

    def apply(reader: BufferedReader): Map[String, Term] = apply(ui.CLI.getLines(reader))
    def apply(lines: Stream[String]) =
      {
        for (line <- tee(lines);
             mo <- re.findPrefixMatchOf(line))
          yield (mo.group(1), mo.group(2) |> parse |> conj)
      } toMap

    def tee(lines: Stream[String]) = lines map { x => println(x) ; x }

    def parse(s: String) = JSON.parse(s) |> parseJson

    import Domains._
    
    def parseJson(json: Any): Any = json match {
      case +~+(Array(s,p)) => I(p, "predicate") :<: scope.sorts.getMasterOf(I(s))
      case s: String => scope.sorts.findSortHie(I(s)) match
                        { case Some(h) => h.root case _ => V(s); }
      case i: Int => I(i)
      case l: BasicDBList => l.toList map parseJson
    }
    
    // - just some string matching sugar
    object +~+ { def unapply(o: Any) = o match { 
      case p: String if p.contains('~') => Some(p.split("~", 2))
      case _ => None
    } }

    /* parse components */
    private def conj(o: Any): Term = o match {
      case Nil => TRUE  /* empty conjunction? */
      case l :: ps => (disj(l) /: ps)((l,p) => l map (_ ∩ atom(p))) match {
        case List(one) => one
        case many => ConsPod.`⟨ ⟩`(many)
      }
      case id: Identifier => T(id)
    }
    private def disj(o: Any): List[Term] = o match {
      case l: List[_] => l map atom
      case id: Identifier => List(T(id))
    }
    private def atom(o: Any): Term = o match {
      case Nil => T(Domains.⊥)
      case l: List[_] => (l map atom) reduce (_ x _)
      case pred: Domains.Extends => T(pred.sup) ∩ T(pred.sub)
      case id: Identifier => T(id)
    }
  }
}

