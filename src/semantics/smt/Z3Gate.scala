
package semantics.smt

import java.io.File
import java.util.regex.Pattern
import scala.collection.mutable.HashMap
import scala.util.Either

import com.microsoft.z3.Expr
import com.microsoft.z3.Sort
import com.microsoft.z3.FuncDecl
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Z3Exception
import com.microsoft.z3.Status
import com.microsoft.z3.Solver

import syntax.Identifier
import syntax.AstSugar
import syntax.transform.Mnemonics
import syntax.Piping._
import semantics.TypedIdentifier



class Z3Gate {
  
  import AstSugar._
  import Z3Sugar._
  
  val declarations = new HashMap[Identifier, Either[FuncDecl,Expr]]
  val sorts = new HashMap[Identifier, Sort]
  
  val mnemonics = new Mnemonics
  
  /* some built-in declarations */
  sorts += (//S("R") -> ctx.getRealSort,
            //S("N") -> ctx.getIntSort,
            S("") -> ctx.getBoolSort)
  
  declarations += (I(true) -> Right(ctx mkBool true),
                   I(false) -> Right(ctx mkBool false))
  
  // -----------------
  // Declarations part
  // -----------------
  
  def getSort(sort: Identifier) = sorts getOrElse (sort, {
    val newSort = ctx mkUninterpretedSort sort.toString
    sorts += (sort -> newSort)
    newSort
  })
  
  def getSorts(typ: Term): List[Sort] =
    if (typ.isLeaf) List(getSort(typ.root))
    else if (typ.root == "->") {
      val sorts = typ.unfold.subtrees
      if (sorts forall (_.isLeaf)) sorts map (x => getSort(x.root))
      else throw new SmtNotFirstOrder(s"not first-order: type '${typ.toPretty}'")
    }
    else throw new SmtException(s"cannot handle type '${typ.toPretty}'")
  
  def declare(symbol: TypedIdentifier): Either[FuncDecl, Expr] = declare(symbol.untype, symbol.typ)
  
  def declare(symbol: Identifier, typ: Term) = declarations get symbol match {
    case Some(decl) => 
      val existingType = typeOf(decl)
      if (existingType == typ) decl
      else
        throw new SmtException(s"multiply declared symbol '$symbol' " +
          s"(conflicting types: ${existingType.toPretty}  ~  ${typ.toPretty})")
    case _ => 
      val decl = Left(func (mne(symbol) :-> (getSorts(typ):_*)))
      declarations += symbol -> decl
      decl
  }
  
  def typeOf(d: Either[FuncDecl, Expr]): Term = d match {
    case Left(f) => typeOf(f)
    case Right(e) => typeOf(e)
  }
  
  def typeOf(e: Expr): Term = typeOf(e.getSort)
  
  def typeOf(f: FuncDecl): Term =
    TI("->", f.getDomain.toList map typeOf)(typeOf(f.getRange)).foldRight
  
  
  def typeOf(sort: Sort): Term = sorts find (_._2 == sort) match {
    case Some((k,_)) => T(k)
    case _ => T(S(sort.toString))
  }
  
  /**
   * Gets a string mnemonic for this identifier; makes sure distinct
   * identifiers get distinct mnemonics (even if they have the same
   * literal).
   */
  def mne(id: Identifier) = mnemonics get id

  // ---------------
  // Assertions part
  // ---------------

  implicit class App(private val d: Either[FuncDecl, Expr])  {
    def apply(args: Expr*) = d match {
      case Left(f) => f(args:_*)
      case Right(e) =>
        if (args.nonEmpty) throw new SmtException(s"non-function $e used with ${args.length} arguments")
        else e
    }
  }
  
  def expression(expr: Term): Expr = {
    val r = expr.root
    val arity = expr.subtrees.length
    def recurse = expr.subtrees map expression
    if (r == "forall" || r == "∀") {
      val (vas :+ body) = expr.unfoldRight.subtrees
      val vas_decl = vas map quantifiedVar 
      fork(vas map (_.root)) {
        forall(vas_decl:_*)(expression(body))
      }
    }
    else if ((r == "->" || r == "→") && arity == 2) {
      val List(l, r) = recurse
      l -> r
    }
    else if (r == "&" || r == "∧") 
      conjunction(recurse:_*) 
    else if (r == "|" || r == "∨") 
      disjunction(recurse:_*)
    else if ((r == "<->" || r == "↔︎") && arity == 2) {
      val List(l, r) = recurse
      l <-> r
    }
    else if ((r == "~" || r == "¬") && arity == 1)
      ~(recurse(0))
    else if ((r == "=") && arity == 2) {
      val List(l, r) = recurse
      l =:= r
    }
    else {
      declarations get r match {
        case Some(decl) => decl(recurse:_*)
        case _ => r match {
          case rt: TypedIdentifier => declare(rt)(recurse:_*)
          case _=> throw new SmtException(s"undeclared '$r' ($arity-ary ${r.kind})")
        }
      }
    }
  }
  
  def formula(term: Term) = try !! ( expression(term) )
    catch { 
      case x: SmtException => throw x.at(term)
      case z: Z3Exception => throw new SmtException(z.toString()).at(term)
    }
  
  def quantifiedVar(va: Term) = (va.isLeaf, va.root) match {
    case (true, tid@TypedIdentifier(_, typ)) =>
      if (typ.isLeaf) declare(tid)() 
      else throw new SmtNotFirstOrder(s"high-order quantification: '${va.toPretty}'")
    case _ =>
      throw new SmtException(s"not a valid variable: '${va.toPretty}'")
  }
  
  def fork[R](retract: Iterable[Identifier])(op: => R) = {
    def rollback = { declarations --= retract ; mnemonics --= retract }
    try op
    finally rollback
  }

  // -----------
  // Solver part
  // -----------

  def solve(assumptions: List[BoolExpr], goals: List[BoolExpr], verbose: Boolean=false) =
    if (verbose)
      Z3Gate.solveAndPrint(assumptions, goals)
    else      
      Z3Gate.solve(assumptions, goals)
      
  def solveAndPrint(assumptions: List[BoolExpr], goals: List[BoolExpr]) = solve(assumptions, goals, true)
  
  def solve(assumptions: List[BoolExpr], goal: Iterable[Z3Gate.Sequent]) = Z3Gate.solve(assumptions, goal)
}


object Z3Gate {
  
  import Z3Sugar._

  // -----------
  // Solver part
  // -----------

  import Z3Sugar.ctx
  
  def mkSolver = {
    val s = ctx mkSolver()
    val p = ctx mkParams()
    //p.add("soft_timeout", 1000)
    //p.add("smt.macro_finder", true)
    s.setParameters(p)
    s
  }
  
  object ProverStatus extends Enumeration {
    type ProverStatus = Value
    val VALID, INVALID, UNKNOWN = Value

    def fromStatus(status: Status) = status match {
      case Status.UNSATISFIABLE => VALID
      case Status.SATISFIABLE => INVALID
      case Status.UNKNOWN => UNKNOWN
    }

    def fromResult(status: String) = status.trim match {
      case "unsat" => VALID
      case "sat" => INVALID
      case _ => UNKNOWN
    }
    
    def toPretty(status: Value) = status.toString.toLowerCase
    
    implicit class Pretty(v: Value) {
      def toPretty = v.toString.toLowerCase
    }
  }
  
  import ProverStatus._

  case class Sequent(negative: List[BoolExpr], positive: BoolExpr)
  
  def solve(assumptions: List[BoolExpr], goals: List[BoolExpr]) = {
    val s = mkSolver
    save(assumptions, goals)
    assumptions foreach (s.add(_))
    goals map (checkAndPrint(s, _))
  }
  
  def solveAndPrint(assumptions: List[BoolExpr], goals: List[BoolExpr]) = {
    val s = mkSolver
    
    for (a <- assumptions) {
      println(s" * $a")
      s add a
    }
      
    for (g <- goals) yield {
      println("-" * 80)
      println(s" ? $g")
      checkAndPrint(s, g)
    }
  }

  def solve(assumptions: List[BoolExpr], goals: Iterable[Sequent])(implicit d: DummyImplicit)  = {
    val s = mkSolver
    save(assumptions, goals)
    assumptions foreach (s.add(_))
    goals map (check(s, _))
  }
    
  def check(s: Solver, goal: BoolExpr) = {
    s.push
    s add ~goal
    try ProverStatus.fromStatus(s.check)
    finally s.pop
  }
  
  def checkAndPrint(s: Solver, goal: BoolExpr): ProverStatus = {
    s.push
    s add ~goal
    try checkAndPrint(s)
    finally s.pop
  }

  def check(s: Solver, goal: Sequent) = {
    s.push
    goal.negative foreach (s add _)
    s add ~goal.positive
    try ProverStatus.fromStatus(s.check)
    finally s.pop
  }
  
  def checkAndPrint(s: Solver, goal: Sequent): ProverStatus = {
    s.push
    goal.negative foreach (s add _)
    s add ~goal.positive
    try checkAndPrint(s)
    finally s.pop
  }

  def checkAndPrint(s: Solver): ProverStatus = {
    val status = s.check
    status match {
      case Status.UNSATISFIABLE => 
        println("valid")
        ProverStatus.VALID
      case Status.SATISFIABLE =>
        println("invalid")
        println(s.getModel)
        ProverStatus.INVALID
      case Status.UNKNOWN => 
        println(s"unknown (${s.getReasonUnknown})")
        ProverStatus.UNKNOWN
    }
  }
    
  // --------------
  // Benchmark Part
  // --------------
      
  var benchmarkCounter = 0
  def benchmarkNext(nparts: Int) = {
    0 until nparts map (i => new File(s"/tmp/benchmark$benchmarkCounter-$i.smt2"))
  } |-- { _ => benchmarkCounter += 1 }

  def zipWithBench[A](l: Iterable[A]) = l zip benchmarkNext(l.size)

  def save(assumptions: List[BoolExpr], goals: List[BoolExpr]) = {
    import java.io._
    zipWithBench(goals) |-- (_ foreach { case(goal, benchf) =>
      val f = new PrintWriter(benchf)
      f write ctx.benchmarkToSMTString("bellmania", "", "unknown", "", assumptions toArray, ~goal) |> standardize
      f.close()
    })
  }
  
  def save(assumptions: List[BoolExpr], goals: Iterable[Sequent])(implicit d: DummyImplicit) = {
    import java.io._
    zipWithBench(goals) |-- (_ foreach { case(goal, benchf) =>
      val f = new PrintWriter(benchf)
      f write ctx.benchmarkToSMTString("bellmania", "", "unknown", "", (assumptions ++ goal.negative) toArray, ~goal.positive) |> standardize
      f.close()
    })
  }
  
  def standardize(smt: String) = {
    def declare_sort(smt: String) = Pattern.compile(raw"\((declare-sort .*?)\)") matcher smt replaceAll "($1 0)"
    def implies(smt: String) = smt.replace("implies", "=>")  // TODO word boundaries
    smt |> declare_sort |> implies
  }
}


class SmtException(msg: String) extends Exception(msg) { 
  import syntax.AstSugar._
  
  var formula: Term = null;
  def at(formula: Term): SmtException = {
    this.formula = formula; this
  }
  
  override def getMessage = if (formula == null) super.getMessage 
    else s"$msg\n\tin: ${formula.toPretty}"
}
class SmtNotFirstOrder(msg: String) extends SmtException(msg) {}
