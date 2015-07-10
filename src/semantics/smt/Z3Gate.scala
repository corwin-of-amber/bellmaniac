
package semantics.smt

import java.util.regex.Pattern
import scala.collection.mutable.HashMap
import com.microsoft.z3.Expr
import com.microsoft.z3.Sort
import syntax.Identifier
import syntax.AstSugar
import com.microsoft.z3.FuncDecl
import semantics.TypeTranslation.TypedIdentifier
import semantics.TypeTranslation.TypedIdentifier
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Z3Exception
import scala.util.Either
import com.microsoft.z3.Status
import com.microsoft.z3.Solver



class Z3Gate {
  
  import AstSugar._
  import Z3Sugar._
  
  val declarations = new HashMap[Identifier, Either[FuncDecl,Expr]]
  val sorts = new HashMap[Identifier, Sort]
  
  val mnemonics = new HashMap[Identifier, String]
  
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
  def mne(id: Identifier) = mnemonics get id match {
    case Some(x) => x
    case _ =>
      val lit = normalizeLiteral(id)
      val newMne = (lit #:: (nat map (lit + _))) find (x => ! mnemonics.exists (_._2 == x))
      mnemonics += id -> newMne.get
      newMne.get
  }
  
  def normalizeLiteral(id: Identifier) = normalize(id.literal.toString)
  
  def normalize(s: String) =
    if (s == "<") "lt"
    else if (s == "+") "plus"
    else {
      val esc = s.replace("'", "_").replace(".", "_").replace("|", "!").replace("@", "apply")
      if (Character.isJavaIdentifierStart(esc.charAt(0))) esc else "_" + esc;
    }

  /**
   * just the stream of naturals (taken from Scala docs)
   */
  def nat = { 
    def loop(v: Int): Stream[Int] = v #:: loop(v + 1)
    loop(0)
  }

  // ---------------
  // Assertions part
  // ---------------

  import AstSugar.TreeBuild
  
  implicit class App(private val d: Either[FuncDecl, Expr])  {
    def apply(args: Expr*) = d match {
      case Left(f) => f(args:_*)
      case Right(e) =>
        if (args.length > 0) throw new SmtException(s"non-function $e used with ${args.length} arguments")
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
    p.add("smt.macro_finder", true)
    s.setParameters(p)
    s
  }
  
  object ProverStatus extends Enumeration {
    type ProverStatus = Value
    val VALID, INVALID, UNKNOWN = Value

    def fromStatus(status: Status) = {
      status match {
        case Status.UNSATISFIABLE => VALID 
        case Status.SATISFIABLE => INVALID
        case Status.UNKNOWN => UNKNOWN
      }
    }
    
    def toPretty(status: Value) = status.toString.toLowerCase
    
    implicit class Pretty(v: Value) {
      def toPretty = v.toString.toLowerCase
    }
  }
  
  import ProverStatus._

  case class Sequent(val negative: List[BoolExpr], val positive: BoolExpr)
  
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
      
  import syntax.Piping._

  var benchmarkCounter = 0;
  
  def save(assumptions: List[BoolExpr], goals: List[BoolExpr]) {
    import java.io._
    goals.zipWithIndex foreach { case(goal, i) =>
      val f = new PrintWriter(new File(s"/tmp/benchmark${benchmarkCounter}-${i}.txt"))
      f write ctx.benchmarkToSMTString("bellmania", "", "unknown", "", assumptions toArray, ~goal) |> standardize
      f close
    }
    benchmarkCounter = benchmarkCounter + 1
  }
  
  def save(assumptions: List[BoolExpr], goals: Iterable[Sequent])(implicit d: DummyImplicit)  {
    import java.io._
    goals.zipWithIndex foreach { case(goal, i) =>
      val f = new PrintWriter(new File(s"/tmp/benchmark${benchmarkCounter}-${i}.txt"))
      f write ctx.benchmarkToSMTString("bellmania", "", "unknown", "", (assumptions ++ goal.negative) toArray, ~goal.positive) |> standardize
      f close
    }
    benchmarkCounter = benchmarkCounter + 1
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
