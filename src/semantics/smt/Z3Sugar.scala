package semantics.smt

import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Symbol
import com.microsoft.z3.Quantifier
import com.microsoft.z3.Sort
import com.microsoft.z3.FuncDecl
import com.microsoft.z3.Solver
import com.microsoft.z3.Status
import com.microsoft.z3.ArithExpr
import com.microsoft.z3.Z3Exception



/**
 * Provides some syntactic sugar for Z3 formulas embedded in Scala code
 * (like a mini-internal-DSL)
 */
object Z3Sugar {

  val ctx = new Context  // main context

  def !!(e: Expr) = try e.asInstanceOf[BoolExpr]
    catch { case _: ClassCastException => throw new Z3Exception(s"expected BoolExpr, found '$e'") }

  implicit class LogicalConnectives(private val e: Expr) extends AnyVal {
    def |(other: Expr) = ctx mkOr (!!(e), !!(other))
    def &(other: Expr) = ctx mkAnd (!!(e), !!(other))
    def ->(other: Expr) = ctx mkImplies (!!(e), !!(other))
    def ->:(other: Expr) = other -> e
    def <->(other: Expr) = ctx mkIff (!!(e), !!(other))
    def =:=(other: Expr) = ctx mkEq (e, other)
    def unary_~ = ctx mkNot (!!(e))
  }
  
  implicit class Arith(private val e: Expr) extends AnyVal {
    def unary_+ = e.asInstanceOf[ArithExpr]
    def +(other: Expr) = ctx mkAdd (+e, +other)
  }

  implicit class ArrowMulti[A](private val self: A) extends AnyVal {
    def :->[B](s: B*) = (self, s)
  }
  
  implicit def mkSymbol(name: String): Symbol = ctx mkSymbol name
  implicit def mkSymbol[T](name: (String,T)): (Symbol,T) = (ctx mkSymbol name._1, name._2)
  
  def forall(i: Seq[Expr], body: Expr) = ctx mkForall (i.toArray, body, 0, null, null, null, null)
  def forall(vars: Expr*): (Expr => Quantifier) = (body: Expr) => forall(vars, body)
  def ∀(vars: Expr*) = forall(vars:_*)
  
  def conjunction(conjuncts: Expr*) = ctx mkAnd ((conjuncts map !!):_*)
  def disjunction(disjuncts: Expr*) = ctx mkOr((disjuncts map !!):_*)
  
  def const(name: Symbol, sort: Sort) = ctx mkConst (name, sort)
  def const(namesort: (Symbol, Sort)) = ctx mkConst (namesort._1, namesort._2)
  def func(name: Symbol, sorts: Sort*) =
    ctx mkFuncDecl (name, sorts.slice(0, sorts.length - 1).toArray[Sort], sorts.last)

  def func(namesorts: (Symbol, Seq[Sort])): FuncDecl = func(namesorts._1, namesorts._2:_*)

  
  // -----------
  // Solver part
  // -----------

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
  }
  
  import ProverStatus._

  def solve(assumptions: List[BoolExpr], goals: List[BoolExpr]) = {
    val s = ctx mkSolver()
    assumptions foreach (s.add(_))
    goals map (check(s, _))
  }
  
  def solveAndPrint(assumptions: List[BoolExpr], goals: List[BoolExpr]) = {
    val s = ctx mkSolver()
    
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
}
