package semantics.smt

import com.microsoft.z3.BoolExpr
import syntax.Piping._
import java.io.File

/**
 * A hack for running CVC4 instead of Z3.
 * It uses the Z3 API, then instead of running the solver, it creates
 * a benchmark file and runs "cvc4 ..." on it.
 */
class CVC4Gate(implicit guidelines: SmtGuidelines=SmtGuidelines.default) extends Z3Gate {

  import Z3Gate._

  val flags = if (guidelines.fullSaturate) Seq("--full-saturate-quant") else Seq()
  
  def cmdline(smt2f: File) = Seq("cvc4") ++ flags ++ Seq(smt2f.getPath)
  
  override def solve(assumptions: List[BoolExpr], goals: List[BoolExpr], verbose: Boolean=false) = {
    if (verbose) for (a <- assumptions) println(s" * $a")

    save(assumptions, goals) map { case (goal, smt2f) =>
      import scala.sys.process._
      if (verbose) { println("-" * 80); println(s" ? $goal") }
      cmdline(smt2f).!! |> ProverStatus.fromResult
    } toList
  }

  override def solve(assumptions: List[BoolExpr], goals: Iterable[Sequent]) = {
    save(assumptions, goals) map { case (_, smt2f) =>
      import scala.sys.process._
      cmdline(smt2f).!! |> ProverStatus.fromResult
    } toList
  }

}



class NullSmtGate extends Z3Gate {

  import Z3Gate._

  val MSG = " - - - -    cold is the void    - - - -"
  
  override def solve(assumptions: List[BoolExpr], goals: List[BoolExpr], verbose: Boolean=false) = {
    println(MSG)
    
    if (verbose) for (a <- assumptions) println(s" * $a")

    save(assumptions, goals) map { case (goal, smt2f) =>
      import scala.sys.process._
      if (verbose) { println("-" * 80); println(s" ? $goal") }
      ProverStatus.VALID
    } toList
  }

  override def solve(assumptions: List[BoolExpr], goals: Iterable[Sequent]) = {
    println(MSG)
    
    save(assumptions, goals) map { case (_, smt2f) =>
      import scala.sys.process._
      ProverStatus.VALID
    } toList
  }

}
