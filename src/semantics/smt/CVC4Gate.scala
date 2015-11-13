package semantics.smt

import com.microsoft.z3.BoolExpr

import syntax.Piping._

/**
 * A hack for running CVC4 instead of Z3.
 * It uses the Z3 API, then instead of running the solver, it creates
 * a benchmark file and runs "cvc4 ..." on it.
 */
class CVC4Gate extends Z3Gate {

  import Z3Gate._

  override def solve(assumptions: List[BoolExpr], goals: List[BoolExpr], verbose: Boolean=false) = {
    if (verbose) for (a <- assumptions) println(s" * $a")

    save(assumptions, goals) map { case (goal, smt2f) =>
      import scala.sys.process._
      if (verbose) { println("-" * 80); println(s" ? $goal") }
      Seq("cvc4", smt2f.getPath).!! |> ProverStatus.fromResult
    } toList
  }

  override def solve(assumptions: List[BoolExpr], goals: Iterable[Sequent]) = {
    save(assumptions, goals) map { case (_, smt2f) =>
      import scala.sys.process._
      Seq("cvc4", smt2f.getPath).!! |> ProverStatus.fromResult
    } toList
  }

}
