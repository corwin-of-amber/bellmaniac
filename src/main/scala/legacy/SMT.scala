//private object UnsatException extends RuntimeException("inconsistent model")
//
//case class SolverException(msg: String) extends RuntimeException(msg)
//
//sealed trait Result
//case object Unsat extends Result
//case object Sat extends Result
//case object Unknown extends Result
//
///** SMT-LIB2 compliant solver. */
//trait Solver {
//  /** Issue a command and expect success. */
//  def command(s: String) {
//    //println("Z3: " + s)
//    >(s);
//    val reply = <();
//    if (reply != "success") {
//      println(s)
//      throw SolverException("unexpected reply: " + reply)
//    }
//  }
//  /** Check satisfiability. */
//  def check(): Result = {
//    >("(check-sat)");
//    val reply = <();
//    if (reply == "sat")
//      Sat
//    else if (reply == "unsat")
//      Unsat
//    else if (reply == "unknown")
//      Unknown
//    else
//      throw SolverException("unexpected reply: " + reply)
//  }
//  /** Evaluate the term in the current model. */
//  def eval(term: String): String = {>("(get-value (" + term + "))"); <<()}
//  /** Assert a boolean condition. */
//  def assert(s: String) = command("(assert " + s + ")")
//  /** Push a context */
//  def push() = command("(push)")
//  /** Pop a context */
//  def pop() = command("(pop)")
//  /** Reset the solver */
//  def reset() = command("(reset)")
//  /** Terminate the solver. */
//  def close()
//  /** Send to solver. */
//  protected def >(s: String)
//  /** Receive a line from the solver. */
//  protected def <(): String
//  /** Receive a term from the solver. */
//  def <<() = {
//    import scala.collection.mutable
//    val out = new mutable.ListBuffer[String]
//    var balance = 0;
//    do {
//      var line = <();
//      balance = balance + line.count(_ == '(') - line.count(_ == ')');
//      out += line;
//    } while (balance > 0)
//    out.toList.mkString;
//  }
//}
//
///** Log input and output of a solver. */
//trait Logging extends Solver {
//  abstract override def >(s: String) {Console.out.println("> " + s); super.>(s)}
//  abstract override def <() = {val s = super.<(); Console.out.println("< " + s); s}
//  abstract override def close() = {super.close(); Console.out.println(this + " closed")}
//}
//
///** Z3 version 3.2+. */
//class Z3 extends Solver {
//  import java.io._
//
//  // Requires version 4.3.2
//  private def BINARY = Option(System.getProperty("smt.home")) match {
//    case Some(path) => path
//    case None => System.getProperty("user.home") + "/opt/z3-4.3.2/bin/z3"
//  }
//
//  private def PARAMS ="-smt2" :: "-in" :: "-nw" :: Nil
//
//  private var process = {
//    val pb = new ProcessBuilder((BINARY :: PARAMS).toArray: _*);
//    pb.redirectErrorStream(true);
//    pb.start;
//  }
//
//  private var input = new BufferedWriter(new OutputStreamWriter(process.getOutputStream));
//  private var output = new BufferedReader(new InputStreamReader(process.getInputStream));
//
//  override def >(s: String) = {input.write(s); input.newLine; input.flush}
//  override def <() = output.readLine
//
//  command("(set-option :print-success true)")
//
//  // Disable MBQI
//  // See: http://stackoverflow.com/questions/17706219/defining-a-theory-of-sets-with-z3-smt-lib2
//  command("(set-option :smt.mbqi false)")
//  command("(set-option :auto-config false)")
//
//  // Remember solution values whenever possible
//  command("(set-option :produce-models true)")
//
//  override def close() {
//    input.close;
//    output.close;
//    process.destroy;
//  }
//}
//
//trait SMT extends Logger {
//  private var z3: Z3 = new Z3
//  z3.command("(declare-fun zero () Int)")
//  z3.command("(declare-fun plus (Int Int) Int)")
//  // substitute + for plus
//  //z3.command("(define-fun plus ((a Int) (b Int)) Int (+ a b))")
//
//  // zero for plus
//  z3.command("(assert (forall ((x Int)) (= (plus x zero) x)))")
//  z3.command("(assert (forall ((x Int)) (= (plus zero x) x)))")
//
//  // plus is commutative and associative
//  z3.command("(assert (forall ((x Int) (y Int)) (= (plus x y) (plus y x))))")
//  z3.command("(assert (forall ((x Int) (y Int) (z Int)) (= (plus x (plus y z)) (plus (plus x y) z))))")
//
//  // monoid
//  z3.command("(declare-sort M)")
//  z3.command("(declare-fun reduce (M) Int)")
//  z3.command("(declare-fun join (M M) M)")
//  z3.command("(declare-fun compr (Int Int) M)")
//
//  // push reduce down
//  z3.command("(assert (forall ((x M) (y M)) (= (reduce (join x y)) (plus (reduce x) (reduce y)))))")
//
//  // eliminate singleton
//  z3.command("(declare-fun singleton (Int) M)")
//  z3.command("(assert (forall ((x Int)) (= (reduce (singleton x)) x)))")
//
//  // eliminate empty comprehension
//  z3.command("(assert (forall ((x Int)) (= (reduce (compr x 0)) zero)))")
//
//  // special variables
//  private val iterator = Var("_i")
//  private val witness = (1 to 16).map(i => Var("_w" + i)).toList
//
//  // iterator
//  z3.command("(declare-fun " + iterator.name + " () Int)")
//
//  // equality witnesses
//  for (w <- witness)
//    z3.command("(declare-fun " + w.name + " () Int)")
//
//  assert(! prove(False) && prove(True), "over constraining check")
//
//  import collection.mutable.ListBuffer
//  import Transform.vars
//
//  def print(e: Expr)(implicit side: ListBuffer[String]): String = e match {
//    case Var(n, k) if k == 0 => n
//    // apply to variable witnesses
//    // assume parameters are 0-arity
//    case v: Funct  => print(App(v, (1 to v.arity).map(i => witness(i-1)).toList))
//    case Const(i) => if (i >= 0) i.toString else "(- " + (-i).toString + ")"
//    case Plus(l, r) => "(+ " + print(l) + " " + print(r) + ")"
//    case Minus(l, r) => "(- " + print(l) + " " + print(r) + ")"
//    case Times(l, r) => "(* " + print(l) + " " + print(r) + ")"
//    case Div(l, r) =>
//      // TODO: can't easily express n is a power of two
//      if (vars(l).isEmpty || ! vars(r).isEmpty)
//        error("can't assume divisibility of " + Div(l,r))
//      side += "(assert " + print((l mod r) === Const(0)) + ")"
//      "(div " + print(l) + " " + print(r) + ")"
//    case Mod(l, r) => "(mod " + print(l) + " " + print(r) + ")"
//    case Zero => "zero"
//    case Havoc =>
//      val v = Var.fresh()
//      side += "(declare-const " + v.name + " Int)"
//      print(v)
//    case Op(l, r) => "(plus " + print(l) + " " + print(r) + ")"
//    case Reduce(r) => "(reduce " + print(r) + ")"
//    case a: App => a.flatten match {
//      case App(Var(n, k), args) => "(" + n + " " + args.map(print(_)).mkString(" ") + ")"
//      case _ => ???
//    }
//    case Cond(cases, d) => cases match {
//      case (p, e) :: rest=> "(ite " + print(p) + " " + print(e) + "\n " + {
//        rest match {
//          case Nil => print(d)
//          case _ => print(Cond(rest, d))
//        }} + ")"
//      case _ => ???
//    }
//  }
//
//  def print(s: Seq)(implicit side: ListBuffer[String]): String = s match {
//    case Singleton(e) => "(singleton " + print(e) + ")"
//    case Join(l, r) => "(join " + print(l) + " " + print(r) + ")"
//    case Compr(e, v, Range(l, h)) => "(compr " +
//      print(e.s(List(v->(iterator+l)))) + " " + print(h-l) + ")"
//  }
//
//  def print(p: Pred)(implicit side: ListBuffer[String]): String = p match {
//    case True => "true"
//    case False => "false"
//    case And(l, r) => "(and " + print(l) + " " + print(r) + ")"
//    case Or(l, r) => "(or " + print(l) + " " + print(r) + ")"
//    case Not(l) => "(not " + print(l) + ")"
//    case Eq(l, r) => "(= " + print(l) + " " + print(r) + ")"
//    case LT(l, r) => "(< " + print(l) + " " + print(r) + ")"
//    case GT(l, r) => "(> " + print(l) + " " + print(r) + ")"
//    case LE(l, r) => "(<= " + print(l) + " " + print(r) + ")"
//    case GE(l, r) => "(>= " + print(l) + " " + print(r) + ")"
//  }
//
//  // Try to prove the negative
//  def check(p: Pred) = ! prove(! p)
//
//  // Prove the predicate by checking for counter example.
//  // Returns true if the solver says "unsat" for !p, false if "sat" or "unknown"
//  def prove(p: Pred) = {
//    implicit val side = new ListBuffer[String]
//
//    for (v <- vars(p))
//      side += (CONST.get(v) match {
//        case None => "(declare-fun " + v.name +
//          " (" + (1 to v.arity).map(_ => "Int").mkString(" ") + ") Int)"
//        case Some(e) => "(define-fun " + v.name +
//          " (" + (1 to v.arity).map("(v" + _ + " Int)").mkString(" ") + ") Int " + print(e) + ")"
//      })
//
//    val formula = print(! p)
//
//    z3.push()
//    for (s <- side)
//      z3.command(s)
//    z3.assert(formula)
//    val out = z3.check()
//    z3.pop()
//
//    out == Unsat
//  }
//
//  // Provides defined mapping (useful for debugging)
//  var CONST: Map[Var, Expr] = Map()
//
//  def close() {
//    z3.close()
//  }
//}
//
//
