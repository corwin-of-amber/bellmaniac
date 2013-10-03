sealed trait Term 

// Recursive algorithm definition
// TODO: we only need values for certain inputs, should be part of the spec
case class Algorithm(v: Var, args: List[Var], pre: Pred, expr: Expr) {
  assert (v.arity == args.size)
  override def toString = Python.print(this)
}

// Boolean predicate
sealed trait Pred extends Term {
  def and(that: Pred): Pred = that match {
    case True => this
    case _ => And(this, that)
  }
  def or(that: Pred): Pred = that match {
    case False => this
    case _ => Or(this, that)
  }
  def unary_! = Not(this)  
  override def toString = Python.print(this)
}
object True extends Pred {
  override def and(that: Pred) = that
}
object False extends Pred {
  override def or(that: Pred) = that
}
sealed trait Comparison extends Pred { 
  def l: Expr
  def r: Expr 
}
case class Eq(l: Expr, r: Expr) extends Comparison
case class GT(l: Expr, r: Expr) extends Comparison
case class LT(l: Expr, r: Expr) extends Comparison
case class GE(l: Expr, r: Expr) extends Comparison
case class LE(l: Expr, r: Expr) extends Comparison
sealed trait BinaryPred extends Pred { 
  def l: Pred
  def r: Pred 
}
case class And(l: Pred, r: Pred) extends BinaryPred
case class Or(l: Pred, r: Pred) extends BinaryPred
case class Not(p: Pred) extends Pred

// Expression language
sealed trait Expr extends Term {
  def +(that: Expr) = Plus(this, that)
  def -(that: Expr) = Minus(this, that)
  def *(that: Expr) = Times(this, that)
  def /(that: Expr) = Div(this, that)
  def mod(that: Expr) = Mod(this, that)
  def ===(that: Expr) = Eq(this, that)
  def <(that: Expr) = LT(this, that)
  def <=(that: Expr) = LE(this, that)
  def >(that: Expr) = GT(this, that)
  def >=(that: Expr) = GE(this, that)
  override def toString = Python.print(this)
  def arity = 0
  def where(v: Var) = {
    val that = this
    new { def in(r: Range) = Compr(that, v, r) }
  }
}

// Fall through conditional statement
case class Cond(cases: List[(Pred, Expr)], default: Expr) extends Expr {
  def ELIF(pe: (Pred, Expr)) = Cond(cases :+ pe, default)
  def ELSE(e: Expr) = Cond(cases, e)
}
object IF {
  def apply(pe: (Pred, Expr)) = Cond(List(pe), Const(0))
}

// Algebra on integers 
case class Const(i: Int) extends Expr 
sealed trait BinaryExpr extends Expr { 
  assert (l.arity == 0 && r.arity == 0)
  def l: Expr
  def r: Expr 
}
case class Plus(l: Expr, r: Expr) extends BinaryExpr
case class Minus(l: Expr, r: Expr) extends BinaryExpr
case class Times(l: Expr, r: Expr) extends BinaryExpr
case class Div(l: Expr, r: Expr) extends BinaryExpr
case class Mod(l: Expr, r: Expr) extends BinaryExpr
object Zero extends Expr
case class Reduce(range: Seq, init: Expr = Zero) extends Expr 

// Functions
sealed trait Funct extends Expr {
  def apply(exprs: Expr*) = App(this, exprs.toList)
}
case class Var(name: String, override val arity: Int = 0) extends Funct {
  def fresh = Var.fresh(name, arity)
  // Translate argument list
  def translate(args: List[Var], op: (Var, Expr)*) = {
    assert (arity > 0)
    val map = op.toMap
    val dargs = args.map(_.fresh)
    val exprs = (args zip dargs).map {
      case (arg, darg) => 
        if (map.contains(arg)) 
          Transform.substitute(map(arg), args zip dargs toMap)
        else
          darg
    }
    OpVar(this, dargs, exprs)
  }
}
object Var {
  private var counter = 0
  def fresh(prefix: String = "_v", arity: Int = 0) = {
    counter = counter + 1
    Var(prefix + counter, arity)
  }
}
case class OpVar(v: Var, args: List[Var], exprs: List[Expr]) extends Funct {
  assert(v.arity > 0, "must be a function")
  assert(v.arity == args.size && exprs.size == args.size, "wrong number of arguments in translation")
  override def arity = v.arity
}
case class App(v: Funct, args: List[Expr]) extends Expr {
  assert(v.arity == args.size, "wrong number of arguments in app")
  def flatten = v match {
    case OpVar(v, vargs, vexprs) =>
      App(v, vexprs.map(Transform.substitute(_, vargs zip args toMap)))
    case _ => this
  }
}

// Sequence of (one-dimensional) values to be reduced
sealed trait Seq extends Term {
  def ++(that: Seq) = Join(this, that)
}
case class Range(l: Expr, h: Expr) 
case class Compr(expr: Expr, v: Var, r: Range) extends Seq 
case class Join(l: Seq, r: Seq) extends Seq 
case class Singleton(e: Expr) extends Seq 

// Collect all variables
object Vars {
  def apply(t: Term): Set[Var] = t match {
    case True | False => Set() 
    case t: Comparison => apply(t.l) ++ apply(t.r)
    case t: BinaryPred => apply(t.l) ++ apply(t.r)
    case Not(p) => apply(p)
    case e: BinaryExpr => apply(e.l) ++ apply(e.r)
    case Zero => Set()
    case _: Const => Set() 
    case Reduce(range, init) => apply(range) ++ apply(init)
    case v: Var => Set(v)
    case OpVar(v, args, exprs) => exprs.toSet[Expr].flatMap(apply(_)) ++ Set(v) -- args.toSet
    case App(v, args) => args.toSet[Expr].flatMap(apply(_)) ++ apply(v)
    case Compr(expr, v, Range(l, h)) => apply(expr) ++ Set(v) ++ apply(l) ++ apply(h)
    case Join(l, r) => apply(l) ++ apply(r)
    case Singleton(e) => apply(e)
    case Cond(cases, default) => 
      cases.flatMap { case (p, e) => apply(p) ++ apply(e) }.toSet ++
      apply(default)
  }
}

object Python {
  val prelude = 
"""
class memoize(dict):
  def __init__(self, func):
    self.func = func
  def __call__(self, *args):
    return self[args]
  def __missing__(self, key):
    result = self[key] = self.func(*key)
    return result
plus = min
zero = 10000000000000000000000000000
"""
  // translate into python list/generator
  def print(s: Seq): String = s match {
    case Singleton(e) => "[" + print(e) + "]"
    case Join(l, r) => print(l) + " + " + print(r)
    case Compr(e, v, Range(l, h)) => "[" + print(e) + " for " + print(v) + 
      " in range(" + print(l) + ", " + print(h) + ")]"
  }
  def print(e: Expr): String = e match {
    case Var(n, _) => n
    case Const(i) => i.toString
    case Plus(l, r) => "(" + print(l) + " + " + print(r) + ")"
    case Minus(l, r) => "(" + print(l) + " - " + print(r) + ")"
    case Times(l, r) => print(l) + "*" + print(r)
    case Div(l, r) => print(l) + "/" + print(r)
    case Mod(l, r) => "(" + print(l) + " mod " + print(r) + ")"
    case App(v, args) => print(v) + "(" + args.map(print(_)).mkString(", ") + ")"
    case Reduce(r, init) => "reduce(plus, " + print(r) + ", " + print(init) + ")"
    case Zero => "zero"
    case OpVar(v, args, exprs) => "(lambda " + args.map(print(_)).mkString(", ") + 
      ": " + print(v) + "(" + exprs.map(print(_)).mkString(", ") + ")"
    case Cond(cases, default) => "  if " + cases.map { case (pred, expr) =>
      print(pred) + ":\n    return " + print(expr)
    }.mkString("\n  elif ") + "\n  else:\n    return " + print(default)          
  }
  def print(p: Pred): String = p match {
    case True => "True"
    case False => "False"
    case And(l, r) => "(" + print(l) + " and " + print(r) + ")"
    case Or(l, r) => "(" + print(l) + " or " + print(r) + ")"
    case Not(l) => "(not " + print(l) + ")"
    case Eq(l, r) => "(" + print(l) + " == " + print(r) + ")"
    case LT(l, r) => "(" + print(l) + " < " + print(r) + ")"
    case GT(l, r) => "(" + print(l) + " > " + print(r) + ")"
    case LE(l, r) => "(" + print(l) + " <= " + print(r) + ")"
    case GE(l, r) => "(" + print(l) + " >= " + print(r) + ")"
  }
  def print(a: Algorithm): String = {
    "@memoize\ndef " + print(a.v) +
    "(" + a.args.map(print(_)).mkString(", ") + "):\n" +     
    "  assert " + print(a.pre) + 
    "\n" + { a.expr match {
      case e: Cond => print(e)
      case e => "  return " + print(e)
    }}
  }
}

object SMT {
  val z3 = new Z3
  import z3._
  // Model comprehensions as sets
  // command("(define-sort Seq () (Array Int Bool))")
  // command("(declare-fun zero () Int)")
  // command("(declare-fun reduce (Seq Int) Int)")
  // command("(declare-fun join (Seq Seq) Seq)")
  // command("(declare-fun abstraction (Int) Seq)")
  command("(define-fun join ((a Int) (b Int)) Int (+ a b))")
  command("(declare-fun zero () Int)")
  command("(define-fun reduce ((a Int) (b Int)) Int (+ a b))")

 
  import collection.mutable.ListBuffer
  def print(e: Expr)(implicit side: ListBuffer[String]): String = e match {
    // TODO: passing higher order functions
    case Var(n, k) if k == 0 => n
    case v @ Var(n, k) if k > 0 => print(App(v, (1 to k).map(i => Var(n + "_v_" + i)).toList))
    case o @ OpVar(Var(n, k), _, _) => print(App(o, (1 to k).map(i => Var(n + "_v_" + i)).toList))
    case Const(i) => i.toString
    case Plus(l, r) => "(+ " + print(l) + " " + print(r) + ")"
    case Minus(l, r) => "(- " + print(l) + " " + print(r) + ")"
    case Times(l, r) => "(* " + print(l) + " " + print(r) + ")"
    case Div(l, r) => 
      // TODO: can't easily express n is a power of two
      side += "(assert " + print((l mod r) === Const(0)) + ")"
      "(div " + print(l) + " " + print(r) + ")"
    case Mod(l, r) => "(mod " + print(l) + " " + print(r) + ")"
    case Zero => "zero"
    case Reduce(r, init) => "(reduce " + print(r) + " " + init + ")"
    case a: App => a.flatten match {
      case App(Var(n, k), args) => "(" + n + " " + args.map(print(_)).mkString(" ") + ")"
      case _ => ???
    }
    case Cond(cases, d) => cases match {
      case (p, e) :: rest=> "(ite " + print(p) + " " + print(e) + "\n " + print(Cond(rest, d)) + ")"
      case Nil => print(d)
    }
  }
  def print(s: Seq)(implicit side: ListBuffer[String]): String = s match {
    case Singleton(e) => ???
    case Join(l, r) => "(join " + print(l) + " " + print(r) + ")"
    case Compr(e, v, Range(l, h)) =>
      /* TODO: not working, use dumb approximation
      val k = Var.fresh()
      side += "(declare-fun " + print(k) + " () Seq)";      
      val i = Var.fresh()      
      side += "(assert (forall ((" + print(i) + " Int)) " + 
        "(iff (select " + print(k) + " " + print(i) + ") (exists ((" + print(v) + " Int)) " +
          print(l <= v and v < h and i === e) + "))))"
      print(k)
      */
      import Transform.substitute
      print(substitute(e, Map(v->h)) - substitute(e, Map(v->l)))
  }
  def print(p: Pred)(implicit side: ListBuffer[String]): String = p match {
    case True => "true"
    case False => "false"
    case And(l, r) => "(and " + print(l) + " " + print(r) + ")"
    case Or(l, r) => "(or " + print(l) + " " + print(r) + ")"
    case Not(l) => "(not " + print(l) + ")"
    case Eq(l, r) => "(= " + print(l) + " " + print(r) + ")"
    case LT(l, r) => "(< " + print(l) + " " + print(r) + ")"
    case GT(l, r) => "(> " + print(l) + " " + print(r) + ")"
    case LE(l, r) => "(<= " + print(l) + " " + print(r) + ")"
    case GE(l, r) => "(>= " + print(l) + " " + print(r) + ")"
  }

  // Check for satisfaction
  def check(p: Pred) = {
    val side = new ListBuffer[String]
    for (v <- Vars(p)) {
      side += "(declare-fun " + v.name + 
        " (" + (1 to v.arity).map(_ => "Int").mkString(" ")+ ") Int)";
      // equality witnesses
      for (i <- 1 to v.arity)
        side += "(declare-fun " + v.name + "_v_" + i + " () Int)";
    }

    val formula = print(p)(side)

    push()
    for (s <- side)
      command(s)
    assert(formula)
    val out = z3.check()

    if (out) {
      println("cex: " + p)
      for (v <- Vars(p) if v.arity == 0)
        println(eval(v.name))
    }

    pop()

    out
  }

  def close() {
    z3.close()
  }
}


object Transform {
  trait Transformer {
    def apply(path: Pred, p: Pred): Option[Pred] = None
    def apply(path: Pred, e: Expr): Option[Expr] = None
    def apply(path: Pred, s: Seq): Option[Seq] = None
  }
  def visit(p: Pred)(implicit path: Pred, f: Transformer): Pred = 
    f(path, p) match {
      case Some(out) => out
      case None => p match {
        case True => True
        case False => False
        case And(l, r) => And(visit(l), visit(r))
        case Or(l, r) => Or(visit(l), visit(r))
        case Not(l) => Not(visit(l))
        case Eq(l, r) => Eq(visit(l), visit(r))
        case LT(l, r) => LT(visit(l), visit(r))
        case GT(l, r) => GT(visit(l), visit(r))
        case LE(l, r) => LE(visit(l), visit(r))
        case GE(l, r) => GE(visit(l), visit(r))
      }
    }
  def visit(e: Expr)(implicit path: Pred, f: Transformer): Expr = 
    f(path, e) match {
      case Some(out) => out
      case None => e match {
        case _: Var => e
        case _: Const => e
        case Plus(l, r) => Plus(visit(l), visit(r))
        case Minus(l, r) => Minus(visit(l), visit(r))
        case Times(l, r) => Times(visit(l), visit(r))
        case Div(l, r) => Div(visit(l), visit(r))
        case Mod(l, r) => Mod(visit(l), visit(r))
        case App(v, args) => 
          App(visit(v).asInstanceOf[Funct], args.map(visit(_)))
        case Zero => Zero
        case Reduce(range, init) => Reduce(visit(range), visit(init))
        case OpVar(v, args, exprs) => 
          OpVar(visit(v).asInstanceOf[Var], 
            args.map(visit(_).asInstanceOf[Var]), 
            exprs.map(visit(_)))
        case Cond(cases, default) => 
          var els: Pred = path
          Cond(cases.map {
            case (p, e) => 
              val out = (visit(p)(els, f), visit(e)(els and p, f))
              els = els and !p
              out
          }, visit(default)(els, f))
      }
    }
  def visit(s: Seq)(implicit path: Pred, f: Transformer): Seq = 
    f(path, s) match {
      case Some(out) => out
      case None => s match {
        case Compr(expr, v, Range(l, h)) => 
          Compr(visit(expr)(path and l <= v and v < h, f), 
            visit(v).asInstanceOf[Var], 
            Range(visit(l), visit(h)))
        case Join(l, r) => Join(visit(l), visit(r))
        case Singleton(e) => Singleton(visit(e))
      }
    }

  def transformer(f: PartialFunction[Term, Term]) = new Transformer {
    override def apply(path: Pred, p: Pred) = f.lift(p).asInstanceOf[Option[Pred]]
    override def apply(path: Pred, e: Expr) = f.lift(e).asInstanceOf[Option[Expr]]
    override def apply(path: Pred, s: Seq) = f.lift(s).asInstanceOf[Option[Seq]]
  }

  def transform(e: Expr)(f: PartialFunction[Term, Term]): Expr = 
    visit(e)(True, transformer(f))


  def transform(p: Pred)(f: PartialFunction[Term, Term]): Pred = 
    visit(p)(True, transformer(f))

  def substitute(e: Expr, f: Map[Var, Expr]): Expr = 
    transform(e) {
      case v: Var if f.contains(v) => f(v)
    }

  def substitute(p: Pred, f: Map[Var, Expr]): Pred =
    transform(p) {
      case v: Var if f.contains(v) => f(v)
    }
}
/**
 * Refinement steps
 */
class Refinement() {
  // keep all versions of algorithms
  var algs: Set[Algorithm] = Set()
 
  import Transform._

  override def toString = 
    algs.map(_.toString).mkString("\n")

  def step(f: Algorithm => List[Algorithm]): Algorithm => List[Algorithm] = {
    case x: Algorithm =>
      val out = f(x)
      algs += x
      algs ++= out
      println(x)
      println("*** refined to ")
      out.foreach(println(_))
      out
  }

  // Add parameters to a function 
  def introduce(name: String, vs: Var*) = 
    step {
      case Algorithm(v, args, pre, e) => 
        val w = Var(name, v.arity + vs.size)
        Algorithm(w, args ++ vs.toList, pre, transform(e) {
          case App(f, args) if v == f => App(w, args ++ vs.toList)      
        }) :: Nil
    }
  
  
  // Create specialized versions of alg by splitting the domain
  def split(name: String, base: Pred, splits: Pred*) = 
    step {
      case Algorithm(v, args, pre, e) =>
        var cases: List[(Pred, Expr)] = Nil;
        var algs: List[Algorithm] = Nil;

        var out = IF (base -> App(v, args))

        def explore(mask: List[Boolean] = Nil) {
          if (mask.size == splits.size) {
            val p = (mask.reverse zip splits.toList) map {
              case (b, split) => if (b) split else !split
            } reduce (_ and _)

            if (SMT.check(p and pre)) {
              val n = v.name + mask.reverse.map(if (_) "0" else "1").mkString
              val cs = Algorithm(Var(n, v.arity), args, pre and p, App(v, args))
              out = out ELIF (p -> App(cs.v, args))
              algs = cs :: algs        
            }
          } else {
            explore(true :: mask)
            explore(false :: mask)
          }
        }
        explore()

        out = out ELSE App(v, args)

        Algorithm(Var(name, v.arity), args, pre, out) :: algs.reverse
      }

/*
  // Rewrite calls to d.v as d provided it's valid
  def rewrite(c: Algorithm, op: (Var, Expr)*) = (a: Algorithm) => {
    val d = c.translate(op: _*)  
    a.make(_.map {
        case (pred, expr) => (pred, 
          if (proveInd(a.pre and pred, c, d)) {
            transform(expr) {
              case App(w, args) if w == c.v => App(d, args).flatten
            }
          } else {
            expr
          })
      })      
  }

  // Prove by induction that pred(v) => c(v) = c(f(v)) where d = OpVar(c, f)
  def proveInd(pred: Pred, c: Algorithm, d: OpVar): Boolean = {
    assert (d.v == c.v)
    // check domains: d is well defined at p and c.pre
    val domain = pred and c.pre and ! substitute(c.pre, 
      c.args zip App(d, c.args).flatten.args)
    if (SMT.check(domain)) {
      println("*** failed domain check")
      return false
    }

    // check that inductive calls satisfy pred
    visit(c)({ (e, path) => 
      e match {
        case a @ App(v, args) if v == c.v =>
          if (SMT.check(path and ! substitute(pred, c.args zip args))) {
            println("*** failed inductive step check")
            return false
          }
        case _ =>
      }
    None }, pred)

   
    // prove by induction on v
    // inductive step
    // ind is an uninterpreted version of c for the inductive step
    val ind = Var("_ind_"+c.v.name, c.v.arity)
    for ((p, e) <- c.cases) {
      val ce = transform(e) {
        case App(v, args) if v == c.v =>
          // unroll with d to ind
          App(d, args).flatten match {
            case App(v, args) => assert(v == c.v); App(ind, args)
          }
      }
      val de = transform(substitute(e, c.args zip App(d, c.args).flatten.args)) {
        case App(v, args) if v == c.v => App(ind, args)
      }
      if (SMT.check(pred and c.pre and p and !(ce === de))) {
        println("*** failed to prove equation equality")
        println(ce)
        println(de)
        return false
      }
    }

    // base case
    // TODO
    true
  }


  // Replace calls to c with calls to c1 provided ind decreases and its pre-condition is satisfied
  // c1 is a refinement and/or restriction of c0
  // TODO: induction should be a global metric on all algorithms
  def refine(c: Algorithm, c1: Algorithm, ind: Expr) = {
    assert(c.args == c1.args)
    (a: Algorithm) => 
    a.make(_ => visit(a)({ (e, path) => 
      e match {          
        case app @ App(v, args) if v == c.v =>
          if (SMT.check(path and ! (substitute(ind, c.args zip args) < ind))) {
            println("** can't refine because induction fails")
            None
          } else if (SMT.check(path and ! (substitute(c1.pre, c1.args zip args)))) {
            println("** can't refine because pre fails")
            None
          } else
            Some(App(c1.v, args))
        case _ => 
          None
      }}, True))          
  }
  

  def unfold(c: Algorithm) = (a: Algorithm) =>
    a.make(_.flatMap {
        case (p, App(v, args)) if v == c.v =>
          c.cases.map {
            case (cp, ce) => (p and cp, substitute(ce, c.args zip args))
          }
        case t => List(t)
    })

  // Split "k in range(a,b) into k1 in range(a,e) and k2 in range(e,b)
  def splitRange(k: Var, mid: Expr) = (a: Algorithm) =>   
    a.make(_.map {
      case (p, e) => (p, transform(e) {
        case Compr(e, v, Range(l, h)) if v == k && 
          ! SMT.check(a.pre and ! (l <= mid and mid <= h)) => 
          val v1 = Var(v.name + "1")
          val v2 = Var(v.name + "2")
          Join(Compr(substitute(e, Map(v->v1)), v1, Range(l, mid)), 
              Compr(substitute(e, Map(v->v2)), v2, Range(mid, h)))
      })
    }) 
  */
}

object Parenthesis {
  import Prelude._
  implicit def int2expr(i: Int) = Const(i)

  val c = Var("c", 2)
  val w = Var("w", 3)
  val x = Var("x", 1)
  
  val C = Algorithm(c, i :: j :: Nil, 
    0 <= i and i < n and i < j and j < n, 
    IF 
      ((i === j - 1) -> x(j))
    ELSE 
      Reduce(
        (c(i, k) + c(k, j) where k in Range(i+1, j)) ++ 
        (w(i, l, j) where l in Range(i+1, j))))
    
  def main(args: Array[String]) {
    import Console.println
    import Transform._
    
    val R = new Refinement()
    import R._

    val List(c0) = introduce("c0", n, w, x)(C)
    val List(c1, c000, c001, c011) = split("c1", n < 4, i < n/2, j < n/2)(c0) 
    val List(cs1) = rewrite(c0, n -> n/2)(c000)
    /*
    val cs11 = refine(c0, c1, n)(cs1)
 
    // domain check fails for n = 3, i = 1, j = 2
    // use free assumption n mod 2 = 0
  
    val cs3 = rewrite(c0, i -> (i-n/2), j -> (j-n/2), n -> n/2, 
      x -> x.translate(List(j), j->(j+n/2)), 
      w -> w.translate(List(i, j, k), i->(i+n/2), j->(j+n/2), k->(k+n/2)))(c011)
    println(cs3)
    
    // hard case

    val cs31 = refine(c0, c1, n)(cs3)
    println(cs31)

    val b = unfold(c0)(c001)
    println(b)

    val b1 = splitRange(k, n/2)(b)
    println(b1)

    val b2 = 
      (refine(c0, cs11, j-i) andThen
      refine(c0, cs31, j-i))(b1)
    println(b2)

    val b3 = refine(c0, b2, j-i)(b2)
    println(b3)

    val s = Var("s", 5)
    val t = Var("t", 5)
    val b4 = generalize(cs11.v->s, cs31.v->t)(b3)
    println(b4)

    val List(b5, b00, b01, b10, b11) = split(n < 8, i < n/4, j < n/2+n/4)(b4)
    println(b5)
    println(b00)
    println(b01)
    println(b10)
    println(b11)

    val b100 = rewrite(b4, 
        i->(i-n/4),
        j->(j-n/4),
        n->n/2,
        w->w.translate(List(i,j,k), i->(i+n/4),j->(j+n/4),k->(k+n/4)),
        x->x.translate(List(i), i->(i+n/4)),
        s->s.translate(List(i,j,n,w,x), i->(i+n/4), j->(j+n/4)),        
        t->t.translate(List(i,j,n,w,x), i->(i+n/4), j->(j+n/4)))(b10)
    println(b100)
    */

    SMT.close()
  }
}

object Gap {
  import Prelude._
  implicit def int2expr(i: Int) = Const(i)
  implicit def expr2singleton(e: Expr) = Singleton(e)

  val w = Var("w", 2)
  val w1 = Var("w1", 2)
  val S = Var("S", 2)
  val g = Var("g", 2)

  val G = Algorithm(g, i :: j :: Nil,
    0 <= i and i <= n and 0 <= j and j <= n,
    IF  
      ((i === 0 and j === 0) -> 0)
    ELIF 
      ((i === 0 and j > 0) -> w(0, j))
    ELIF 
      (((i > 0 and j === 0) -> w1(0, i)))
    ELSE 
      Reduce(
        (g(i, q) + w(q, j) where q in Range(0, j)) ++
        (g(p, j) + w1(p, i) where p in Range(0, i)) ++
        (g(i-1, j-1) + S(i, j))))
}

object Floyd {
  import Prelude._ 
  implicit def int2expr(i: Int) = Const(i)

  val l = Var("l", 2)
  val d = Var("d", 3)

  // TODO: custom operators
  val D = Algorithm(d, i :: j :: k :: Nil,
    0 <= i and i < n and
    0 <= j and j < n and
    0 <= k and k <= n,
    IF 
      ((k === 0) -> l(i, j))
    ELSE 
      (d(i, j, k-1) + d(i, k-1, k-1) * d(k-1, j, k-1)))
}


object Prelude {
  val i = Var("i")
  val j = Var("j") 
  val k = Var("k")
  val l = Var("l")
  val m = Var("m")
  val n = Var("n")
  val o = Var("o")
  val p = Var("p")
  val q = Var("q")
}
