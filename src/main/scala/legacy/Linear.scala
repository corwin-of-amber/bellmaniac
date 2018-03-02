//// Rational number
//class Rational(n: Int, d: Int) {
//  assert(d != 0)
//  private def gcd(x: Int, y: Int): Int = {
//    if (x == 0)
//      y
//    else
//      if (x < 0)
//        gcd(-x, y)
//      else if (y < 0)
//        -gcd(x, -y)
//      else gcd(y % x, x)
//  }
//  private val g = gcd(n, d)
//  val numer: Int = n/g
//  val denom: Int = d/g
//  def +(that: Rational) =
//    new Rational(numer * that.denom + that.numer * denom,
//      denom * that.denom)
//  def -(that: Rational) =
//    new Rational(numer * that.denom - that.numer * denom,
//      denom * that.denom)
//  def *(that: Rational) =
//    new Rational(numer * that.numer, denom * that.denom)
//  def /(that: Rational) =
//    new Rational(numer * that.denom, denom * that.numer)
//  def inverse =
//    new Rational(denom, numer)
//  def eq(that: Rational) =
//    this.numer * that.denom == this.denom * that.numer
//  def positive = (numer > 0 && denom > 0) || (numer < 0 && denom < 0)
//  def >(that: Rational) = (this - that).positive
//  def <(that: Rational) = that > this
//  override def toString = "" + numer + "/" + denom
//}
//// Rational linear combination
//case class Linear(terms: Map[Var, Rational], free: Rational) {
//  import Linear.{zero, one}
//  assert(terms.forall { case (k, v) => ! (v eq zero) })
//
//  def expr =
//    terms.map { case (v, r) => (Const(r.numer)*v)/Const(r.denom) }.fold(Const(0): Expr)(_ + _) +
//    Const(free.numer)/Const(free.denom)
//  def vars = terms.keys.toSet
//  def proj(v: Var) =
//    if (terms.contains(v))
//      terms(v)
//    else
//      zero
//  def drop(v: Var) =
//    Linear(terms - v, free)
//  def has(v: Var) = terms.contains(v)
//  def +(that: Linear) =
//    Linear.make((this.vars ++ that.vars).map {
//      v => (v, this.proj(v) + that.proj(v))}.toMap,
//    this.free + that.free)
//  def -(that: Linear) =
//    Linear.make((this.vars ++ that.vars).map {
//      v => (v, this.proj(v) - that.proj(v))}.toMap,
//    this.free - that.free)
//  def *(r: Rational) =
//    Linear.make(terms.mapValues(_*r), free*r)
//  def /(r: Rational) = this * r.inverse
//  override def toString = expr.toString
//}
//
//case class NonLinear(t: Term) extends RuntimeException(t.toString)
//
//object Linear {
//  val zero = new Rational(0, 1)
//  val one = new Rational(1, 1)
//
//  def make(terms: Map[Var, Rational], free: Rational): Linear =
//    Linear(terms.filter { case (k, v) => ! (v eq zero) }, free)
//
//  def make(e: Expr): Linear = e match {
//    case Plus(a, b) => make(a) + make(b)
//    case Minus(a, b) => make(a) - make(b)
//    case Times(a, Const(i)) => make(a) * new Rational(i, 1)
//    case Times(Const(i), a) => make(a) * new Rational(i, 1)
//    case Div(a, Const(i)) => make(a) * new Rational(1, i)
//    case v: Var if v.arity == 0 => Linear(Map(v -> one), zero)
//    case Const(i) => Linear(Map(), new Rational(i, 1))
//    case _ => throw NonLinear(e)
//  }
//
//  def apply(e: Expr) =
//    try {
//      Some(make(e))
//    } catch {
//      case _: NonLinear => None
//    }
//
//  // extract offsets from expressions if possible
//  // reverses shift/lift operation, e.g. adding a fixed offset and more parameters
//  def offsets(op: OpVar): Option[(Funct, List[Expr])] = op.flatten match {
//    case OpVar(v: Var, args, exprs) if args.size <= exprs.size =>
//      val k = args.size
//      val offsets = (exprs.take(k) zip args) flatMap { case (e, arg) => Linear(e - arg) }
//      // all offsets are linear and do not contain formal arguments
//      if (offsets.size == k &&
//          offsets.forall { o => args.forall { arg => ! o.has(arg)}})
//        Some((
//          if (exprs.size == k)
//            v
//          else
//            OpVar(v, args, args ::: exprs.drop(k)),
//          offsets.map(_.expr)))
//      else
//        None
//    case _ => None
//  }
//
//  // extract linear constraints: each linear >= 0
//  def equations(p: Pred): List[Linear] = p match {
//    case And(p1, p2) => equations(p1) ::: equations(p2)
//    case LE(a, b) => Linear.make(b-a) :: Nil
//    case Not(GT(a, b)) => equations(LE(a, b))
//    case LT(a, b) => Linear.make(b-a-Const(1)) :: Nil
//    case Not(GE(a, b)) => equations(LT(a, b))
//    case GE(a, b) => Linear.make(a-b) :: Nil
//    case Not(LT(a, b)) => equations(GE(a, b))
//    case GT(a, b) => Linear.make(a-b-Const(1)) :: Nil
//    case Not(LE(a, b)) => equations(GT(a, b))
//    case _ => throw NonLinear(p)
//  }
//
//}
//
