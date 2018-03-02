//object Floyd {
//  import Prelude._
//  import java.io.{File, PrintStream}
//
//  // distance matrix
//  // assume r(i,i) == 0
//  val r = Var("r", 2)
//  val f = Var("f", 3)
//
//  // here semi-ring is instantiated for Floyd Warshall
//  val floyd = Algorithm(f, i :: j :: k :: Nil,
//    0 <= i and i < n and
//    0 <= j and j < n and
//    0 <= k and k <= n,
//    IF
//      ((k === 0) -> r(i, j))
//    ELSE
//      Op(f(i, j, k-1), f(i, k-1, k-1) + f(k-1, j, k-1)))
//
//  def main(args: Array[String]) {
//    val proof = new Proof
//    import proof._
//
//    input(n, 64)
//    input(r)
//    add(floyd, k)
//
//    val a = (introduce($, n, r)(n) andThen selfRefine("a"))(floyd)
//
//    // derive b,c,d problems
//    val s = Var("s", 3)
//    val t = Var("t", 3)
//    // op(b, s+b)
//    val b = (genApp($, a.v, s, 1) andThen selfRefine("b"))(a)
//    // op(c, c+t)
//    val c = (genApp($, a.v, t, 2) andThen selfRefine("c"))(a)
//
//    // cut refinement at this point since this leads to twisting
//    val c1 = ($$.app($) andThen rewrite0("c1", c, b, b.v)(
//      i -> j,
//      j -> i,
//      s -> (t >> ((i,j,k) => (j,i,k))),
//      r -> (r >> ((i,j) => (j,i)))
//    ))(c)
//    // op(d, s+t)
//    val d = (genApp($, b.v, t, 1) andThen selfRefine("d"))(b)
//
//    // cases for b
//    val List(b1, b000, b001, b010, b011, b100, b101, b110, b111) =
//      split("b1", n < 4, i < n/2, j < n/2, k <= n/2)(b)
//
//    val b000x = rewrite("b000x", b)(n -> n/2)(b000)
//    val b010x = rewrite("b010x", b)(
//      j->(j-n/2), n->n/2, r->(r>>(0, n/2)))(b010)
//    val b100x = (
//      refine($, b.v, d.v) andThen
//      rewrite($, d)(
//        i->(i-n/2), n->n/2, r->(r>>(n/2,0)), s->(s>>(n/2,0,0))) andThen
//      specialize("b100x", b)
//    )(b100)
//    val b110x = (
//      refine($, b.v, d.v) andThen
//      rewrite($, d)(
//        i->(i-n/2), j->(j-n/2), n->n/2, r->(r>>(n/2,n/2)),
//        s->(s>>(n/2,0,0)), t->(t>>(0,n/2,0))) andThen
//      specialize("b110x", b)
//    )(b110)
//    val b101x = (
//      relax($, n/2 <= i and i < n and 0 <= j and j < n/2 and n/2 <= k and k <= n) andThen
//      rewrite($, b,
//        $$.guard($, k === n/2))(
//        i->(i-n/2), k->(k-n/2), n->n/2,
//        s->(s>>(n/2,n/2,n/2)),
//        r->b.gen(2)(i+n/2, j, n/2, n, r, s)) andThen
//      specialize("b101x", b)
//    )(b101)
//    val b111x = (
//      relax($, n/2 <= i and i < n and n/2 <= j and j < n and n/2 <= k and k <= n) andThen
//      rewrite($, b,
//        $$.guard($, k === n/2))(
//        i->(i-n/2), j->(j-n/2), k->(k-n/2), n->n/2,
//        s->(s>>(n/2,n/2,n/2)),
//        r->b.gen(2)(i+n/2, j+n/2, n/2, n, r, s)) andThen
//      specialize("b111x", b)
//    )(b111)
//    val b001x = (
//      relax($, 0 <= i and i < n/2 and 0 <= j and j < n/2 and n/2 <= k and k <= n) andThen
//      refine($, b.v, d.v) andThen
//      rewrite($, d,
//        $$.guard($, k === n/2))(
//        k->(k-n/2), n->n/2,
//        s->(s>>(0,n/2,n/2)),
//        t->(t>>(n/2,0,n/2)),
//        r->d.gen(2)(i, j, n/2, n, r, s, t)) andThen
//      specialize("b001x", b)
//    )(b001)
//    val b011x = (
//      relax($, 0 <= i and i < n/2 and n/2 <= j and j < n and n/2 <= k and k <= n) andThen
//      refine($, b.v, d.v) andThen
//      rewrite($, d,
//        $$.guard($, k === n/2))(
//        j->(j-n/2), k->(k-n/2), n->n/2,
//        s->(s>>(0,n/2,n/2)),
//        t->(t>>(n/2,n/2,n/2)),
//        r->d.gen(2)(i, j+n/2, n/2, n, r, s, t)) andThen
//      specialize("b011x", b)
//    )(b011)
//
//    val List(a1, a000, a001, a010, a011, a100, a101, a110, a111) =
//      split("a1", n < 4, i < n/2, j < n/2, k <= n/2)(a)
//
//    // lift version of a
//    val ax = a.capture(3)
//    val amid = a.gen(2)(i, j, n/2, n, r)
//
//    // cases for a
//    val a000x = rewrite("a000x", a)(n -> n/2)(a000)
//    val a010x = (rewrite0($, a, b, a.lift(b.v)(ax))(
//      j->(j-n/2),
//      r->(r>>(0,n/2))) andThen
//      specialize("a010x", a)
//    )(a010)
//    val a100x = (rewrite0($, a, c, a.lift(c.v)(ax))(
//      i->(i-n/2), r->(r>>(n/2,0))) andThen
//      specialize("a100x", a)
//    )(a100)
//    val a110x = (rewrite0($, a, d,
//      a.lift(d.v)(ax>>(n/2,0,0), ax>>(0,n/2,0)))(
//      i->(i-n/2), j->(j-n/2), r->(r>>(n/2,n/2))) andThen
//      specialize("a110x", a)
//    )(a110)
//    // relax to k >= n/2
//    val a111x = (
//      relax($, a.pre and i >= n/2 and j >= n/2 and k >= n/2) andThen
//      rewrite($, a,
//        $$.guard($, k === n/2))(
//        i->(i-n/2),
//        j->(j-n/2),
//        k->(k-n/2),
//        n->n/2,
//        r->(amid>>(n/2, n/2))) andThen
//      specialize("a111x", a)
//    )(a111)
//    val a011x = (
//      relax($, a.pre and i < n/2 and j >= n/2 and k >= n/2) andThen
//      rewrite0($, a, c,
//        a.lift(c.v)(ax>>(n/2,n/2,n/2)),
//        $$.guard($, k === n/2))(
//        j->(j-n/2),
//        k->(k-n/2),
//        r->(amid>>(0,n/2))) andThen
//      specialize("a011x", a)
//    )(a011)
//    val a101x = (
//      relax($, a.pre and i >= n/2 and j < n/2 and k >= n/2) andThen
//      rewrite0($, a, b,
//        a.lift(b.v)(ax>>(n/2,n/2,n/2)),
//        $$.guard($, k === n/2))(
//        i->(i-n/2), k->(k-n/2), r->(amid>>(n/2,0))) andThen
//      specialize("a101x", a)
//    )(a101)
//    val a001x = (
//      relax($, a.pre and i < n/2 and j < n/2 and k >= n/2) andThen
//      rewrite0($, a, d,
//        a.lift(d.v)(ax>>(0,n/2,n/2), ax>>(n/2,0,n/2)),
//        $$.guard($, k === n/2))(
//        k->(k-n/2), r->amid) andThen
//      specialize("a001x", a)
//    )(a001)
//
//    compile(floyd, new PrintStream(new File("floyd.py")),
//      new NumPython(proof, 3))
//    println(proof)
//    close()
//  }
//}
//
