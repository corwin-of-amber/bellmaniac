object Gap {
  import Prelude._

  val w = Var("w", 2)
  val w1 = Var("w1", 2)
  val s = Var("s", 2)
  val w2 = Var("w2")
  val r = Var("r", 2) 
  val g = Var("g", 2)

  // TODO: twisted coordinates not implemented since can't handle non-shifting linear transformations
  // e.g. if we replace w1 by its transpose, we can't generate code as of now

  val gap = Algorithm(g, i :: j :: Nil,
    0 <= i and i <= n and 0 <= j and j <= n and n > 0, 
    // n > 0 important so that cases are truly disjoint
    IF  
      ((i === 0 and j === 0) -> w2)
    ELIF 
      ((i === 0 and j > 0) -> w(0, j))
    ELIF 
      (((i > 0 and j === 0) -> w1(i, 0)))
    ELSE 
      Reduce(
        (g(i, q) + w(q, j) where q in Range(0, j)) ++
        (g(p, j) + w1(i, p) where p in Range(0, i)) ++
        (g(i-1, j-1) + s(i, j)) ++ 
        r(i, j)))

  def main(args: Array[String]) {
    val proof = new Proof
    import proof._
    
    input(n, 64)
    input(w)
    input(w1)
    input(w2, 0)
    input(s)    
    input(r, Zero)

    add(gap, i+j)

    // add variables to unify 
    val v = Var("v", 2)
    val v1 = Var("v1", 2)

    val g0 = (   
      genApp($, w, v) andThen
      genApp($, w1, v1) andThen
      introduce($, n, w, w1, w2, s, r)(n) andThen 
      selfRefine("g0")
    )(gap)
    val List(g1, g00, g01, g10, g11) = split("g1", n < 4, i <= n/2, j <= n/2)(g0)

    
    val gij = g0.capture(2)

    val g100 = rewrite("g100", g0)(n -> n/2)(g00)
  
    val t = Var("t", 2)
    val b = Algorithm(Var("b", 6), List(i, j, n, w, t, r),
      gap.pre,
      Op(Reduce(t(i, q) + w(q, j) where q in Range(0, n)), r(i, j)))
    add(b, 0)    
    
    val g101 = rewrite("g101", g0,
      $$.guard($, i > 0 and j === n/2) andThen $$.splitRange($, q, n/2),
      $$.unfold($, b))(
      n -> n/2,
      i -> i,
      j -> (j-n/2),
      v -> (v>>(0,n/2)),
      v1 -> (gij>>(0,n/2)),
      w -> (w>>(n/2,n/2)),
      r -> b.gen(2)(i, j, n/2, w>>(0,n/2), gij, r>>(0,n/2)),
      w2 -> v(0, n/2),
      s -> (s>>(0,n/2))
    )(relax($, 0 <= i and i <= n/2 and n/2 <= j and j <= n and 0 < n)(g01))
    
    val g201 = specialize("g201", g0)(g101)
    
    val c = Algorithm(Var("c", 6), List(i, j, n, w1, t, r),
      gap.pre,
      Op(Reduce(t(p, j) + w1(i, p) where p in Range(0, n)), r(i, j)))
    add(c, 0)
  
    val g110 = rewrite("g110", g0,
      $$.guard($, i === n/2 and j > 0) andThen $$.splitRange($, p, n/2),
      $$.unfold($, c))(
      n -> n/2,
      i -> (i-n/2),
      j -> j,
      v -> (gij>>(n/2,0)),
      r -> c.gen(2)(i, j, n/2, w1>>(n/2,0), gij, r>>(n/2,0)),
      v1 -> (v1>>(n/2,0)),
      w -> w,
      w1 -> (w1>>(n/2,n/2)),
      w2 -> v1(n/2, 0),
      s -> (s>>(n/2,0))
    )(relax($, n/2 <= i and i <= n and 0 <= j and j <= n/2 and 0 < n)(g10))

    val g210 = specialize("g210", g0)(g110)
  
    val g111 = rewrite("g111", g0,
      $$.guard($, i === n/2 or j === n/2) andThen $$.splitRange($, p, n/2) andThen $$.splitRange($, q, n/2),
      $$.unfold($, c) andThen $$.unfold($, b))(
      n -> n/2,
      i -> (i-n/2),
      j -> (j-n/2),
      w -> (w>>(n/2,n/2)),
      w1 -> (w1>>(n/2,n/2)),
      w2 -> gij(n/2,n/2),      
      s -> (s>>(n/2,n/2)),
      v -> (gij>>(n/2, n/2)),      
      v1 -> (gij>>(n/2, n/2)),
      r -> c.gen(2)(i, j, n/2, w1>>(n/2,0), gij>>(0,n/2),
        b.gen(2)(i, j, n/2, w>>(0,n/2), gij>>(n/2,0), r>>(n/2,n/2)))
    )(relax($, n/2 <= i and i <= n and n/2 <= j and j <= n and 0 < n)(g11))

    val g211 = specialize("g211", g0)(g111)
    
    val List(b1, b00, b01, b10, b11) = split("b1", n < 4, i < n/2, j < n/2)(b)    
    val b100 = rewrite("b100", b, $$.splitRange($, q, n/2), $$.unfold($, b))(
      n -> n/2,
      r -> b.gen(2)(i, j, n/2, w>>(n/2,0), t>>(0,n/2), r)
    )(b00)    
    val b101 = rewrite("b101", b, $$.splitRange($, q, n/2), $$.unfold($, b))(
      n -> n/2,
      j -> (j-n/2),
      w -> (w>>(0,n/2)),
      r -> b.gen(2)(i, j, n/2, w>>(n/2,n/2), t>>(0,n/2), r>>(0,n/2))
    )(b01)
    val b110 = rewrite("b110", b, $$.splitRange($, q, n/2), $$.unfold($, b))(
      n -> n/2,
      i -> (i-n/2),
      t -> (t>>(n/2,0)),
      r -> b.gen(2)(i, j, n/2, w>>(n/2,0), t>>(n/2,n/2), r>>(n/2,0))
    )(b10)
    val b111 = rewrite("b111", b, $$.splitRange($, q, n/2), $$.unfold($, b))(
      n -> n/2,
      i -> (i-n/2),
      j -> (j-n/2),
      w -> (w>>(0,n/2)),
      t -> (t>>(n/2,0)),
      r -> b.gen(2)(i, j, n/2, w>>(n/2,n/2), t>>(n/2,n/2), r>>(n/2,n/2))
    )(b11)

    val List(c1, c00, c01, c10, c11) = split("c1", n < 4, i < n/2, j < n/2)(c)
    val c100 = rewrite("c100", c, $$.splitRange($, p, n/2), $$.unfold($, c))(
      n -> n/2,
      r -> c.gen(2)(i, j, n/2, w1>>(0,n/2), t>>(n/2,0), r)
    )(c00)
    val c101 = rewrite("c101", c, $$.splitRange($, p, n/2), $$.unfold($, c))(
      n -> n/2,
      j -> (j-n/2),
      t -> (t>>(0,n/2)),
      r -> c.gen(2)(i, j, n/2, w1>>(0,n/2), t>>(n/2,n/2), r>>(0,n/2))
    )(c01)
    val c110 = rewrite("c110", c, $$.splitRange($, p, n/2), $$.unfold($, c))(
      n -> n/2,
      i -> (i-n/2),
      w1 -> (w1>>(n/2,0)),
      r -> c.gen(2)(i, j, n/2, w1>>(n/2,n/2), t>>(n/2,0), r>>(n/2,0))
    )(c10)
    val c111 = rewrite("c111", c, $$.splitRange($, p, n/2), $$.unfold($, c))(
      n -> n/2,
      i -> (i-n/2),
      j -> (j-n/2),
      t -> (t>>(0,n/2)),
      w1 -> (w1>>(n/2,0)),
      r -> c.gen(2)(i, j, n/2, w1>>(n/2,n/2), t>>(n/2,n/2), r>>(n/2,n/2))
    )(c11)

    val py = new NumPython(proof, 2)    
    compile(gap, new java.io.PrintStream(new java.io.File("gap.py")), py)
    println(proof)
    close()
  }

}

