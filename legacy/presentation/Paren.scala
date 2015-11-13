object Parenthesis {
  import Prelude._
  import java.io.{PrintStream, File}
  
  // function w takes 3 inputs, x takes 1 input
  val w = Var("w", 3)
  val x = Var("x", 1)
   
  val c = Var("c", 2)
  // define c(i, j) 
  val par = Algorithm(c, i :: j :: Nil,
    // pre-condition
    0 <= i and i < n and i < j and j < n,
    // recursive definition
    IF ((i === j-1) -> x(i)) 
    ELSE
      Reduce(c(i, k) + c(k, j) + w(i, k, j) 
      where k in Range(i+1, j)))
   
  def main(args: Array[String]) {
    // initiate refinement environment
    val proof = new Proof()
    import proof._
   
    // add w,x,n as global input tables
    input(n, 128)
    input(w)
    input(x)

    // add par
    // second argument defines decreasing ranking function 
    // termination is checked at this step
    add(par, j-i)

    // define r(i, j) to hold the initial table values
    val r = Var("r", 2)
    val R = Algorithm(r, List(i, j), par.pre, IF ((i === j-1) -> x(i)) ELSE Zero)
    add(R, 0)

    // first manually change expression of c to use r and prove equivalence
    // $ just makes a fresh name for a variable
    val par0 = manual($, 
      // Op is the monadic operation used in Reduce; prover knows standard monad axioms
      Op(Reduce(c(i, k) + c(k, j) + w(i, k, j) where k in Range(i+1, j)), r(i, j)),
      // tell prover ($$ is meant for prover) to unfold r above
      $$.unfold($, R))(par)

    // add n,w,r as parameters to c
    val c0 = (introduce($, n, w, r)(n) andThen 
      // recurse to c0 instead of c
      selfRefine("c0"))(par0)    

    // partition into cases based on predicates
    // c1 calls c0 if n < 4, or calls c000, ... depending on the predicates
    // (e.g. c000 stands for i < n/2, j < n/2, c001 stands for i < n/2, j >= n/2)
    // one case is eliminated automatically using pre-condition
    val List(c1, c000, c001, c011) = split("c1", n < 4, i < n/2, j < n/2)(c0) 
  
    // prove by induction that we can change n to n/2 in the call to c0 in c000
    val c100 = rewrite("c100", c0)(n -> n/2)(c000) 

    // note: free assumption n mod 2 = 0 

    // prove by induction that the change to parameters is OK
    val c111 = rewrite("c111", c0)(
        i->(i-n/2), 
        j->(j-n/2), 
        n->n/2, 
        // shift notation: \lambda i, j, k . w(i + n/2, j + n/2, k + n/2)
        w->(w>>(n/2,n/2,n/2)), 
        r->(r>>(n/2,n/2))
      )(c011)

    // we have to make a very general version of b0 to make proofs work

    // define auxiliary functions
    val s = Var("s", 2)
    val t = Var("t", 2)
    val w1 = Var("w1", 3)
    // starting from c001 unfold c0
    val b0 = (unfold($, c0) andThen
      // split Range(i+1, j) into two list comprehensions over Range(i+1, n/2) and Range(n/2, j)
      splitRange($, k, n/2) andThen
      // inside each list comprehension pick a specialization of c0 (c001, c001, c011) using
      // the path condition
      specialize($, c0) andThen
      // make c000 and c011 parameters s and t
      genApp($, c000.v, s) andThen 
      genApp($, c011.v, t) andThen
      // change first application of w to a new parameter w1
      genApp($, w, w1) andThen
      // recurse to b0 instead (and populate the additional arguments)
      selfRefine("b0"))(c001)

    // separate b0 into four cases
    val List(b1, b000, b001, b010, b011) = split("b1", n < 4, i < n/4, j < n/2+n/4)(b0)
       
    // reduce to n/2
    val b110 = rewrite("b110", b0)(
        i->(i-n/4),
        j->(j-n/4),
        n->n/2,
        w->(w>>(n/4,n/4,n/4)),
        w1->(w1>>(n/4,n/4,n/4)),
        s->(s>>(n/4,n/4)),       
        t->(t>>(n/4,n/4)),
        r->(r>>(n/4,n/4))
      )(b010)

    // define d explicitly
    // note: should be inferred from c eventually
    val d = Var("d0", 7)
    val D = Algorithm(d, List(i, j, n, w, r, s, t), 
      0 <= i and i < n/2 and 0 <= j and j < n/2,
      Op(Reduce(s(i, k) + t(k, j) + w(i, k, j) where k in Range(0, n/2)), r(i, j)))

    // add and check d
    // important to have n to make split pass termination test
    add(D, n)
     
    // sugar: curry b0 to take first two parameters 
    val bij = b0.capture(2) 

    // reduce to n/2
    val b100 = rewrite("b100", b0, 
        // tell prover split range in b000 
        $$.splitRange($, Var("k1"), n/4),
        // tell prover to unfold D in b100
        // the equivalence of the symbolic expressions becomes provable
        // using solely monad axioms
        $$.unfold($, D))(
        i->i,
        j->(j-n/4),
        n->n/2,        
        w->(w>>(0,n/4,n/4)),
        w1->(w1>>(0,0,n/4)),        
        t->(t>>(n/4,n/4)),
        // make d a function of i, j and pass the following arguments to d
        r->D.gen(2)(i, j-n/4, n/2, w1>>(0,n/4,n/2), 
          r>>(0,n/2),s>>(0,n/4),bij>>(n/4,n/2))          
      )(b000)

    // specialize inner bij using the path condition
    val b200 = specialize("b200", b0)(b100)

    val b111 = rewrite("b111", b0, $$.splitRange($, Var("k2"), n/4+n/2), $$.unfold($, D))(
        i->(i-n/4),
        j->(j-n/2),
        s->(s>>(n/4,n/4)),
        t->(t>>(n/2,n/2)),
        w->(w>>(n/4,n/2,n/2)),
        w1->(w1>>(n/4,n/4,n/2)),
        n->n/2,
        r->D.gen(2)(i, j-n/4, n/2, w>>(n/4,n/2,n/2+n/4),
          r>>(n/4,n/2+n/4), bij>>(n/4,n/2), t>>(n/2,n/2+n/4))
      )(b011)

    val b211 = specialize("b211", b0)(b111)
    
    val b101 = rewrite("b101", b0, 
        $$.splitRange($, Var("k1"), n/4) andThen $$.splitRange($, Var("k2"), n/4+n/2),
        $$.unfold($, D) andThen $$.unfold($, D))(
        j->(j-n/2),
        n->n/2,
        s->s,
        w1->(w1>>(0,0,n/2)),
        t->(t>>(n/2,n/2)),
        w->(w>>(0,n/2,n/2)),
        r->D.gen(2)(i, j-n/4, n/2, w1>>(0,n/4,n/2+n/4),
          D.gen(2)(i, j, n/2, w>>(0,n/2,n/2+n/4), r>>(0,n/2+n/4), bij>>(0,n/2), t>>(n/2,n/2+n/4)), 
          s>>(0,n/4), bij>>(n/4,n/2+n/4))        
      )(b001)
    
    val b201 = specialize("b201", b0)(b101)

    // repeat the process for d

    val List(d1, d00, d01, d10, d11) = split("d1", n < 4, i < n/4, j < n/4)(D)
    val d100 = rewrite("d100", D, $$.splitRange($, k, n/4), $$.unfold($, D))(
      n->n/2, 
      r->D.gen(2)(i,j,n/2,w>>(0,n/4,0),r,s>>(0,n/4),t>>(n/4,0))
    )(d00)
    val d110 = rewrite("d110", D, $$.splitRange($, k, n/4), $$.unfold($, D))(
      i->(i-n/4), n->n/2, 
      r->D.gen(2)(i, j, n/2, w>>(n/4,0,0), r>>(n/4,0), s>>(n/4,0), t),
      w->(w>>(n/4,n/4,0)),
      s->(s>>(n/4,n/4)),
      t->(t>>(n/4,0))
    )(d10)
    val d101 = rewrite("d101", D, $$.splitRange($, k, n/4), $$.unfold($, D))(
      j->(j-n/4), n->n/2,
      r->D.gen(2)(i, j, n/2, w>>(0,0,n/4), r>>(0,n/4), s, t>>(0, n/4)),
      w->(w>>(0,n/4,n/4)),
      s->(s>>(0,n/4)),
      t->(t>>(n/4,n/4))
    )(d01)
    val d111 = rewrite("d111", D, $$.splitRange($, k, n/4), $$.unfold($, D))(
      i->(i-n/4), j->(j-n/4), n->n/2,
      r->D.gen(2)(i, j, n/2, w>>(n/4,0,n/4), r>>(n/4,n/4), s>>(n/4,0), t>>(0,n/4)),
      w->(w>>(n/4,n/4,n/4)),
      s->(s>>(n/4,n/4)),
      t->(t>>(n/4,n/4))
    )(d11)

    // create imperative code generator; 2 makes it use (i, j) for table dimensions
    val py = new NumPython(proof, 2)    

    // refine all functions to finest level, inline, introduce offsets,
    // eliminate common sub-expressions, introduce valid memory overwrites
    compile(par, new PrintStream(new File("paren.py")), py)
    close()
  }
}

