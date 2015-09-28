
package examples

import examples.Gap.BreakDown.Instantiated
import syntax.Tree
import syntax.Identifier
import semantics.{TypedLambdaCalculus, Scope, TypedIdentifier}
import semantics.TypeTranslation.Declaration
import semantics.TypeTranslation.Environment
import semantics.TypeTranslation.Declaration
import synth.pods.ConsPod.`⟨ ⟩?`
import synth.pods.{StratifySlashPod, StratifyFixPod, ConsPod, Pod}


object Paren {
  
  import syntax.AstSugar._
  import semantics.Domains._
  import semantics.Prelude._
  
  val J = T(S("J"))
  val J0 = T(S("J₀"))
  val J1 = T(S("J₁"))
  val K0 = T(S("K₀"))
  val K1 = T(S("K₁"))
  val K2 = T(S("K₂"))
  val K3 = T(S("K₃"))
  
  val scope = new Scope
  scope.sorts.declare(N.root)
  scope.sorts.declare(R.root)
  scope.sorts.declare(J.root)
  scope.sorts.declare(J0.root :<: J.root)
  scope.sorts.declare(J1.root :<: J.root)
  scope.sorts.declare(K0.root :<: J0.root)
  scope.sorts.declare(K1.root :<: J0.root)
  scope.sorts.declare(K2.root :<: J1.root)
  scope.sorts.declare(K3.root :<: J1.root)

  def A = TV("A")
  def `A'` = TV("A'")
  def f = TV("f")
  def g = TV("g")
  def θ = TV("θ")
  def i = TV("i")
  def j = TV("j")
  def k = TV("k")
  def e = TV("e")
  def w = TV("w")
  def < = TV("<")
  
  def K12 = TV("K₁₊₂")
  def K02 = TV("K₀₊₂")
  def K012 = TV("K₀₊₁₊₂")
  def K12sq = TV("K₁₊₂²")
  def P1 = TV("P₁")
  def Q0 = TV("Q₀")
  
  def x = TV("x")
  def _0 = TI(0)
  def _1 = TI(1)
  def succ = TV("+1")
  def pred = TV("-1")
  
  def TT(v: Any) = T(new Identifier(v, "type variable"))
  
  val tree = TI("program")(
      
      TV("+") :: (R x R) ->: R ,
      < :: (J x J) ->: B , 
      
      K012   :: J ->: B ,
      K12    :: J ->: B ,
      K12sq  :: (J x J) ->: B ,
      P1     :: (J x J) ->: B ,
      Q0     :: (J x J) ->: B ,
      
      A :- fix( 
        TI("↦")(
          θ :: ∩(J x J, <) ->: R , i , j ,
  
          (@:(x, i) |! ((i+_1) =:= j)) /:
          (min:@(k ↦
              (((θ:@(i, k)) + (θ:@(k, j)) + (w:@(i, k, j))) -: TV("item")))
          ) -: TV("compute")
        ).foldRight -: f ) ,
      
      TV("f|nw") :- ( f :: (? ->: (J0 x J0) ->: ?) ) ,
      TV("f|ne") :- ( f :: (? ->: (J0 x J1) ->: ?) ) ,
      TV("f|sw") :- ( f :: (? ->: (J1 x J0) ->: ?) ) ,
      TV("f|se") :- ( f :: (? ->: (J1 x J1) ->: ?) ) ,
      
      //`A'` :- fix( TV("f|nw") /: TV("f|ne") /: TV("f|se") ) ,
      
      
      g :- TV("f|ne") ,
      
      TV("g|nw") :- ( g :: (? ->: (K0 x K2) ->: ?) ) ,
      TV("g|sw") :- ( g :: (? ->: (K1 x K2) ->: ?) ) ,

      TV("g|nw'") :- (
        TI("↦")(
          θ :: ((J x J) ∩ <) ->: R , i , j ,
  
              (min:@((e :: K0) ↦
                  (((θ:@(i, e)) + (θ:@(e, j)) + (w:@(i, e, j))) -: TV("item1")))) +
              (min:@((k :: K1) ↦
                  (((θ:@(i, k)) + (θ:@(k, j)) + (w:@(i, k, j))) -: TV("item2"))))
                    /*
          min:@(
            cons:@(
              min:@((e :: K0) ↦
                    (((θ:@(i, e)) + (θ:@(e, j)) /*+ (w:@(i, e, j))*/) -: TV("item1"))),
              cons:@(
                min:@((k :: K1) ↦
                    (((θ:@(i, k)) + (θ:@(k, j)) + (w:@(i, k, j))) -: TV("item2"))),
                nil))
          )*/ // -: TV("compute")
        ).foldRight :: (? ->: (K0 x K2) ->: ?) ) 
  
  )
    
    
  def env = {
    import semantics.Prelude._
    import semantics.TypeTranslation
    import semantics.TypeTranslation.TypingSugar._

    val ley = scope.sorts.findSortHie(J.root).get.nodes filter (_.subtrees == List(T(⊥))) toList
    val newbot = new Identifier("⊥.J", "set")
    val h = scope.sorts.hierarchy.replaceDescendants(ley map (t => (t, T(t.root, List(T(newbot, t.subtrees))))))
    scope.sorts.hierarchy = h

    TypeTranslation.subsorts(scope) ++ TypeTranslation.decl(scope, Map(< ~> (J ->: J ->: B), succ ~> (J ->: J ->: B), pred ~> (J -> J))) where 
         ( transitive(J)(<), antisymm(J)(<),
           ∀:( J, (x,y,z) => succ(x,z) -> (<(x,z) & ~(<(x,y) & <(y,z))) ),
           compl(J)(J0, J1), allToAll(J)(J0, <, J1), ∀:( J, x => ~T(newbot)(x) )
           /*partition(J)(J0, K0, K1), partition(J)(J1, K2, K3),
           allToAll(J)(K0, <, K1), allToAll(J)(K2, <, K3),
           ∀:( J, x => K12(x) <-> (K1(x) | K2(x)) ),
           ∀:( J, x => K012(x) <-> (K0(x) | K1(x) | K2(x)) ),
           ∀:( J, (x,y) => K12sq(x,y) <-> (K12(x) & K12(y)) ),
           ∀:( J, (x,y) => P1(x,y) <-> ((K0(x) & K0(y)) | (K0(x) & K1(y)) | (K0(x) & K2(y)) | (K1(x) & K2(y)) | (K2(x) & K2(y))) ),
           ∀:( J, (x,y) => Q0(x,y) <-> ((K0(x) & K1(y)) | (K1(x) & K2(y))) )*/
         )
  } 
  
  
  def main(args: Array[String]) = BreakDown.main(args)

          
  import semantics.Prelude
  
  object BreakDown {
  
    import Prelude.{R,B}
    
    object InputPod {
      val program = TI("program")(
        
        TV("+") :: (R x R) ->: R ,
        < :: (J x J) ->: B , 
        
        K012   :: J ->: B ,
        K12    :: J ->: B ,
        K12sq  :: (J x J) ->: B ,
        P1     :: (J x J) ->: B ,
        Q0     :: (J x J) ->: B
      )
    }
    
    class APod(val J: Term) {
      import Prelude.{fix,∩,min,?,cons,nil}
      import ConsPod.`⟨ ⟩`
      
      val A = $TV("A")
      val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), TV("k"))

      val program = TI("program")(
        A :- (ψ ↦ fix(
            (θ :: ((J x J) ∩ <) ->: R) ↦: i ↦: j ↦: (
    
            min:@`⟨ ⟩`(
              min:@(k ↦
                    ( ((θ:@(i, k)) + (θ:@(k, j)))/*((θ:@(i, k)) + (θ:@(k, j)) + (w:@(i, k, j)))*/ -: TV("item") )
                  )
              ,
              ψ:@(i, j)
            )
            
          ) -: f )
        )
      )
    }
    
    object APod {
      def apply(J: Term) = new APod(J)
    }
    
    class BPod(J0: Term, J1: Term) {
      import Prelude._
      
      val B = $TV("B")
      val P = $TV("▜")
      
      val program = TI("program")(
        B :- ω( /::(
          ℐ :: (? x J0 x J0) -> ?,
          (TI("↦")(
            θ :: ((J x J) ∩ P ∩ <) ->: R , i , j ,
    
            min:@
            (
              cons:@(
                (min:@ 
                  (k ↦
                    ( ((θ:@(i, k)) + (θ:@(k, j)))/*((θ:@(i, k)) + (θ:@(k, j)) + (w:@(i, k, j)))*/ -: TV("item") )
                  )
                ),
                cons:@(
                  (θ:@(i, j)),
                  nil
                )
              )
            )
            
          ).foldRight -: f) :: (? x J0 x J1) -> ?,
          ℐ :: (? x J1 x J1) -> ?
      ) ) )
      
      def decl = new Declaration(P) where List(
          (P <-> (i ↦ (j ↦ ((J0(i) & J0(j)) | (J0(i) & J1(j)) | (J1(i) & J0(j))))))
        )
    }
    
    object BPod {
      def apply(J0: Term, J1: Term) = new BPod(J0, J1)
    }
    
    class CPod(J0: Term, J1: Term, J2: Term) {
      import semantics.Prelude._
      
      val C = $TV("C")
      val P = $TV("▚")
      val (θ, i, j, k) = ($TV("θ"), $TV("i"), $TV("j"), $TV("k"))
      val (item, compute) = ($TV("item"), $TV("compute"))
      
      val program =
        TV("program")(
            P :: ((J x J) -> B),
            w :: ((J x J x J) -> R),
            C :- ((θ ↦ (i ↦ (j ↦ (min :@ (k ↦ ( item :- ((θ :@ (i, k)) + (θ :@ (k, j)) + (w :@ (i, k, j)))))))))
             :: ((((J x J) ∩ P) -> R) ->: J0 ->: J2 ->: R))
        )
        
      val decl = new Declaration(P) where List(
          (P <-> (i ↦ (j ↦ ((J0(i) & J1(j)) | (J1(i) & J2(j))))))
        )
    }
    
    object CPod {
      def apply(J0: Term, J1: Term, J2: Term) = new CPod(J0, J1, J2)
    }
        
  
    val L0 = TS("L₀")
    val L1 = TS("L₁")
    val L2 = TS("L₂")
    val L3 = TS("L₃")
    val L4 = TS("L₄")
    val L5 = TS("L₅")
    val * = TI("*")
    
    def main(args: Array[String]): Unit = {
      import semantics.Domains._
      import semantics.Prelude._
      
      
      implicit val scope = new Scope
      scope.sorts.declare(J)
      scope.sorts.declare(J0 :<: J)
      scope.sorts.declare(J1 :<: J)
      scope.sorts.declare(K0 :<: J0)
      scope.sorts.declare(K1 :<: J0)
      scope.sorts.declare(K2 :<: J1)
      scope.sorts.declare(K3 :<: J1)
      scope.sorts.declare(L0 :<: K0)
      scope.sorts.declare(L1 :<: K0)
      scope.sorts.declare(L2 :<: K1)
      scope.sorts.declare(L3 :<: K1)
      scope.sorts.declare(L4 :<: K2)
      scope.sorts.declare(L5 :<: K2)
      scope.sorts.declare(N)
      scope.sorts.declare(R)

      scope.sorts.cork()


      implicit val env = new Environment(scope, Map())
      
      rewriteA
    }
    
    
    import syntax.transform.Extrude
    import semantics.pattern.SimplePattern 
    import synth.tactics.Rewrite.{Rewrite,instantiate}
    import synth.pods.{SlicePod,StratifyPod,StratifyReducePod,MinDistribPod,MinAssocPod}
    import semantics.TypedLambdaCalculus.{simplify,pullOut}
    import report.console.Console.display
    import syntax.Piping._

    def instapod(it: Term)(implicit scope: Scope) = instantiate(it)._2
    def instapod(it: Pod)(implicit scope: Scope) = new Instantiated(it)

    def rewriteA(implicit env: Environment, scope: Scope) {
      import Prelude.{?,ω,nil}
      val (_, tA) = instantiate(APod(J).program)
      val A = tA
      
      val extrude = Extrude(Set(I("/")))
      def ctx(A: Term, t: Term) = TypedLambdaCalculus.context(A, t)

      //display(A)
      
      val f = (A :/ "f").subtrees(1)
      val (_, slicef) = instantiate(SlicePod(f, List(J0 x J0, J0 x J1, J1 x J1) map (? x _)))
      for (A <- Rewrite(slicef)(A)) {
        println(s"A  ===  ${A toPretty}")
        val ex = extrude(A) |-- display
        // Stratify  🄰
        val strat = SimplePattern(fix(* :- `...`(ex :/ "🄰"))) find A map (x => StratifySlashPod(x(*), ex :/ "🄰", ctx(A, ex :/ "🄰")("ψ"))) map instapod
        for (A <- Rewrite(strat)(A)) {
          val ex = extrude(A) |-- display
          // Stratify  🄰
          val strat = SimplePattern(fix(* :- `...`(ex :/ "🄰"))) find A map (x => StratifySlashPod(x(*), ex :/ "🄰", ctx(A, ex :/ "🄰")("ψ"))) map instapod
          for (A <- Rewrite(strat)(A)) {
            val ex = extrude(A) |-- display
            val A0 = instapod(new APod(J0).program)
            for (target <- SimplePattern(fix(* :- ?)) find A0 flatMap (x => TypedLambdaCalculus.pullOut(A0, x(*)))) {
              extrude(target) |-- display
            }
          }
        }
      }
    }
    
    def rewriteB(implicit env: Environment, scope: Scope) {
      import Prelude.{?,ω,min,cons}
      val (vassign, tB) = instantiate(BPod(J0, J1).program)
      val B = tB
      
      val extrude = Extrude(Set(I("/")))

      //display(B)
      
      import syntax.Piping._
      
      val ex = extrude(B) |-- display
      
      val f = (B :/ "f").subtrees(1)
      // Slice  f  ? x [ K₀, K₁ ] x [ K₂, K₃ ]
      val slicef = SlicePod(f, List(K0 x K2, K0 x K3, K1 x K2, K1 x K3) map (? x _)) |> instapod
      for (B <- Rewrite(slicef)(B)) {
        val ex = extrude(B) |-- display
        // Stratify  🄳 :: ? -> (K₁ x K₂) -> ?   [ K₁ x K₁, K₂ x K₂ ]
        val strat = SimplePattern(ω(* :- /::(`...`))) find B map
                    (tier => StratifyPod(tier(*), ex :/ "🄳", List(K1 x K1, K2 x K2) map (? x _))) map instapod
        for (B <- Rewrite(strat)(B)) {
          val ex = extrude(B) |-- display
          // Stratify  🄲 :: ? -> (K₀ x K₂) -> ?   [ K₀ x K₀, K₀ x K₁, K₁ x K₂, K₂ x K₂ ]
          val strat = SimplePattern(ω(* :- /::(`...`))) find B filter (_(*).hasDescendant(ex :/ "🄲")) map
                      (tier => StratifyPod(tier(*), ex :/ "🄲", List(K0 x K0, K0 x K1, K1 x K2, K2 x K2) map (? x _))) map instapod
          for (B <- Rewrite(strat)(B)) {
            val ex = extrude(B) |-- display
            // Stratify  🄴 :: ? -> (K₁ x K₃) -> ?   [ K₁ x K₁, K₁ x K₂, K₂ x K₃, K₃ x K₃ ]
            val strat = SimplePattern(ω(* :- /::(`...`))) find B filter (_(*).hasDescendant(ex :/ "🄴")) map
                        (tier => StratifyPod(tier(*), ex :/ "🄴", List(K1 x K1, K1 x K2, K2 x K3, K3 x K3) map (? x _))) map instapod
            for (B <- Rewrite(strat)(B) map simplify) {
              val ex = extrude(B) |-- display
              // Slice  🄱 ... ( k ↦ ? )  [ K₁, K₂, K₃ ]
              //        🄲 ... ( k ↦ ? )  [ K₀, K₁, K₂ ]
              val slicekf = (SimplePattern(k ↦ ?) find (ex :/ "🄱") map 
                             (x => SlicePod(x.subterm, List(K1, K2, K3)))) ++
                            (SimplePattern(k ↦ ?) find (ex :/ "🄲") map 
                             (x => SlicePod(x.subterm, List(K0, K1, K2)))) |>> instapod
              for (B <- Rewrite(slicekf)(B)) {
                // MinDistrib
                val mindistkfs = SimplePattern(min :@ (* :- /::(`...`))) find B map 
                                 (x => MinDistribPod(x(*).split)) map instapod
                for (B <- Rewrite(mindistkfs)(B)) {
                  val extrude = Extrude(Set(I("/"), cons.root))
                  // MinAssoc
                  val minassockfs = SimplePattern(min :@ (* :- ?)) find B flatMap (_(*) |> `⟨ ⟩?`) map
                                    (MinAssocPod(_)) filter (x => x.subtrees(0) != x.subtrees(1)) map instapod
                  for (B <- Rewrite(minassockfs)(B)) {
                    val ex = extrude(B) |-- display
                    // Stratify  🄸,🄺 from 🄱
                    //           🄽,🄿 from 🄲
                    /*
                    val letout = List(StratifyReducePod(ex :/ "🄱" subtrees 0, ex :/ "🄸"),
                                      StratifyReducePod(ex :/ "🄲" subtrees 0, ex :/ "🄽")) |>> instapod
                                      */
                    /*
                    val strat = List(StratifyReducePod(ex :/ "🄱" subtrees 0, List(ex :/ "🄸", ex :/ "🄺")),
                                     StratifyReducePod(ex :/ "🄲" subtrees 0, List(ex :/ "🄽", ex :/ "🄿"))) map instapod
                    for (B <- Rewrite(strat)(B)) {
                      val ex = extrude(B) |-- display
                    }
                    */
                  }
                }
              }
            }
          }
        }
      }
    }
  
  
    def rewriteC(implicit env: Environment, scope: Scope) {
      import semantics.Prelude.{cons,?,min}
      
      val (vassign, tC) = instantiate(CPod(K0, K1, K2).program)
      val C = tC
      
      //display(C)
      
      println(s"C  ===  ${C toPretty}")
      
      val extrude = Extrude(Set(I("/"), cons.root))
      
      // Slice  ( k ↦ ? )  [ L2, L3 ]
      for (kf <- SimplePattern(k ↦ ?) find C) {
        val (vassign1, slicekf) = instantiate(SlicePod(kf.subterm, List(L2, L3)))//, vassign)
        for ((k,v) <- vassign1)
          println(s"$k   $v")
        //val env1 = TypeTranslation.decl(scope, vassign1)
        //proveEquality(slicekf.subtrees(0), slicekf.subtrees(1), vassign1)(env1)//Map())
        
        for (C <- Rewrite(slicekf)(C)) {
          println(s"C  ===  ${C toPretty}")
          // MinDistrib  ( min  /(...) )
          for (smallkfs <- SimplePattern(min :@ (* :- /::(`...`))) find C) {
            val (_, mindistkfs) = instantiate(MinDistribPod(smallkfs(*).split))//, vassign)
            for (C <- Rewrite(mindistkfs)(C)) {
              println(s"C  ===  ${C toPretty}")
              // Slice  ( i ↦ ? )  [ L0, L1 ] x [ L4, L5 ]
              for (if_ <- SimplePattern(i ↦ ?) find C) {
                val (_, sliceif) = instantiate(SlicePod(if_.subterm, List(L0 x L4, L0 x L5, L1 x L4, L1 x L5)))//, vassign)
                for (C <- Rewrite(sliceif)(C)) {
                  println(s"C  ===  ")
                  display(extrude(C))
                  for (kf <- SimplePattern(min :@ (k ↦ ?)) find C; x <- pullOut(C, kf.subterm)) {
                    println(s"${x toPretty} :: ${env typeOf_! x toPretty}")
                    //display(x)
                  }
                }
                //display(tC :/ "C")
              }
            }
          }
        }
      }
      
      
    }
      
  
  }


}