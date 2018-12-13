
package examples

import java.io.{BufferedReader, FileReader}
import com.mongodb.{BasicDBList, DBObject, BasicDBObject}
import com.mongodb.util.JSON
import report.{AppendLog, DevNull, FileLog}
import report.data.{SerializationContainer, Rich, DisplayContainer}
import semantics.TypedScheme.TermWithHole
import semantics.transform.Explicate
import syntax.{Formula, Tree, Identifier}
import semantics._
import semantics.TypeTranslation.Declaration
import semantics.TypeTranslation.Environment
import semantics.TypeTranslation.Declaration
import syntax.transform.ExtrudedTerms
import synth.pods.ConsPod.`⟨ ⟩?`
import synth.pods._
import ui.CLI
import synth.engine.CollectStats


object Paren {
  
  import syntax.AstSugar._
  import semantics.Domains._
  import semantics.Prelude._
  
  val J  = TS("J")
  val J0 = TS("J₀")
  val J1 = TS("J₁")
  val K0 = TS("K₀")
  val K1 = TS("K₁")
  val K2 = TS("K₂")
  val K3 = TS("K₃")
  val L0 = TS("L₀")
  val L1 = TS("L₁")
  val L2 = TS("L₂")
  val L3 = TS("L₃")
  val L4 = TS("L₄")
  val L5 = TS("L₅")

  val scope = new Scope
  scope.sorts.declare(N)
  scope.sorts.declare(R)
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
  
  scope.sorts.cork()

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
          θ :: ((J x J) ∩ <) ->: R , i , j ,
  
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

    TypeTranslation.subsorts(scope) /*++ TypeTranslation.decl(scope, Map(/*< ~> (J ->: J ->: B), succ ~> (J ->: J ->: B)*/)) */ where
         ( //transitive(J)(<), antisymm(J)(<),
           //∀:( J, (x,y,z) => succ(x,z) -> (<(x,z) & ~(<(x,y) & <(y,z))) )
         //  compl(J)(J0, J1), allToAll(J)(J0, <, J1) /*, ∀:( J, x => ~T(newbot)(x) ) */
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

    import ConsPod.`⟨ ⟩`

    class APod(val J: Term) extends Pod {
      import Prelude.{fix,min,?}

      val A = $TV("A")
      val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), TV("k"))

      override val program = TI("program")(
        A :- ((ψ :: ((J x J) ∩ <) ->: R) ↦ fix(
            (θ :: ((J x J) ∩ <) ->: R) ↦: i ↦: j ↦: (
    
            min:@`⟨ ⟩`(
              min:@(k ↦
                    ( ((θ:@(i, k)) + (θ:@(k, j)) + (w:@(i, k, j))) -: TV("item") )
              ),
              ψ:@(i, j)
            )
            
          ) -: f :: (? ->: ((J x J) ∩ <) ->: ?) )
        )
      )
    }
    
    object APod {
      def apply(J: Term) = new APod(J)
    }
    
    class BPod(J0: Term, J1: Term) extends Pod {
      import Prelude._
      
      val B = $TV("B")
      val P = $TV("▜")

      val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), TV("k"))

      override val program = TI("program")(
        B :- (ψ ↦ fix(
          /::(
            $TV ↦ ψ :: ? ->: (J0 x J0) ->: ?,
            (θ :: ((J x J) ∩ <) ->: R) ↦: i ↦: j ↦: (
              min:@`⟨ ⟩`(
                min:@(k ↦
                  ( ((θ:@(i, k)) + (θ:@(k, j)) + (w:@(i, k, j))) -: TV("item") )
                ),
                ψ:@(i, j)
              )
            ) -: f :: ? ->: (J0 x J1) ->: ?,
            $TV ↦ ψ :: ? ->: (J1 x J1) ->: ?
          )
      ) ) )
      /*
      def decl = new Declaration(P) where (
          P <-> (i ↦ (j ↦ ((J0(i) & J0(j)) | (J0(i) & J1(j)) | (J1(i) & J0(j)))))
        )*/
    }
    
    object BPod {
      def apply(J0: Term, J1: Term) = new BPod(J0, J1)
    }
    
    class CPod(J0: Term, J1: Term, J2: Term) extends Pod {
      import semantics.Prelude._
      
      val C = $TV("C")
      val P = $TV("▚")
      val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), TV("k"))

      override val program = Prelude.program(
          ψ ↦ /::(
            ψ :: (J0 x J1) ->: ?,
            i ↦: j ↦: (
              min:@`⟨ ⟩`(
                min:@((k :: J1) ↦
                    (( ((ψ:@(i, k)) + (ψ:@(k, j)) + (w:@(i, k, j))) ) /*|! (<(i, k) & <(k, j))*/)
                    ),
                ψ:@(i, j)
              )
            ) :: (J0 x J2) ->: R,
            ψ :: (J1 x J2) ->: ?
          )
      )

      /*
      val decl = new Declaration(P) where List(
          (P <-> (i ↦ (j ↦ ((J0(i) & J1(j)) | (J1(i) & J2(j))))))
        )*/
    }
    
    object CPod {
      def apply(J0: Term, J1: Term, J2: Term) = new CPod(J0, J1, J2)
    }
        
  
    val * = TI("*")
    
    def main(args: Array[String]): Unit = {
      ui.Config.tae(args)
      new Interpreter()(scope, env).executeFile(ui.Config.config.filename())
    }
    
    import syntax.transform.Extrude
    import semantics.pattern.SimplePattern 
    import synth.tactics.Rewrite.{Rewrite,instantiate}
    import synth.pods.{StratifyReducePod,ReduceDistribPod,ReduceAssocPod}
    import synth.tactics.SlicePod
    import semantics.TypedLambdaCalculus.{pullOut}
    import report.console.Console.{display,sdisplay}
    import syntax.Piping._

    import synth.engine.TacticApplicationEngine.{instapod, fixer, fixee, ctx, slasher}

    def emit(term: Term)(implicit scope: Scope) = Explicate.explicateHoist(term)

    def preformat(doc: Map[String, AnyRef], extrude: Extrude) = doc get "term" match {
      case Some(Term_:(term)) => doc - "term" + ("text" -> sdisplay(extrude(term))) + ("term" -> term)
      case _ => doc
    }

    def rewriteA(implicit env: Environment, scope: Scope) {
      import Prelude.?
      val (_, tA) = instantiate(APod(J).program)
      val A = tA
      
      val extrude = Extrude(Set(I("/")))

      val outf = new FileLog(new java.io.File("Paren-A.json"), new DisplayContainer)

      val ex = extrude(A) |-- display

      outf += preformat(Map("program" -> "A[J]", "style" -> "loop", "term" -> emit(A)), extrude)

      val cert = false

      val f = (A :/ "f").subtrees(1)
      val slicef = SlicePod(f, List(J0 x J0, J0 x J1, J1 x J1) map (? x _)) |> instapod
      if (cert) invokeProver(List(), slicef.obligations.conjuncts)
      for (A <- Rewrite(slicef)(A)) {
        val ex = extrude(A) |-- display
        // Stratify  🄰
        val strat = SimplePattern(fix(* :- `...`(ex :/ "🄰"))) find A map (x => StratifySlashPod(x(*), ex :/ "🄰", ctx(A, ex :/ "🄰")("ψ"))) map instapod
        if (cert) invokeProver(List(), strat flatMap (_.obligations.conjuncts))
        for (A <- Rewrite(strat)(A)) {
          val ex = extrude(A) |-- display
          // Stratify  🄱
          val strat = SimplePattern(fix(* :- `...`(ex :/ "🄱"))) find A map (x => StratifySlashPod(x(*), ex :/ "🄱", ctx(A, ex :/ "🄱")("ψ"))) map instapod
          if (cert) invokeProver(List(), strat flatMap (_.obligations.conjuncts))
          for (A <- Rewrite(strat)(A)) {
            val ex = extrude(A) |-- display
            def equivQuadrant(lhs: Term, rhs: Term) {
              env.typeOf(lhs) match {
                case Some(x -> y) =>
                  invokeProver(List(), List(lhs =:= (rhs :: (? -> y))) |>> instapod)
                case _ =>
              }
            }
            if (cert) {
              val A0 = new APod(J0).program
              for (target <- SimplePattern(fix(* :- ?)) find A0 flatMap (x => TypedLambdaCalculus.pullOut(A0, x(*))))
                equivQuadrant(fixee(A, ex :/ "🄲"), target :@ ctx(A, ex :/ "🄲")("ψ"))
              val A1 = new APod(J1).program
              for (target <- SimplePattern(fix(* :- ?)) find A1 flatMap (x => TypedLambdaCalculus.pullOut(A1, x(*))))
                equivQuadrant(fixee(A, ex :/ "🄱"), target :@ ctx(A, ex :/ "🄱")("ψ"))
            }
            // Synths!
            val newA = TypedTerm.preserve(fixee(A, ex :/ "🄰"), TV("B[J₀,J₁]"))
            val newB = TypedTerm.replaceDescendant(fixee(A, ex :/ "🄱"), (ex :/ "🄱", TV("A[J₁]")))
            val newC = TypedTerm.replaceDescendant(fixee(A, ex :/ "🄲"), (ex :/ "🄲", TV("A[J₀]")))
            val synths = List( fixer(A, ex :/ "🄰") =:= (newA :@ ctx(A, ex :/ "🄰")("ψ")),
                               fixer(A, ex :/ "🄱") =:= (newB :@ ctx(A, ex :/ "🄱")("ψ")),
                               fixer(A, ex :/ "🄲") =:= (newC :@ ctx(A, ex :/ "🄲")("ψ")) )
            for (A <- Rewrite( synths ) apply (A)) {
              val ex = extrude(A) |-- display
              outf += preformat(Map("program" -> "A[J]", "style" -> "rec", "term" -> emit(A)), extrude)
            }
          }
        }
      }
    }

    def rewriteB(implicit env: Environment, scope: Scope) {
      import Prelude.{?,min,cons}
      val (vassign, tB) = instantiate(BPod(J0, J1).program)
      val B = tB
      
      val extrude = Extrude(Set(I("/")))

      val outf = new FileLog(new java.io.File("Paren-B.json"), new DisplayContainer)

      import syntax.Piping._
      
      val ex = extrude(B) |-- display
      outf += preformat(Map("program" -> "B[J₀,J₁]", "style" -> "loop", "term" -> emit(B)), extrude)

      val cert = false

      val f = (B :/ "f").subtrees(1)
      // Slice  f  ? x [ K₀, K₁ ] x [ K₂, K₃ ]
      val slicef = SlicePod(f, List(K0 x K2, K0 x K3, K1 x K2, K1 x K3) map (? x _)) |> instapod
      if (cert) invokeProver(List(), slicef.obligations.conjuncts)
      for (B <- Rewrite(slicef)(B)) {
        val ex = extrude(B) |-- display
        // Stratify  🄳 :: ? -> (K₁ x K₂) -> ?
        val strat = SimplePattern(fix(* :- `...`(ex :/ "🄳"))) find B map (x => StratifySlashPod(x(*), ex :/ "🄳", ctx(B, ex :/ "🄳")("ψ"))) map instapod
        if (cert) invokeProver(List(), strat flatMap (_.obligations.conjuncts))
        for (B <- Rewrite(strat)(B)) {
          val ex = extrude(B) |-- display
          // Stratify  🄲 :: ? -> (K₀ x K₂) -> ?
          val strat = SimplePattern(fix(* :- `...`(ex :/ "🄲"))) find B map (x => StratifySlashPod(x(*), ex :/ "🄲", ctx(B, ex :/ "🄲")("ψ"))) map instapod
          if (cert) invokeProver(List(), strat flatMap (_.obligations.conjuncts))
          for (B <- Rewrite(strat)(B)) {
            val ex = extrude(B) |-- display
            // Stratify  🄴 :: ? -> (K₁ x K₃) -> ?
            val strat = SimplePattern(fix(* :- `...`(ex :/ "🄴"))) find B map (x => StratifySlashPod(x(*), ex :/ "🄴", ctx(B, ex :/ "🄴")("ψ"))) map instapod
            if (cert) invokeProver(List(), strat flatMap (_.obligations.conjuncts))
            for (B <- Rewrite(strat)(B)) {
              val ex = extrude(B) |-- display
              // Slice  🄰 ... ( k ↦ ? )  [ K₀, K₁, K₂, K₃ ]
              //        🄱 ... ( k ↦ ? )  [ K₁, K₂, K₃ ]
              //        🄲 ... ( k ↦ ? )  [ K₀, K₁, K₂ ]
              val slicekf = (SimplePattern(k ↦ ?) find (ex :/ "🄰") map
                              (x => SlicePod(x.subterm, List(K0, K1, K2, K3)))) ++
                            (SimplePattern(k ↦ ?) find (ex :/ "🄱") map
                              (x => SlicePod(x.subterm, List(K1, K2, K3)))) ++
                            (SimplePattern(k ↦ ?) find (ex :/ "🄲") map
                              (x => SlicePod(x.subterm, List(K0, K1, K2)))) |>> instapod
              for (B <- Rewrite(slicekf)(B)) {
                // MinDistrib
                val mindistkfs = SimplePattern(min :@ (* :- /::(`...`))) find B map
                  (x => ReduceDistribPod(min, x(*).split)) map instapod
                for (B <- Rewrite(mindistkfs)(B)) {
                  val extrude = Extrude(Set(I("/"), cons.root))
                  // MinAssoc
                  val minassockfs = SimplePattern(min :@ (* :- ?)) find B flatMap (_(*) |> `⟨ ⟩?`) map
                                    (ReduceAssocPod(min, _)) filterNot (_.isTrivial) map instapod
                  for (B <- Rewrite(minassockfs)(B)) {
                    val ex = extrude(B) |-- display
                    def stratduce(A: Term, `.` : Term, subelements: List[Term]) =
                      SimplePattern(min:@(* :- ?)) find `.` flatMap (x => `⟨ ⟩?`(x(*)) map (elements =>
                        StratifyReducePod(TermWithHole.puncture(fixee(A,`.`), x.subterm), min, elements, subelements, ctx(A, `.`)("ψ"))))
                    val strat = stratduce(B, ex :/ "🄰", List("🄶", "🄹") map (ex :/ _)) ++
                                stratduce(B, ex :/ "🄱", List("🄼", "🄾") map (ex :/ _)) ++
                                stratduce(B, ex :/ "🄲", List("🅁", "🅃") map (ex :/ _)) |>> instapod
                    strat.head.obligations.conjuncts foreach { x =>
                      extrude(x) |-- display
                      for (n <- x.nodes) if (n.root == "θ" || n.root == "ψ") println(s" --  ${n toPretty} : ${env.typeOf_!(n) toPretty}")
                    }
                    if (cert) invokeProver(List(), strat flatMap (_.obligations.conjuncts))
                    for (B <- Rewrite(strat)(B)) {
                      val ex = extrude(B) |-- display
                      val strat = stratduce(B, ex :/ "🄰", List("🄸", "🄺") map (ex :/ _)) |>> instapod
                      if (cert) invokeProver(List(), strat flatMap (_.obligations.conjuncts))
                      for (B <- Rewrite(strat)(B)) {
                        val ex = extrude(B) |-- display

                        // This is such a hack @@@
                        def emulateSynth(subterm: Term, synthed: Term) = {
                          val newTerm = TypedTerm.replaceDescendant(fixee(B, subterm), (subterm, synthed))
                          fixer(B, subterm) =:= (newTerm :@ ctx(B, subterm)("ψ"))
                        }
                        val synths = List(emulateSynth(ex :/ "🄸", TV("B[K₀,K₃]")),
                                          emulateSynth(ex :/ "🄼", TV("C[K₀,K₂,K₃]")),
                                          emulateSynth(ex :/ "🄿", TV("C[K₀,K₁,K₃]")),
                                          emulateSynth(ex :/ "🅂", TV("B[K₁,K₃]")),
                                          emulateSynth(ex :/ "🅆", TV("C[K₁,K₂,K₃]")),
                                          emulateSynth(ex :/ "🅉", TV("B[K₀,K₂]")),
                                          emulateSynth(ex :/ "🄳̲", TV("C[K₀,K₁,K₂]")),
                                          emulateSynth(ex :/ "🄶̲", TV("B[K₁,K₂]"))
                        )
                        for (B <- Rewrite(synths) apply (B)) {
                          val ex = extrude(B) |-- display
                          outf += preformat(Map("program" -> "B[J₀,J₁]", "style" -> "rec", "term" -> emit(B)), extrude)
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  
  
    def rewriteC(implicit env: Environment, scope: Scope) {
      import semantics.Prelude.{cons, ?, min}

      val (vassign, tC) = instantiate(CPod(K0, K1, K2).program)
      val C = tC

      val outf = new FileLog(new java.io.File("Paren-C.json"), new DisplayContainer)
      val logf = new FileLog(new java.io.File("/tmp/bell.json"), new DisplayContainer)

      val extrude = Extrude(Set(I("/"), cons.root))

      val ex = extrude(C) |-- display
      outf += preformat(Map("program" -> "C[K₀,K₁,K₂]", "style" -> "loop", "term" -> emit(C)), extrude)

      def slasher(A: Term, f: Term) =
        (SimplePattern(/::(`...`(f))) find A head) |> (_.subterm)

      // Slice  ( i ↦ ? )  [ L0, L1 ] x [ L4, L5 ]
      val sliceijf = SimplePattern(i ↦ ?) find C map (x => SlicePod(x.subterm, List(L0 x L4, L0 x L5, L1 x L4, L1 x L5))) map instapod
      for (C <- Rewrite(sliceijf)(C)) {
        val ex = extrude(C) |-- display
        // Let  🄰
        val let = LetSlashPod(slasher(C, ex :/ "🄰"), ex :/ "🄰", ctx(C, ex :/ "🄰")("ψ")) |> instapod
        for (C <- Rewrite(let)(C)) {
          val ex = extrude(C) |-- display
          // Let  🄰
          val let = LetSlashPod(slasher(C, ex :/ "🄰"), ex :/ "🄰", ctx(C, ex :/ "🄰")("ψ")) |> instapod
          for (C <- Rewrite(let)(C)) {
            val ex = extrude(C) |-- display
            // Let  🄰
            val let = LetSlashPod(slasher(C, ex :/ "🄰"), ex :/ "🄰", ctx(C, ex :/ "🄰")("ψ")) |> instapod
            for (C <- Rewrite(let)(C)) {
              val ex = extrude(C) |-- display
              // Slice  ( k ↦ ? )  [ L2, L3 ]
              val slicekf = SimplePattern(k ↦ ?) find C map (x => SlicePod(x.subterm, List(L2, L3))) map instapod
              for (C <- Rewrite(slicekf)(C)) {
                val ex = extrude(C) |-- display |-- (logf += Rich.display(_))
                // MinDistrib  ( min  /(...) )
                val mindistkfs = SimplePattern(min :@ (* :- /::(`...`))) find C map
                    (x => ReduceDistribPod(min, x(*).split)) map instapod
                for (C <- Rewrite(mindistkfs)(C)) {
                  val ex = extrude(C) |-- display
                  // MinAssoc
                  val minassockfs = SimplePattern(min :@ (* :- ?)) find C flatMap (_(*) |> `⟨ ⟩?`) map
                      (ReduceAssocPod(min, _)) filterNot (_.isTrivial) map instapod
                  for (C <- Rewrite(minassockfs)(C)) {
                    val ex = extrude(C) |-- display

                    def letduce(A: Term, `.` : Term, subelements: List[Term]) =
                      SimplePattern(min:@(* :- ?)) find `.` flatMap (x => `⟨ ⟩?`(x(*)) map (elements =>
                        LetReducePod(TermWithHole.puncture(slasher(A, `.`), x.subterm), min, elements, subelements, ctx(A, `.`)("ψ"))))

                    val let = letduce(C, ex :/ "🄰", List("🄴", "🄶") map (ex :/ _)) ++
                              letduce(C, ex :/ "🄱", List("🄷", "🄹") map (ex :/ _)) ++
                              letduce(C, ex :/ "🄲", List("🄺", "🄼") map (ex :/ _)) ++
                              letduce(C, ex :/ "🄳", List("🄽", "🄿") map (ex :/ _)) map instapod
                    for (C <- Rewrite(let)(C)) {
                      val ex = extrude(C) |-- display |-- (logf += Rich.display(_))
                      // This is such a hack @@@
                      def emulateSynth(subterm: Term, synthed: Term) = {
                        import TypedTerm.typeOf_!
                        val ψ = ctx(C, subterm)("ψ")
                        val newTerm = TypedTerm(synthed, typeOf_!(ψ) -> typeOf_!(subterm))
                        subterm =:= (newTerm :@ ψ)
                      }
                      val synths = List( emulateSynth(ex :/ "🄰", TV("C[L₁,L₃,L₅]")),
                                         emulateSynth(ex :/ "🄱", TV("C[L₁,L₂,L₅]")),
                                         emulateSynth(ex :/ "🄲", TV("C[L₁,L₃,L₄]")),
                                         emulateSynth(ex :/ "🄳", TV("C[L₁,L₂,L₄]")),
                                         emulateSynth(ex :/ "🄴", TV("C[L₀,L₃,L₅]")),
                                         emulateSynth(ex :/ "🄵", TV("C[L₀,L₂,L₅]")),
                                         emulateSynth(ex :/ "🄶", TV("C[L₀,L₃,L₄]")),
                                         emulateSynth(ex :/ "🄷", TV("C[L₀,L₂,L₄]"))
                      )
                      for (C <- Rewrite(synths) apply (C)) {
                        val ex = extrude(C) |-- display
                        outf += preformat(Map("program" -> "C[K₀,K₁,K₂]", "style" -> "rec", "term" -> emit(C)), extrude)
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }



    import synth.engine.TacticApplicationEngine
    import synth.proof.{Prover, Assistant}
    
    trait InvokeProver extends TacticApplicationEngine {
      override lazy val prover: Prover = prover(List())
        
      def prover(pods: Iterable[Pod]) = {
        import synth.proof._
  
        implicit val env = Paren.env
        implicit val scope = env.scope
  
        val toR = TotalOrderPod(R)
        val toJ = TotalOrderPod(J, <)
        val idxJ = new IndexArithPod(J, toJ.<, succ)
        val partJ = PartitionPod(J, <, J0, J1)
        val partJ0 = PartitionPod(J0, <, K0, K1)
        val partJ1 = PartitionPod(J1, <, K2, K3)
        val partK0 = PartitionPod(K0, <, L0, L1)
        val partK1 = PartitionPod(K1, <, L2, L3)
        val partK2 = PartitionPod(K2, <, L4, L5)
        val offsets = List(J0, J1, K0, K1, K2, K3 /*, L0, L1, L2, L3, L4, L5*/) map (OffsetsPod(_, idxJ))
        val nilNR = NilPod(N, R)
        val minJR = MinPod(J, R, toR.<)
        val minNR = MinPod(N, R, toR.<)
  
        new Prover(List(NatPod, TuplePod, toR, toJ, idxJ, partJ, partJ0, partJ1, partK0, partK1, partK2, minJR, minNR, nilNR) /*++ offsets*/ ++ pods, verbose = Prover.Verbosity.ResultsOnly)
      }
      override def invokeProver(pod: Pod) { invokeProver(List(), pod.obligations.conjuncts, List(pod)) }
      
      def invokeProver(assumptions: List[Term], goals: List[Term], pods: List[Pod]=List()) {
        (new Assistant()(env)).invokeProver(assumptions, goals, new SimplePattern(min :@ ?))(prover(pods))
      }    
    }
    
    class Interpreter(implicit scope: Scope, env: Environment) extends TacticApplicationEngine with InvokeProver with CollectStats {
      import TacticApplicationEngine._

      override def pods(implicit s: State): PartialFunction[(Term, List[Term]), Pod] = {
        case (L("A"), List(~(j))) => APod(j)
        case (L("B"), List(~(j0), ~(j1))) => BPod(j0, j1)
        case (L("C"), List(~(j0), ~(j1), ~(j2))) => CPod(j0, j1, j2)
      }

      val A = TV("A")
      val B = TV("B")
      val C = TV("C")
      val P1 = TV("P₁")
      val P2 = TV("P₂")
      val P3 = TV("P₃")
      override val prototypes = Map(A → (A:@(? ∩ P1)), B → (B:@(? ∩ P1, ? ∩ P2)), C → (C:@(? ∩ P1, ? ∩ P2, ? ∩ P3)))
    }


    def invokeProver(assumptions: Iterable[Term], goals: Iterable[Term], pods: Iterable[Pod]=List(), logf: AppendLog=DevNull): Unit = {
      new Interpreter()(scope, env).invokeProver(assumptions.toList, goals.toList, pods.toList)
      /*
      import synth.proof._
      import synth.pods._
      import semantics.Trench

      val extrude = Extrude(Set(I("/"), cons.root))

      for (goal <- goals) logf += Map("term" -> goal,
        "display" -> Rich.display(extrude(goal) |-- report.console.Console.display))

      implicit val env = Paren.env
      implicit val scope = env.scope

      val a = new Assistant
      val p = prover(pods)
      
      val commits =
        for (goals <- goals map (List(_))) yield {
        //for (goals <- List(goals)) yield {
          val igoals = goals map a.intros

          import semantics.pattern.SimplePattern
          val t = new p.Transaction
          val switch = t.commonSwitch(new p.CommonSubexpressionElimination(igoals, new SimplePattern(min :@ ?)))

          t.commit(assumptions map a.simplify map t.prop, igoals map (switch(_)) map a.simplify map t.goal)
        }

      val results = commits reduce (_ ++ _)

      println("=" * 80)
      Trench.display(results, "◦")

      /*
      val t = new p.Transaction
      val switch = t.commonSwitch(new p.CommonSubexpressionElimination(goals, new SimplePattern(min :@ ?)))

      val results =
        t.commit(assumptions map a.simplify map t.prop, goals map (switch(_)) map a.intros map a.simplify map t.goal)

      println("=" * 80)
      Trench.display(results, "◦")*/

      if (!(results.toList forall (_.root == "valid"))) System.exit(1)*/
    }


  }


}