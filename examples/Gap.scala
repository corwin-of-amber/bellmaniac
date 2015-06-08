package examples

import syntax.AstSugar._
import semantics.Prelude._
import synth.pods.MinDistribPod.`⟨ ⟩`
import semantics.Scope
import semantics.TypeTranslation.Environment
import syntax.transform.Extrude
import synth.pods.SlashDistribPod
import synth.pods.SlashToReducePod



object Gap {
  
  val J = TS("J")
  val K = TS("K")
  val J0 = TS("J₀")
  val J1 = TS("J₁")
  val K0 = TS("K₀")
  val K1 = TS("K₁")
  
  val w = TV("w")
  val `w'` = TV("w'")
  val S = TV("S")
  
  val f = TV("f")
  
  def < = TV("<")
  val _1 = TI(1)
  
  val program = TI("program")(
      w :: ((K x K) ∩ <) -> R,
      `w'` :: ((J x J) ∩ <) -> R,
      S :: (J x K) -> R
    )
    
  class APod(val J: Term, val K: Term) {
    val A = $TV("A")
    val (θ, i, j, p, q) = ($TV("θ"), $TV("i"), $TV("j"), TV("p"), TV("q"))
    
    val program = TI("program")(
        A :- ω(
          ((θ :: (J x K) -> R) ↦: i ↦: j ↦: (min :@
            `⟨ ⟩`(
              (θ:@(i-_1, j-_1)) + (S:@(i,j)),
              min :@ (q ↦ ((θ:@(i,q)) + (w:@(q,j)))),
              min :@ (p ↦ ((θ:@(p,j)) + (`w'`:@(p,i)))),
              θ:@(i,j)
            )
          )) -: f
        )
      )
  }
  
  object APod {
    def apply(J: Term, K: Term) = new APod(J, K)
  }
  
  class BPod(val J: Term, val K0: Term, val K1: Term) {
    val B = $TV("B")
    val (θ, i, j, p, q) = ($TV("θ"), $TV("i"), $TV("j"), $TV("p"), $TV("q"))
    
    val program = TI("program")(
        B :- ω(
          (θ ↦: i ↦: j ↦: (min :@
            `⟨ ⟩`(
              (θ:@(i-_1, j-_1)) + (S:@(i,j)),
              min :@ (q ↦ ((θ:@(i,q)) + (w:@(q,j)))),
              min :@ (p ↦ ((θ:@(p,j)) + (w:@(p,i)))),
              θ:@(i,j)
            )
          )) :: ((J x K0) -> ?) -> ((J x K1) -> ?)
        )
      )
  }
  
  def main(args: Array[String]) = BreakDown.main(args)

  
  object BreakDown {
    
    def main(args: Array[String]): Unit = {
      import semantics.Domains._
      implicit val scope = new Scope
      scope.sorts.declare(R)
      scope.sorts.declare(N)
      scope.sorts.declare(J)
      scope.sorts.declare(K)

      scope.sorts.declare(J0 :<: J)
      scope.sorts.declare(J1 :<: J)
      scope.sorts.declare(K0 :<: K)
      scope.sorts.declare(K1 :<: K)
      
      implicit val env = new Environment(scope, Map())
      
      rewriteA
    }
    
    import syntax.transform.Extrude
    import semantics.pattern.SimplePattern 
    import synth.tactics.Rewrite.{Rewrite,instantiate,display}
    import synth.pods.{SlicePod,StratifyPod,StratifyReducePod,MinDistribPod,MinAssocPod}
    import semantics.TypedLambdaCalculus.{simplify,pullOut}
    import syntax.Piping._

    def instapod(it: Term)(implicit scope: Scope) = instantiate(it)._2
    val * = TI("*")
    val j = TV("j")
    val p = TV("p")
    val q = TV("q")
    
    def rewriteA(implicit env: Environment, scope: Scope) {
      val extrude = new Extrude(Set(I("/"), cons.root))

      def fixer(A: Term, q: Term) = SimplePattern(ω(?)) find A map (_.subterm) filter (_.hasDescendant(q)) head
      
      val A = instantiate(APod(J, K).program, instantiate(program)._1)._2
      val ex = extrude(A) |-- display
      // Slice  f  [ J₀, J₁ ] x [ K₀, K₁ ]
      val slicef = SlicePod(A :/ "f" subtrees 1, List(J0 x K0, J0 x K1, J1 x K0, J1 x K1) map (? x _)) |> instapod
      for (A <- Rewrite(slicef)(A)) {
        val ex = extrude(A) |-- display
        // Stratify  🄰
        val strat = StratifyPod(fixer(A, ex :/ "🄰") subtrees 0, ex :/ "🄰", List(? x J0 x K0)) |> instapod
        for (A <- Rewrite(strat)(A)) {
          val ex = extrude(A) |-- display
          // Stratify  🄰
          val strat = StratifyPod(fixer(A, ex :/ "🄰") subtrees 0, ex :/ "🄰", List(? x J0 x K0)) |> instapod
          for (A <- Rewrite(strat)(A)) {
            val ex = extrude(A) |-- display
            // Stratify  🄰
            val strat = StratifyPod(fixer(A, ex :/ "🄰") subtrees 0, ex :/ "🄰", List(? x J0 x K0)) |> instapod
            for (A <- Rewrite(strat)(A) map simplify) {
              val ex = extrude(A) |-- display
              // Slice  🄰 ... q ↦ ?  [ K₀, K₁ ]
              //               p ↦ ?  [ J₀, J₁ ]
              //               θ      [ J₀, J₁ ] x [ K₀, K₁ ]
              // Slice  🄱 ... p ↦ ?  [ J₀, J₁ ]
              //               θ      [ J₀, J₁ ] x ?
              // Slice  🄲 ... q ↦ ?  [ K₀, K₁ ]
              //                      ? x [ K₀, K₁ ]
              val slicea = (SimplePattern(q ↦ ?) find ex :/ "🄰" map (x => SlicePod(x.subterm, List(K0, K1)))) ++
                           (SimplePattern(p ↦ ?) find ex :/ "🄰" map (x => SlicePod(x.subterm, List(J0, J1)))) :+
                           (SlicePod((ex :/ "🄰") ? "θ", List(J0 x K0, J0 x K1, J1 x K0, J1 x K1)))
              val sliceb = (SimplePattern(p ↦ ?) find ex :/ "🄱" map (x => SlicePod(x.subterm, List(J0, J1)))) :+
                           (SlicePod((ex :/ "🄱") ? "θ", List(J0, J1) map (_ x ?)))
              val slicec = (SimplePattern(q ↦ ?) find ex :/ "🄲" map (x => SlicePod(x.subterm, List(K0, K1)))) :+
                           (SlicePod((ex :/ "🄲") ? "θ", List(K0, K1) map (? x _)))
              val slice = (slicea ++ sliceb ++ slicec) |>> instapod
              for (A <- Rewrite(slice)(A, SimplePattern(j ↦ (* :- ?)) find A map (_(*)))) {
                val ex = extrude(A) |-- display
                // SlashDistrib  ?⃞  ?⃞ ... /(...) :@ ?
                val dist = (ex.terminals flatMap (x => SimplePattern((* :- /::(`...`)) :@ ?) find x map (x → _(*))) map
                            { case (x, y) => SlashDistribPod(x, y) }) |>> instapod
                for (A <- Rewrite(dist)(A)) {
                  val ex = extrude(A) |-- display
                  // SlashToReduce  cons(/({...}), ?)  [min]
                  val s2m = (SimplePattern(cons:@(* :- /::(`...`))) find A map (x => SlashToReducePod(x(*).split(I("/")), min))) |>> instapod
                  for (A <- Rewrite(s2m)(A)) {
                    // MinDistrib
                    val mindist = (SimplePattern(min :@ (* :- /::(`...`))) find A map 
                                   (x => MinDistribPod(x(*).split))) |>> instapod
                    for (A <- Rewrite(mindist)(A)) {
                      // MinAssoc
                      val minassoc = (SimplePattern(min :@ (* :- ?)) find A flatMap (_(*) |> MinAssocPod.`⟨ ⟩?`) map
                                      (MinAssocPod(_)) filter (x => x.subtrees(0) != x.subtrees(1))) |>> instapod
                      for (A <- Rewrite(minassoc)(A)) {
                        val ex = extrude(A) |-- display
                        // Stratify  🄾, 🅁, 🅃  in  🄱
                        //           🅅, 🅇, 🄰̱  in  🄲
                        //           🄴, 🄼      in  🄰
                        val strat = List(StratifyReducePod(ex :/ "🄱" subtrees 0, List("🄾", "🅁", "🅃") map (ex :/ _)),
                                         StratifyReducePod(ex :/ "🄲" subtrees 0, List("🅅", "🅇", "🄰̱") map (ex :/ _)),
                                         StratifyReducePod(fixer(A, ex :/ "🄰") subtrees 0, List("🄴", "🄼") map (ex :/ _))) |>> instapod
                        for (A <- Rewrite(strat)(A)) {
                          val ex = extrude(A) |-- display
                          // Stratify  🄵, 🄸, 🄼  in  🄰
                          val strat = StratifyReducePod(fixer(A, ex :/ "🄰") subtrees 0, List("🄵", "🄸", "🄼") map (ex :/ _)) |> instapod
                          for (A <- Rewrite(strat)(A)) {
                            val ex = extrude(A) |-- display
                            // Stratify  🄶, 🄹, 🄻  in  🄰
                            val strat = StratifyReducePod(fixer(A, ex :/ "🄰") subtrees 0, List("🄶", "🄹", "🄻") map (ex :/ _)) |> instapod
                            for (A <- Rewrite(strat)(A) map simplify) {
                              val ex = extrude(A) |-- display
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
      }
    }
    
  }

}