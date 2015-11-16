package examples

import report.data.{Rich, DisplayContainer}
import syntax.AstSugar._
import syntax.Identifier
import syntax.transform.Extrude

import semantics._
import semantics.Prelude._
import semantics.TypeTranslation.Environment
import semantics.TypedScheme.TermWithHole
import synth.engine.TacticApplicationEngine

import synth.pods._
import synth.pods.ConsPod.{`⟨ ⟩`, `⟨ ⟩?`}

import report.FileLog
import synth.proof.{Prover, Assistant}


object Gap {
  
  val J = TS("J")
  val K = TS("K")
  val J0 = TS("J₀")
  val J1 = TS("J₁")
  val K0 = TS("K₀")
  val K1 = TS("K₁")
  val L0 = TS("L₀")
  val L1 = TS("L₁")
  val L2 = TS("L₂")
  val L3 = TS("L₃")
  val M0 = TS("M₀")
  val M1 = TS("M₁")
  val M2 = TS("M₂")
  val M3 = TS("M₃")

  val w = TV("w")
  val `w'` = TV("w'")
  val S = TV("S")
  
  val f = TV("f")

  def J_< = T(new Identifier("<", "variable", ns=J))
  def K_< = T(new Identifier("<", "variable", ns=K))
  val _1 = TI(1)
  
  val program = TI("program")(
      w :: ((K x K) ∩ K_<) -> R,
      `w'` :: ((J x J) ∩ J_<) -> R,
      S :: (J x K) -> R
    )
    
  class APod(val J: Term, val K: Term) extends Pod {
    val A = TI("A")
    val (ψ, θ, i, j, p, q) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), TV("p"), TV("q"))
    
    override val program = Prelude.program(
        A :- (ψ ↦ fix(
          ((θ :: (J x K) -> R) ↦: i ↦: j ↦: (min :@
            `⟨ ⟩`(
              ψ:@(i,j),
              (θ:@(i-_1, j-_1)) + (S:@(i,j)),
              min :@ (q ↦ ((θ:@(i,q)) + ((w :: ((K x K) ∩ K_<) ->: ?):@(q,j)))),
              min :@ (p ↦ ((θ:@(p,j)) + ((`w'` :: ((J x J) ∩ J_<) -> ?):@(p,i))))
            )
          )) -: f
        ))
      )
  }
  
  object APod {
    def apply(J: Term, K: Term) = new APod(J, K)
  }
  
  class BPod(val J: Term, val K0: Term, val K1: Term) extends Pod {
    val B = TI("B")
    val (ψ, θ, i, j, p, q) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), $TV("p"), $TV("q"))
    
    override val program = Prelude.program(
        B :- ψ ↦
          /::(
            ψ :: ((J x K0) -> R),
            (i ↦: j ↦: (min :@ `⟨ ⟩`(
              ψ:@(i,j),
              (ψ:@((i-_1)::J, (j-_1)::K0)) + (S:@(i,j)),
              min :@ ((q::K0) ↦ ((ψ:@(i,q)) + (w:@(q,j))))
            ))) :: ((J x K1) -> R)
          )
        )
  }
  
  object BPod {
    def apply(J: Term, K0: Term, K1: Term) = new BPod(J, K0, K1)
  }

  class CPod(val J0: Term, val J1: Term, val K: Term) extends Pod {
    val C = TI("C")
    val (ψ, θ, i, j, p, q) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), $TV("p"), $TV("q"))

    override val program = Prelude.program(
      C :- ψ ↦
          /::(
            ψ :: ((J0 x K) -> R),
            (i ↦: j ↦: (min :@ `⟨ ⟩`(
              ψ:@(i,j),
              (ψ:@((i-_1)::J0, (j-_1)::K)) + (S:@(i,j)),
              min :@ ((p::J0) ↦ ((ψ:@(p,j)) + (`w'`:@(p,i))))
            ))) :: ((J1 x K) -> R)
          )
    )
  }

  object CPod {
    def apply(J0: Term, J1: Term, K: Term) = new CPod(J0, J1, K)
  }


  import semantics.Domains._

  implicit val scope = new Scope(R, N, J, K)(
    J0 :<: J, J1 :<: J, K0 :<: K, K1 :<: K,
    L0 :<: J0, L1 :<: J0, L2 :<: J1, L3 :<: J1,
    M0 :<: K0, M1 :<: K0, M2 :<: K1, M3 :<: K1)

  implicit val env = TypeTranslation.subsorts(scope)

  def main(args: Array[String]) = BreakDown.main(args)

  
  object BreakDown {
    
    def main(args: Array[String]): Unit = {
      val filename = args.headOption getOrElse "/tmp/synopsis.json"
      new Interpreter().executeFile(filename)
    }

    class Interpreter(implicit scope: Scope) extends TacticApplicationEngine {
      import TacticApplicationEngine._

      override def pods(implicit s: State) = {
        case (L("A"), List(~(j), ~(k))) => APod(j, k)
        case (L("B"), List(~(j), ~(k0), ~(k1))) => BPod(j, k0, k1)
        case (L("C"), List(~(j0), ~(j1), ~(k))) => CPod(j0, j1, k)
      }

      def prover(pods: List[Pod]) = {
        import synth.pods._
        
        val toR = TotalOrderPod(R)
        val toJ = TotalOrderPod(J, J_<)
        val toK = TotalOrderPod(K, K_<)
        val idxJ = IndexArithPod(J, toJ.<)
        val idxK = IndexArithPod(K, toK.<)
        val partJ = PartitionPod(J, toJ.<, J0, J1)
        val partK = PartitionPod(K, toK.<, K0, K1)
        val partJ0 = PartitionPod(J0, toJ.<, L0, L1)
        val partJ1 = PartitionPod(J1, toJ.<, L2, L3)
        val partK0 = PartitionPod(K0, toK.<, M0, M1)
        val partK1 = PartitionPod(K1, toK.<, M2, M3)
        val minJR = MinPod(J, R, toR.<)
        val minKR = MinPod(K, R, toR.<)
        val minNR = MinPod(N, R, toR.<)

        new Prover(List(NatPod, TuplePod, toR, toJ, toK, idxJ, idxK, partJ, partK, partJ0, partJ1, partK0, partK1, minJR, minKR, minNR), Prover.Verbosity.ResultsOnly)
      }

      override lazy val prover: Prover = prover(List())
      
      override def invokeProver(pod: Pod) { invokeProver(List(), pod.obligations.conjuncts, List(pod)) }
      def invokeProver(assumptions: List[Term], goals: List[Term], pods: List[Pod]=List()) {
        import syntax.Piping._

        for (goal <- goals) extrude(goal) |> { report.console.Console.display
          //ex => logf += Map("term" -> goal, "display" -> Rich.display(ex))
        }

        println("· " * 25)

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

        if (!(results.toList forall (_.root == "valid"))) System.exit(1)

        println("=" * 80)  // QED!
      }
    }


    import syntax.transform.Extrude
    import semantics.pattern.SimplePattern 
    import synth.tactics.Rewrite.{Rewrite,instantiate}
    import synth.pods.{StratifyReducePod,ReduceDistribPod,ReduceAssocPod}
    import synth.tactics.SlicePod
    import syntax.Piping._
    import report.console.Console.display

    import TacticApplicationEngine.{instapod, fixer, fixee, ctx}

    val * = TI("*")
    val j = TV("j")
    val p = TV("p")
    val q = TV("q")
    
    def rewriteA(implicit env: Environment, scope: Scope) {
      val f = new FileLog(new java.io.File("/tmp/bell.json"), new DisplayContainer)
      val extrude = new Extrude(Set(I("/"), cons.root))

      val A = instantiate(APod(J, K).program, instantiate(program)._1)._2
      val ex = extrude(A) |-- display
      f += Rich.display(ex.terms)
      // Slice  f  [ J₀, J₁ ] x [ K₀, K₁ ]
      val slicef = SlicePod(A :/ "f" subtrees 1, List(J0 x K0, J0 x K1, J1 x K0, J1 x K1) map (? x _)) |> instapod
      f += slicef.obligations
      for (A <- Rewrite(slicef)(A)) {
        val ex = extrude(A) |-- display
        f += Rich.display(List(ex.terms))
        // Stratify  🄰
        val strat = StratifySlashPod(fixee(A, ex :/ "🄰"), ex :/ "🄰", ctx(A, ex :/ "🄰")("ψ"))  |> instapod
        for (A <- Rewrite(strat)(A)) {
          val ex = extrude(A) |-- display
          f += Rich.display(List(ex.terms))
          // Stratify  🄰
          val strat = StratifySlashPod(fixee(A, ex :/ "🄰"), ex :/ "🄰", ctx(A, ex :/ "🄰")("ψ"))  |> instapod
          for (A <- Rewrite(strat)(A)) {
            val ex = extrude(A) |-- display
            // Stratify  🄰
            val strat = StratifySlashPod(fixee(A, ex :/ "🄰"), ex :/ "🄰", ctx(A, ex :/ "🄰")("ψ"))  |> instapod
            for (A <- Rewrite(strat)(A)) {
              val ex = extrude(A) |-- display
              // Slice  🄰 ... q ↦ ?  [ K₀, K₁ ]
              //               p ↦ ?  [ J₀, J₁ ]
              //               θ      [ J₀, J₁ ] x [ K₀, K₁ ]
              // Slice  🄱 ... p ↦ ?  [ J₀, J₁ ]
              //               θ      [ J₀, J₁ ] x ?
              // Slice  🄲 ... q ↦ ?  [ K₀, K₁ ]
              //               θ      ? x [ K₀, K₁ ]
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
                                   (x => ReduceDistribPod(min, x(*).split))) |>> instapod
                    for (A <- Rewrite(mindist)(A)) {
                      // MinAssoc
                      val minassoc = (SimplePattern(min :@ (* :- ?)) find A flatMap (_(*) |> `⟨ ⟩?`) map
                                      (ReduceAssocPod(min, _)) filterNot (_.isTrivial)) |>> instapod
                      for (A <- Rewrite(minassoc)(A)) {
                        val ex = extrude(A) |-- display
                        // Stratify   🄴, 🄵      in  🄰
                        //            🄽, 🄾, 🅁  in  🄱
                        //            🅃, 🅄, 🅆  in  🄲
                        def stratduce(A: Term, `.` : Term, subelements: List[Term]) =
                          SimplePattern(min:@(* :- ?)) find `.` flatMap (x => `⟨ ⟩?`(x(*)) map (elements => 
                            StratifyReducePod(TermWithHole.puncture(fixee(A,`.`), x.subterm), min, elements, subelements, ctx(A, `.`)("ψ"))))
                        val strat = stratduce(A, ex :/ "🄰", List("🄴", "🄵") map (ex :/ _)) ++
                                    stratduce(A, ex :/ "🄱", List("🄽", "🄾", "🅁") map (ex :/ _)) ++
                                    stratduce(A, ex :/ "🄲", List("🅃", "🅄", "🅆") map (ex :/ _)) |>> instapod
                        for (A <- Rewrite(strat)(A)) {
                          val ex = extrude(A) |-- display
                          // Stratify  🄷, 🄸, 🄽  in  🄰
                          val strat = stratduce(A, ex :/ "🄰", List("🄷", "🄸", "🄽") map (ex :/ _)) |>> instapod
                          for (A <- Rewrite(strat)(A)) {
                            val ex = extrude(A) |-- display
                            // Stratify  🄸, 🄹, 🄻  in  🄰
                            val strat = stratduce(A, ex :/ "🄰", List("🄸", "🄹", "🄻") map (ex :/ _)) |>> instapod
                            for (A <- Rewrite(strat)(A)) {
                              val ex = extrude(A) |-- display
                              // Synth  fix(... 🄰 ...)
                              def slices(t: Term) = TypedTerm.split(t, I("/"))
                              val synth = (SimplePattern(fix(* :- /::(`...`))) find fixer(A, ex :/ "🄸")) |>>
                                           (x => SynthSlashPod(slices(x(*)), slices(x(*)))) |>> instapod
                              for (A <- Rewrite(synth)(A)) {
                                val ex = extrude(A) |-- display
                                f += Trench.displayRich(new Trench[Term](List(ex.terms)))
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

}