package synth.tactics

import semantics.TypeTranslation.Declaration
import semantics.pattern.`package`.Superposition
import semantics.pattern.{Contextual, SimpleTypedPattern, MacroMap, SimplePattern}
import syntax.AstSugar._
import semantics._
import semantics.TypeTranslation.TypingSugar._
import synth.pods.ConsPod._
import synth.proof.Prover
import synth.pods._
import syntax.transform.Extrude
import synth.proof.Assistant
import report.console.Console



object StratifyFix {

  import semantics.Domains._
  import semantics.Prelude._

  
  import TypePrimitives.{shape,args}
  import TypedLambdaCalculus.{pullOut, enclosure}
 
  
  //def pair(x: Term, y: Term) = cons:@(x, cons:@(y, nil))
  //def triple(x: Term, y: Term, z: Term) = cons:@(x, cons:@(y, cons:@(z, nil)))
  //def tuple(x: Term, y: Term, z: Term, w: Term) = cons:@(x, cons:@(y, cons:@(z, cons:@(w, nil))))


  
  class SpecPod(val J: Term) {
    import examples.Paren.{<,θ,i,j,k,x,succ,f,w}
    
    val program = TI("program")(
      fix((
        TI("↦")(
          θ :: ((J x J) ∩ <) ->: R , i :: J , j :: J ,
          /::(
            x:@i |! (succ:@(i,j)),
            min:@ 
            (k ↦
              ( ((θ:@(i, k)) + (θ:@(k, j)) + (w:@(i,k,j))) -: TV("item") )
            )
          )
        )>> ) -: f
      )
    )
  }
  
  
  class APod(val J: Term) {
    import Prelude.{fix,∩,R,min,?,cons,nil}
    import examples.Paren.{<,θ,i,j,k,x,w,_1,f}
    
    val A = $TV("A")
    val ψ = $TV("ψ")
    val a = $TyTV("a", N)
    
    val program = TI("program")(
          
      A :- ((ψ :: (((J x J) ∩ <) -> R)) ↦ fix(( 
        TI("↦")(
          θ :: ((J x J) ∩ <) ->: R , i :: J , j :: J ,
  
          min:@
            `⟨ ⟩`(ψ:@(i, j),
                min:@ 
                (k ↦
                  ( ((θ:@(i, k)) + (θ:@(k, j)) + (w:@(i,k,j))) -: TV("item") )
                )
            )
          
          /*
          min:@
          (
            cons:@(
              (min:@ 
                (k ↦
                  ( ((θ:@(i, k)) + (θ:@(k, j))) -: TV("item") )
                )
              )
                ,
              cons:@(
                (ψ:@(i, j)),
                nil
              )
            )
          )  -: TV("compute") */
          /*(min:@ 
            (k ↦
              ( ((θ:@(i, k)) + (θ:@(k, j))) -: TV("item") )
            )
          )*/
          
        ).foldRight /*:: (? ->: ((J x J) ∩ <) ->: R)*/ ) -: f )
    ))
  }
  
  object GapFix {
    
    object InputPod {
      import examples.Paren.{<,J}
      val wv = $TV("w")
      val wh = $TV("w'")
      
      val program = TI("program")(
        wv :: (((J x J) ∩ <) -> R),
        wh :: (((J x J) ∩ <) -> R)
      )        
    }
    
    object SpecPod {
      import examples.Paren.{<,J,f,_0,_1}
      import InputPod.{wv,wh}
      
      val θ = $TV("θ")
      val i = $TV("i")
      val j = $TV("j")
      val p = $TV("p")
      val q = $TV("q")
      //val _0J = TV("0.J")
      
      val program = TI("program")(
        //  _0J :: J,
        fix(
          ((θ :: ((J x J) -> R)) ↦ (i ↦ (j ↦ (
              ( (wh:@(_0,j)) |! (i=:=TypedTerm(_0,J)) ) /:
              ((
              min:@ `⟨ ⟩`(
                  //min:@(p ↦ (min:@(q ↦ ((θ:@(p,q)) |! (succ(p,i) & succ(q,j)))))),
                  θ:@(i - _1, j - _1),
                  //min:@(p ↦ ((θ:@(p,j)) |! (<(p,i)))),
                  min:@(p ↦ ((θ:@(p,j)) + (wv:@(p,i)))),
                  //min:@(q ↦ ((θ:@(i,q)) |! (<(q,j))))
                  min:@(q ↦ ((θ:@(i,q)) + (wh:@(q,j))))
                  )) |! (<(TypedTerm(_0,J), i))
              )
          )))) -: f
        )
      )
    }
    
    class APod(val J: Term) {
      import examples.Paren.{<,f,_1}

      import InputPod.{wv,wh}
      
      val ψ = $TV("ψ")
      val θ = $TV("θ")
      val i = $TV("i")
      val j = $TV("j")
      val p = $TV("p")
      val q = $TV("q")
      
      val program = TI("program")(
        (ψ :: ((J x J) -> R)) ↦ fix(
          ((θ :: ((J x J) -> R)) ↦ (i ↦ (j ↦ (
              min:@ `⟨ ⟩`(
                  ψ:@(i,j),
                  //min:@(p ↦ (min:@(q ↦ ((θ:@(p,q)) |! (succ(p,i) & succ(q,j)))))),
                  θ:@(i - _1, j - _1),
                  //min:@(p ↦ ((θ:@(p,j)) |! (<(p,i)))),
                  min:@(p ↦ ((θ:@(p,j)) + (wv:@(p,i)))),
                  //min:@(q ↦ ((θ:@(i,q)) |! (<(q,j))))
                  min:@(q ↦ ((θ:@(i,q)) + (wh:@(q,j))))
              )
          )))) -: f
        )
      )
    }
    
  }
  
    
  def main(args: Array[String]): Unit = {

    import examples.Paren
    import examples.Paren._
    import semantics.Binding.{inline,prebind}
            
    val prenv = Paren.env
    implicit val scope = prenv.scope
    
    val spec = new SpecPod(Paren.J)
    val A = new APod(Paren.J)
    val A0 = new APod(Paren.J0)
    val A1 = new APod(Paren.J1)
    
    val ginp = GapFix.InputPod
    val gspec = GapFix.SpecPod
    val GA = new GapFix.APod(Paren.J)
    
    val (vassign, program) = TypeInference.infer( inline( prebind( spec.program(ginp.program(gspec.program)).unfold ) ) )
    
    implicit val env = prenv ++ TypeTranslation.decl(scope, vassign + (V("+") -> (R ->: R ->: R)))
    
    println("-" * 80)
    
    import java.util.logging.Level
    //Reflection.log.setLevel(Level.FINER)
        
    val toR = TotalOrderPod(R)
    val nilNR = NilPod(N, R)
    val nilJR = NilPod(J, R)
    val consR = ConsPod(R)
    val minJR = MinPod(J, R, toR.<) //, opaque=true)
    val minNR = MinPod(N, R, toR.<) //, opaque=true)
    import toR.<
    val plustot = ∀:(R, (a,b) => ↓(a + b))
    val plusmono = ∀:(R, (a,b,c,d) => ~(< :@(a, c)) ->: ~(< :@(b, d)) ->: ~(< :@(a + b, c + d)))
    
    import TypedLambdaCalculus.{pullOut,enclosure,simplify}
    
    val ψ = $TV("ψ")
    val θ = $TV("θ")//, ((J x J)) -> R)
    val ζ = $TyTV("ζ", (J x J) -> R)
    val ⊥ = $TyTV("⊥", (J x J) -> R)
    val i = $TV("i")
    val j = $TV("j")
    val r = $TV("r")
    
    val spec_f = spec.program :/ "f"
    val A_f = A.program :-/ "f"
    val A0_f = A0.program :-/ "f"
    val A1_f = A1.program :-/ "f"
    val gspec_f = gspec.program :/ "f"
    val GA_f = GA.program :-/ "f"                       
    
    val a = new Assistant
       
    //import NatPod._0
        /*
    val assumptions = List(((A0.program :-/ "f") :@ (ψ, θ)) =:= θ,
                           (B_f :@ (ψ :: ((? x J1) -> ?)/* /::(θ :: ((J0 x J0) -> ?), ψ :: ((? x J1) -> ?))*/, ζ) ) =:= ζ) map a.compile
    val goals = List(
        //((A0.program :-/ "f") :@ (ψ, ζ)) =:= (ζ :: ((J0 x J0) -> ?)),
        ((A1.program :-/ "f") :@ (ψ, ζ)) =:= (ζ :: ((J1 x J1) -> ?))) map a.compile

    //val goals = List(((A1.program :/ "f") :@ θ) =:= (θ :: ((J1 x J1) -> ?))) //map (TypeInference.infer(_, vassign)) map (_._2) map (a.intros(_))
    */
    
    def north(e: Term) = (e :: ((J0 x ?) -> ?))
    def south(e: Term) = (e :: ((J1 x ?) -> ?))
    def west(e: Term) = (e :: ((? x J0) -> ?))
    def east(e: Term) = (e :: ((? x J1) -> ?))
    def nw(e: Term) = (e :: ((J0 x J0) -> ?))
    def ne_(e: Term) = (e :: ((J0 x J1) -> ?))
    def sw(e: Term) = (e :: ((J1 x J0) -> ?))
    def se(e: Term) = (e :: ((J1 x J1) -> ?))
    def quadrants(enw: Term, ene: Term, esw: Term, ese: Term) = /::(nw(enw), ne_(ene), sw(esw), se(ese))
    
    def */ = { /*lolz*/ }
    
    /*
     * Paren
     */
    object ParenObligations {
    val init = θ ↦ (i ↦ ((j::J) ↦ (x:@i |! (succ:@(i,j)))))
    val phase0 = θ ↦ quadrants(A_f :@ (ψ,θ), ψ, ⊥, ψ)
    val phase1 = ψ ↦ (θ ↦ (quadrants(ψ, A_f :@ (ψ,θ), ⊥, A_f :@ (ψ,θ))))

    val phase2 = θ ↦ quadrants(ψ, ψ, ⊥, A_f :@ (ψ,θ))
    val phase3 = ψ ↦ (θ ↦ (quadrants(ψ, A_f :@ (ψ,θ), ⊥, ψ)))
    val goals = List( init:@(A_f:@(ζ,θ))   =:=   init:@ζ,
                      A_f:@(init:@θ,θ)     =:=   spec_f :@ θ,
                      phase0:@(phase1:@(ζ,θ))  =:= phase0 :@ (ζ),
                      phase1:@(phase0:@θ,θ)    =:= A_f :@ (ψ,θ),
                      phase2:@(phase3:@(ζ,θ))  =:= phase2 :@ (ζ),
                      phase3:@(phase2:@θ,θ)    =:= phase1 :@ (ψ,θ) )

    //val synthassume = List(phase0:@θ  =:= θ)
    //val synthgoals = List(nw(A0_f:@(ψ,θ)) =:= nw(θ))
    val synthassume = List(phase0:@ζ  =:= ζ, phase2:@θ  =:= θ)
    val synthgoals = List(nw(A0_f:@(ψ,ζ)) =:= nw(ζ), se(A1_f:@(ψ,θ)) =:= se(θ))
    }
    
    /*
     * Gap
     */
    object GapObligations {
    val phase0  = θ ↦ quadrants(GA_f :@ (ψ,θ), ψ, ψ, ψ)
    val phase0i = θ  ↦ nw(θ)
    val phase1  = ψ ↦ (θ ↦ quadrants(ψ, GA_f :@ (ψ,θ), GA_f :@ (ψ,θ), GA_f :@ (ψ,θ)))
    
    val phase2  = θ ↦ quadrants(ψ, GA_f :@ (ψ,θ), ψ, ψ)
    val phase2i = θ ↦ north(θ)
    val phase3  = ψ ↦ (θ ↦ (quadrants(ψ, ψ, GA_f :@ (ψ,θ), GA_f :@ (ψ,θ))))

    val phase6  = /*ψ ↦*/ (θ ↦ (quadrants(ψ, ψ, ψ, GA_f :@ (ψ,θ))))
    
    val goals = List( (phase0i:@(phase1:@(ζ,θ)) ) =:= (phase0i :@ (ζ)),
                      (phase1:@(phase0:@θ,θ)) =:= (GA_f :@ (ψ,θ)),
                      (phase2i:@(phase3:@(ζ,θ)) ) =:= (phase2i :@ (ζ)),
                      (phase3:@(phase2:@θ,θ)) =:= (phase1 :@ (ψ,θ)) )
    
    import GapFix.InputPod.{wv,wh}
    import GA.{p,q}
    import ConsPod.`⟨ ⟩`
    import Paren.<
    val phase2let = 
      ((θ :: ((J x J) -> R)) ↦ quadrants(ψ, i ↦ (j ↦ (
              min:@ `⟨ ⟩`(
                  min:@`⟨ ⟩`(
                    ψ:@(i,j),
                    θ:@(i - _1, (j - _1) :: J0),
                    min:@((q::J0) ↦ ((θ:@(i,q)) + (wh:@(q,j))))
                  ),
                  θ:@(i - _1, (j - _1) :: J1),
                  min:@(p ↦ ((θ:@(p,j)) + (wv:@(p,i)))),
                  min:@((q::J1) ↦ ((θ:@(i,q)) + (wh:@(q,j))))
              ))), ψ, ψ))
    
    val phase2_0 = θ ↦ quadrants(ψ,
      (i ↦ (j ↦ (
                min:@`⟨ ⟩`(
                  ψ:@(i,j),
                  θ:@(i - _1, (j - _1) :: J0),
                  min:@((q::J0) ↦ ((θ:@(i,q)) + (wh:@(q,j))))
                )
              ))), ψ, ψ)
    val phase2_1 = ψ ↦ (θ ↦ quadrants(ψ, 
       (i ↦ (j ↦ (
              min:@ `⟨ ⟩`(
                  ψ:@(i,j),
                  θ:@(i - _1, (j - _1) :: J1),
                  min:@(p ↦ ((θ:@(p,j)) + (wv:@(p,i)))),
                  min:@((q::J1) ↦ ((θ:@(i,q)) + (wh:@(q,j))))
              )
            ))), ψ, ψ))

    val phase2_0alt = θ ↦ (phase2:@nw(θ))
    val phase2_0i = phase0i
    val phase2_1alt = ψ ↦ (θ ↦ (phase2:@ne_(θ)))
    
    val phase6_0alt = (θ ↦ (phase6:@nw(θ)),      ψ ↦ (θ ↦ (phase6:@(/::(ne_(θ), sw(θ), se(θ))))))
    
    val phase6_1alt = (θ ↦ (phase6:@ne_(θ)),     ψ ↦ (θ ↦ (phase6:@(/::(sw(θ), se(θ))))))
    
    val phase6_2alt = (θ ↦ (phase6:@sw(θ)),      ψ ↦ (θ ↦ (phase6:@(se(θ)))))
    
    val sgoals = List( (phase2_0i:@(phase2_1:@(ζ,θ)) ) =:= (phase2_0i :@ (ζ)),
                       (phase2let :@ θ) =:= (phase2 :@ θ) ,
                       (phase2_1:@(phase2_0:@θ,θ)) =:= (phase2 :@ θ),
        (phase6_0alt._2 :@ (phase6_0alt._1 :@ θ, θ)) =:= (phase6 :@ θ),              nw(phase6_0alt._2:@(ζ,θ)) =:= nw(ζ),
        (phase6_1alt._2 :@ (phase6_1alt._1 :@ θ, θ)) =:= (phase6_0alt._2 :@ (ψ,θ)),  ne_(phase6_1alt._2:@(ζ,θ)) =:= ne_(ζ),
        (phase6_2alt._2 :@ (phase6_2alt._1 :@ θ, θ)) =:= (phase6_1alt._2 :@ (ψ,θ)),  sw(phase6_0alt._2:@(ζ,θ)) =:= sw(ζ)
        )
        
    //import gspec._0J
    val h1 = (i ↦ (j ↦ ((wh:@(_0,j)) |! (i=:=TypedTerm(_0,J)))))
    val synthassume = List( (gspec_f :@ θ) =:= θ )
    val synthgoals = List( (GA_f:@(h1, θ)) =:= θ )
      //List( ((gspec_f :@ θ ) :@ (i,j)) =:= ((GA_f:@ (h1, (i ↦ (j ↦ (((wh:@(_0J,j)) |! (i=:=_0J)) /: ((θ:@(i,j)) |! (<(_0J,i)))))) )) :@ (i,j)) )
    }
    
    import GapFix.InputPod.wh
    //import gspec._0J
    
    val assumptions = /*GapObligations.synthassume ++ ParenObligations.synthassume ++*/ List(
        ∀:(J, (x,y,z) => ↓(wh:@(x,y)) ->: ↓(wh:@(y,z)) ->: (↓(wh:@(x,z)) & (~ <((wh:@(x,y)) + (wh:@(y,z)), wh:@(x,z)))) ),
        ∀:(J, (x,y) => ~ ↓(⊥ :@(x, y)))) map a.compile
    //noinspection ScalaUnnecessaryParentheses
    val goals = (
        ParenObligations.goals ++
        //ParenObligations.synthgoals   // (requires ParenObligations.synthassume)
        GapObligations.goals ++
        GapObligations.sgoals // ++
        //GapObligations.synthgoals  // (requires GapObligations.synthassume)
    ) map a.compile map a.intros
    

    /*
    def m(k: Term, e: Term) = min:@(k ↦ e)
    def m2(x: Term, y: Term) = min:@pair(x,y)
    def ij(r: Term) = (i ↦ (j ↦ r))
    val e = m(k::J, (θ:@(i,k)) + (θ:@(k,j)))

    import syntax.Piping._
    
    val lhs = /::( east(   ij(m2( /::(west( ij(m2(ψ:@(i,j), e))), east(ψ) ) :@ (i,j), e ))   ),
                   west(   /::(west(ij(m2(ψ:@(i,j), e))), east(ψ))   ))
    val rhs = ij(m2(ψ:@(i,j), e))
    //val goals = List( lhs =:= rhs ) map a.compile map a.intros
    */


    /*
    val assumptions = List() map a.compile
    val goals = List( (/::(ψ :: ((J0 x J0) -> R), (i ↦ (j ↦ r)) :: ((? x J1) -> R)):: ((? x J0) -> R)) =:= (ψ :: ((J0 x J0) -> R)) ) map a.compile map a.intros
    */
    {
    val p = new Prover(List(NatPod, toR, minJR, minNR, nilNR, new IndexArithPod(J, Paren.<, succ), TuplePod))
    
    val extrude = Extrude(Set(I("/"), cons.root))

    goals foreach (g => Console.display(extrude(g)))
    
    //goals foreach (Rewrite.display(_))
    
    val results =
    for (g <- goals) yield {
      val goals = List(g)
    //{
      import semantics.pattern.SimplePattern
      val t = new p.Transaction
      val switch = t.commonSwitch(new p.CommonSubexpressionElimination(goals, new SimplePattern(min :@ ?)))
      
      t.commit(assumptions map a.simplify map t.prop, goals map (switch(_)) map a.simplify map t.goal)
    }
    
    println("=" * 80)
    Trench.display(results reduce (_ ++ _), "◦")
    }
  }
  
}