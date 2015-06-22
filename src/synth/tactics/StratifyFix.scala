package synth.tactics

import syntax.Identifier
import syntax.AstSugar._
import semantics.Scope
import semantics.FunctionType
import semantics.TypedTerm
import semantics.TypeTranslation
import semantics.TypeTranslation.Environment
import semantics.TypeTranslation.TypedIdentifier
import semantics.Reflection
import semantics.TypePrimitives
import semantics.TypeTranslation.TypingSugar._
import semantics.TypedLambdaCalculus
import semantics.TypeInference
import syntax.Strip
import semantics.TypeTranslation.Declaration
import synth.proof.Prover
import synth.pods.TotalOrderPod
import synth.pods.Pod
import semantics.TypedSubstitution
import semantics.Prelude
import synth.pods.NilPod
import synth.pods.ConsPod
import synth.pods.MinPod
import synth.pods.NatPod
import semantics.ProgressiveTypedSubstitution
import semantics.Reflection.Consolidated
import semantics.Binding
import semantics.LambdaCalculus
import syntax.transform.Extrude
import synth.proof.Assistant
import semantics.Trench



object StratifyFix {

  import semantics.Domains._
  import semantics.Prelude._

  
  import TypePrimitives.{shape,args}
  import TypedLambdaCalculus.{pullOut, enclosure}
 
  
  //def pair(x: Term, y: Term) = cons:@(x, cons:@(y, nil))
  //def triple(x: Term, y: Term, z: Term) = cons:@(x, cons:@(y, cons:@(z, nil)))
  //def tuple(x: Term, y: Term, z: Term, w: Term) = cons:@(x, cons:@(y, cons:@(z, cons:@(w, nil))))
  
  def tuple(x: Term, y: Term) = {
    import NatPod.{_0,_1}
    val ι = $TyTV("ι", N)
    ι ↦ /::(x |! (ι =:= _0), y |! (ι =:= _1))
  }
  
  def tuple(x: Term, y: Term, z: Term) = {
    import NatPod.{_0,_1,_2}
    val ι = $TyTV("ι", N)
    ι ↦ /::(x |! (ι =:= _0), y |! (ι =:= _1), z |! (ι =:=  _2))
  }
  
  def tuple(x: Term, y: Term, z: Term, w: Term) = {
    import NatPod.{_0,_1,_2,_3}
    val ι = $TyTV("ι", N)
    ι ↦ /::(x |! (ι =:= _0), y |! (ι =:= _1), z |! (ι =:=  _2), w |! (ι =:=  _3))
  }
  
  def pair(x: Term, y: Term) = tuple(x,y)

  
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
    val Ψ = $TV("Ψ")
    val a = $TyTV("a", N)
    
    val program = TI("program")(
          
      A :- ((Ψ :: (((J x J) ∩ <) -> R)) ↦ fix(( 
        TI("↦")(
          θ :: ((J x J) ∩ <) ->: R , i :: J , j :: J ,
  
          min:@
            pair(Ψ:@(i, j),
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
                (Ψ:@(i, j)),
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
    
    class APod(val J: Term) {
      import examples.Paren.{<,f,succ,pred}

      import InputPod.{wv,wh}
      
      val Ψ = $TV("Ψ")
      val θ = $TV("θ")
      val i = $TV("i")
      val j = $TV("j")
      val p = $TV("p")
      val q = $TV("q")
      
      val program = TI("program")(
        (Ψ :: ((J x J) -> R)) ↦ fix(
          ((θ :: ((J x J) -> R)) ↦ (i ↦ (j ↦ (
              min:@ tuple(
                  Ψ:@(i,j),
                  //min:@(p ↦ (min:@(q ↦ ((θ:@(p,q)) |! (succ(p,i) & succ(q,j)))))),
                  θ:@(pred:@i,pred:@j) |! (succ(pred(i), i) & (succ(pred(j),j))),
                  //θ:@(pred:@i |! <(pred(i), i),pred:@j |! <(pred(j),j)), // |! (succ(pred(i), i) & (succ(pred(j),j))),
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
    import Shrink.{InputPod}
    import semantics.Binding.{inline,prebind}
            
    val prenv = Paren.env
    implicit val scope = prenv.scope
    
    val spec = new SpecPod(Paren.J)
    val A = new APod(Paren.J)
    val A0 = new APod(Paren.J0)
    val A1 = new APod(Paren.J1)
    
    val gspec = GapFix.InputPod
    val GA = new GapFix.APod(Paren.J)
    
    val (vassign, program) = TypeInference.infer( inline( prebind( spec.program(gspec.program).unfold ) ) )
    
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
    
    val Ψ = $TV("Ψ")
    val θ = $TV("θ")//, ((J x J)) -> R)
    val ζ = $TyTV("ζ", (J x J) -> R)
    val ⊥ = $TyTV("⊥", (J x J) -> R)
    val i = $TV("i")
    val j = $TV("j")
    val r = $TV("r")
    
    val spec_f = spec.program :/ "f"
    val A_f = A.program :-/ "f"
    val GA_f = GA.program :-/ "f"                       
    
    val a = new Assistant
       
    import NatPod._0
        /*
    val assumptions = List(((A0.program :-/ "f") :@ (Ψ, θ)) =:= θ,
                           (B_f :@ (Ψ :: ((? x J1) -> ?)/* /::(θ :: ((J0 x J0) -> ?), Ψ :: ((? x J1) -> ?))*/, ζ) ) =:= ζ) map a.compile
    val goals = List(
        //((A0.program :-/ "f") :@ (Ψ, ζ)) =:= (ζ :: ((J0 x J0) -> ?)),
        ((A1.program :-/ "f") :@ (Ψ, ζ)) =:= (ζ :: ((J1 x J1) -> ?))) map a.compile

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
    val phase0 = θ ↦ quadrants(A_f :@ (Ψ,θ), Ψ, ⊥, Ψ)
    val phase1 = Ψ ↦ (θ ↦ (quadrants(Ψ, A_f :@ (Ψ,θ), ⊥, A_f :@ (Ψ,θ))))

    val phase2 = θ ↦ quadrants(Ψ, Ψ, ⊥, A_f :@ (Ψ,θ))
    val phase3 = Ψ ↦ (θ ↦ (quadrants(Ψ, A_f :@ (Ψ,θ), ⊥, Ψ)))
    val goals = List( init:@(A_f:@(ζ,θ))   =:=   init:@ζ,
                      A_f:@(init:@θ,θ)     =:=   spec_f :@ θ,
                      phase2:@(phase3:@(ζ,θ))  =:= phase2 :@ (ζ),
                      phase3:@(phase2:@θ,θ)   =:= phase1 :@ (Ψ,θ) )

    }
    
    /*
     * Gap
     */
    object GapObligations {
    val phase0  = θ ↦ quadrants(GA_f :@ (Ψ,θ), Ψ, Ψ, Ψ)
    val phase0i = θ  ↦ nw(θ)
    val phase1  = Ψ ↦ (θ ↦ (quadrants(Ψ, GA_f :@ (Ψ,θ), GA_f :@ (Ψ,θ), GA_f :@ (Ψ,θ))))
    
    val phase2  = θ ↦ quadrants(Ψ, GA_f :@ (Ψ,θ), Ψ, Ψ)
    val phase2i = θ ↦ north(θ)
    val phase3  = Ψ ↦ (θ ↦ (quadrants(Ψ, Ψ, GA_f :@ (Ψ,θ), GA_f :@ (Ψ,θ))))
    
    val goals = List( (phase0i:@(phase1:@(ζ,θ)) ) =:= (phase0i :@ (ζ)),
                      (phase1:@(phase0:@θ,θ)) =:= (GA_f :@ (Ψ,θ)),
                      (phase2i:@(phase3:@(ζ,θ)) ) =:= (phase2i :@ (ζ)),
                      (phase3:@(phase2:@θ,θ)) =:= (phase1 :@ (Ψ,θ)) )
    
    import GapFix.InputPod.{wv,wh}
    import GA.{p,q}
    import Paren.<
    val phase2let = 
      ((θ :: ((J x J) -> R)) ↦ quadrants(Ψ, i ↦ (j ↦ (
              min:@ tuple(
                  min:@tuple(
                    Ψ:@(i,j),
                    θ:@(pred:@i,pred:@j) |! J0(j) & (succ(pred(i), i) & (succ(pred(j),j))),
                    min:@((q::J0) ↦ ((θ:@(i,q)) + (wh:@(q,j))))
                  ),
                  θ:@(pred:@i,pred:@j) |! J1(j) & (succ(pred(i), i) & (succ(pred(j),j))),
                  min:@(p ↦ ((θ:@(p,j)) + (wv:@(p,i)))),
                  min:@((q::J1) ↦ ((θ:@(i,q)) + (wh:@(q,j))))
              ))), Ψ, Ψ))
    
    val phase2_0 = θ ↦ quadrants(Ψ,
      (i ↦ (j ↦ (
                min:@tuple(
                  Ψ:@(i,j),
                  θ:@(pred:@i,pred:@j) |! J0(j) & (succ(pred(i), i) & (succ(pred(j),j))),
                  min:@((q::J0) ↦ ((θ:@(i,q)) + (wh:@(q,j))))
                )
              ))), Ψ, Ψ)
    val phase2_1 = Ψ ↦ (θ ↦ quadrants(Ψ, 
       (i ↦ (j ↦ (
              min:@ tuple(
                  Ψ:@(i,j),
                  θ:@(pred:@i,pred:@j) |! J1(j) & (succ(pred(i), i) & (succ(pred(j),j))),
                  min:@(p ↦ ((θ:@(p,j)) + (wv:@(p,i)))),
                  min:@((q::J1) ↦ ((θ:@(i,q)) + (wh:@(q,j))))
              )
            ))), Ψ, Ψ))

    val phase2_0alt = θ ↦ (phase2:@nw(θ))
    val phase2_0i = phase0i
    val phase2_1alt = Ψ ↦ (θ ↦ (phase2:@ne_(θ)))
    val sgoals = List( (phase2_0i:@(phase2_1:@(ζ,θ)) ) =:= (phase2_0i :@ (ζ)),
                       (phase2let :@ θ) =:= (phase2 :@ θ) ,
                       (phase2_1:@(phase2_0:@θ,θ)) =:= (phase2 :@ θ) )
    }
    
    
    val assumptions = List(↓(NatPod._0) & ↓(NatPod._1) & ↓(NatPod._2) & ↓(NatPod._3) & ~(NatPod._0 =:= NatPod._1)
        & ~(NatPod._0 =:= NatPod._2) & ~(NatPod._1 =:= NatPod._2)
        & ~(NatPod._0 =:= NatPod._3) & ~(NatPod._1 =:= NatPod._3) & ~(NatPod._2 =:= NatPod._3),
        //∀:( J, (x,y) => ↓(pred:@(x)) -> Paren.<(pred:@(x), x) ),
        ∀:(J, (x,y) => ~(↓(⊥ :@(x,y))))) map a.compile
    val goals = (
        ParenObligations.goals ++ GapObligations.goals ++
        GapObligations.sgoals
    ) map a.compile map a.intros
    
    
    def m(k: Term, e: Term) = min:@(k ↦ e)
    def m2(x: Term, y: Term) = min:@pair(x,y)
    def ij(r: Term) = (i ↦ (j ↦ r))
    val e = m(k::J, (θ:@(i,k)) + (θ:@(k,j)))

    import syntax.Piping._
    
    val lhs = /::( east(   ij(m2( /::(west( ij(m2(Ψ:@(i,j), e))), east(Ψ) ) :@ (i,j), e ))   ),
                   west(   /::(west(ij(m2(Ψ:@(i,j), e))), east(Ψ))   ))
    val rhs = ij(m2(Ψ:@(i,j), e))
    //val goals = List( lhs =:= rhs ) map a.compile map a.intros
    
    
    /*
    val assumptions = List() map a.compile
    val goals = List( (/::(Ψ :: ((J0 x J0) -> R), (i ↦ (j ↦ r)) :: ((? x J1) -> R)):: ((? x J0) -> R)) =:= (Ψ :: ((J0 x J0) -> R)) ) map a.compile map a.intros
    */
    {
    val p = new Prover(List(/*NatPod,*/ toR, minJR, minNR, consR, nilNR))
    
    val extrude = Extrude(Set(I("/"), cons.root))

    goals foreach (g => Rewrite.display(extrude(g)))
    
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