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
import semantics.pattern.MacroMap
import semantics.ProgressiveTypedSubstitution
import semantics.Reflection.Consolidated
import semantics.Binding
import semantics.LambdaCalculus
import semantics.pattern.SimplePattern
import semantics.pattern.ExactMatch
import syntax.transform.Extrude
import synth.proof.Assistant



object StratifyFix {

  import semantics.Domains._
  import semantics.Prelude._

  
  import TypePrimitives.{shape,args}
  import TypedLambdaCalculus.{pullOut, enclosure}
 
  
  //def pair(x: Term, y: Term) = cons:@(x, cons:@(y, nil))

  
  def pair(x: Term, y: Term) = {
    import NatPod.{_0,_1}
    val ι = $TyTV("ι", N)
    ι ↦ /::(x |! (ι =:= _0), y |! (ι =:= _1))
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
                  ( ((θ:@(i, k)) + (θ:@(k, j))) -: TV("item") )
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
          /*
          min:@
          (
            /::(
              a ↦ (min:@ 
                    (k ↦
                      ( ((θ:@(i, k)) + (θ:@(k, j))) -: TV("item") )
                    )
                  ),
              a ↦ (Ψ:@(i, j))
            )
          )
          */
          /*(min:@ 
            (k ↦
              ( ((θ:@(i, k)) + (θ:@(k, j))) -: TV("item") )
            )
          )*/
          
        ).foldRight /*:: (? ->: ((J x J) ∩ <) ->: R)*/ ) -: f )
    ))
  }
    
  def main(args: Array[String]): Unit = {

    import examples.Paren
    import examples.Paren._
    import Shrink.{InputPod}
    import semantics.Binding.{inline,prebind}
            
    val prenv = Paren.env
    implicit val scope = prenv.scope
    
    val A = new APod(Paren.J)
    val A0 = new APod(Paren.J0)
    val A1 = new APod(Paren.J1)
    
    val (vassign, program) = TypeInference.infer( inline( prebind(InputPod.program(A.program).unfoldRight) ) )
    
    implicit val env = prenv ++ TypeTranslation.decl(scope, vassign + (V("+") -> (R ->: R ->: R)))
    
    println("-" * 80)
    
    import java.util.logging.Level
    //Reflection.log.setLevel(Level.FINER)
        
    val toR = TotalOrderPod(R)
    val nilNR = NilPod(N, R)
    val nilJR = NilPod(J, R)
    val consR = ConsPod(R)
    val minJR = MinPod(J, R, toR.<)//, opaque=true)
    val minNR = MinPod(N, R, toR.<)//, opaque=true)
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
    
    val A_f = A.program :-/ "f"
    val B_f = { val Ψ = $TV("Ψ")
                val θ = $TV("θ")
                ((Ψ :: (((J x J) ∩ Paren.<) -> R)) ↦ 
                    ((θ :: (((J x J) ∩ Paren.<) -> R)) ↦ (/::((Ψ) :: ((? x J0) -> ?),
                              ((A.program :-/ "f") :@ (Ψ,θ)) :: ((? x J1) -> ?))))) }
                       
    
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
    
    def west(e: Term) = (e :: ((? x J0) -> ?))
    def east(e: Term) = (e :: ((? x J1) -> ?))
    def nw(e: Term) = (e :: ((J0 x J0) -> ?))
    def ne(e: Term) = (e :: ((J0 x J1) -> ?))
    def sw(e: Term) = (e :: ((J1 x J0) -> ?))
    def se(e: Term) = (e :: ((J1 x J1) -> ?))
    def quadrants(enw: Term, ene: Term, esw: Term, ese: Term) = /::(nw(enw), ne(ene), sw(esw), se(ese))
    
    val phase0 = quadrants(A_f :@ (Ψ,θ), Ψ, ⊥, Ψ)
    val phase1 = Ψ ↦ quadrants(Ψ, A_f :@ (Ψ,θ), ⊥, A_f :@ (Ψ,θ))
    
    val assumptions = List(↓(NatPod._0) & ↓(NatPod._1) & ~(NatPod._0 =:= NatPod._1), ∀:(J, (x,y) => ~(↓(⊥ :@(x,y))))) map a.compile
    val goals = List( (phase1:@phase0 ) =:= (A_f :@ (Ψ,θ)) ) map a.compile map a.intros
    
    
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
    
    val p = new Prover(List(NatPod, toR, minJR, minNR, consR, nilNR))
    val t = new p.Transaction
    
    val extrude = Extrude(Set(I("/"), cons.root))

    goals foreach (g => Rewrite.display(extrude(g)))
    
    goals foreach (Rewrite.display(_))
    
    //System.exit(0)
    
    /*
    import collection.mutable.ListBuffer
    val common = ListBuffer[ListBuffer[Term]]()
    for (a <- ((assumptions ++ goals))) {
      new SimplePattern(min :@ ?).find(a) foreach (mo => { 
        Rewrite.display(mo.subterm) ; println(" ." * 40) 
        common.find { l => new ExactMatch(l.head) matchInclTypes (mo.subterm) } match {
          case Some(l) => l += mo.subterm
          case None => common += ListBuffer(mo.subterm)
        }
      })
    }
    
    val switch = new TypedSubstitution(
      common filter (_.length > 1) flatMap { l =>
        println(s"${l.length}  x  ${l.head toPretty}");
        val uf = t.let(l.head)
        l map ((_, uf))
      } toList)
    
    for (a <- ((assumptions ++ goals))) {
      println(s"${a toPretty}   --->   ${switch(a) toPretty}")
    }
    
        
    for (a <- ((assumptions ++ goals) map (switch(_)) map a.simplify map p.e map (_._2))) {
      //Rewrite.display(a)
      println(a toPretty)
    }*/

    //System.exit(0)
    
    t.commit(assumptions map a.simplify map t.prop, goals /*map (switch(_))*/ map a.simplify map t.prop)
  }
  
}