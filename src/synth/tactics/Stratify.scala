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


object Stratify {

  import semantics.Domains._
  import semantics.Prelude._

  class PodBuilder(program: Term, symbols: List[Term])(implicit env: Environment) {
    val (vassign, body) = TypeInference.infer(program)(env.scope)
    
    def decl = mkDecl(symbols, body.split(Prelude.program.root))
    
    def mkTid(t: Term) = TypedIdentifier(t.leaf, vassign(t.leaf))
    def mkDecl(symbols: List[Term], axioms: List[Term]) = {
      val subst = new TypedSubstitution(symbols map (x => (x, T(mkTid(x)))))
      new Declaration(symbols map mkTid, axioms map (subst(_)))
    }
  }
  
  class MonoPod(val J: Term, val R: Term, val < : Term)(implicit env: Environment) extends Pod {
    val ⊑ = $TyTV("⊑", (J ->: J ->: R) ->: (J ->: J ->: R) ->: B)
    val (θ, ζ, i, j) = ($TV("θ"), $TV("ζ"), $TV("i"), $TV("j"))

    override val decl = new PodBuilder(program(
        ∀(θ,ζ)(
            ⊑ :@ (θ,ζ) <-> 
              ∀(i,j)(↓(θ:@(i,j)) -> ( ↓(ζ:@(i,j)) & ~(< :@(ζ:@(i,j), θ:@(i,j)))) )
        )
      ), List(⊑, θ, ζ, i, j)).decl
        
  }
  
  
  class AntiSymmetryPod(val D: Term, val ⊑ : Term) extends Pod {
    val x = $TyTV("x", D)
    val y = $TyTV("y", D)
    
    override val decl = new Declaration(x, y)
    val obligation = ∀(x,y)( (⊑ :@(x,y)) ->: (⊑ :@(y,x)) ->: (x =:= y) )
  }
  
  
  def main(args: Array[String]): Unit = {

    import examples.Paren
    import examples.Paren._
    import Shrink.{InputPod,APod}
    import semantics.Binding.{inline,prebind}
            
    val prenv = Paren.env
    implicit val scope = prenv.scope
    
    val A = new APod(Paren.J, Paren.J0)
    
    val (vassign, program) = TypeInference.infer( inline( prebind(InputPod.program(A.program).unfoldRight) ) )
    
    implicit val env = prenv ++ TypeTranslation.decl(scope, vassign)
    
    println("-" * 80)
    
    val toR = TotalOrderPod(R)
    val < = toR.<
    
    val monoJJR = new MonoPod(J, R, <)
    import monoJJR.{⊑}
    
    val asymm = new AntiSymmetryPod(J ->: J ->: R, ⊑)
    
    val p = new Prover(List(monoJJR, toR))
    val t = new p.Transaction
    t.commit(List(), List( t.intros(asymm.obligation) ))
  }
  
/*  
  def main(args: Array[String]): Unit = {
    import examples.Paren._
    implicit val scope = new Scope
    
    scope.sorts.declare(J.root)
    scope.sorts.declare(R.root)
    scope.sorts.declare(J0.root :<: J.root)
    scope.sorts.declare(J1.root :<: J.root)
    
    val f = TV("f")
    val c = TV("c")
    val x = TV("x")
    val i = TV("i")
    val Ijr = TV("Ijr")

    val prenv = (TypeTranslation.subsorts(scope) where (compl(J)(J0, J1)))
    val typedecl = Map(
        //< ~> ((J x J) -> B),
        Ijr ~> (((J x J)->R) -> ((J x J)->R)),
        f ~> (((J x J) -> R) -> (((J x J) /*∩ <*/) -> R)),
        c ~> (((J0 x J0) -> R) -> ((J1 x J1) -> R)),
        x ~> ((J x J) -> R) )
    
    implicit val env = prenv ++ TypeTranslation.decl(scope, typedecl)

    // f := c / I    ( := \x i. c x i / x i )
    
    // need to prove
    // c x = c (f x)
    
    val termb = new TermBreak(env)

    val (_, cxcfx) = 
      TypeInference.infer( c =:= (x ↦ (c :@ (f :@ x))), typedecl )
      
    Rewrite.display(cxcfx)
    
    val assumptions = List(
        Ijr =:= { val x = T($v("α")) ; TypedTerm(x ↦ x, (J->(J->R))->(J->(J->R))) },
        f =:= TypedTerm(c /: Ijr, (J->(J->R)) -> (J->(J->R)))
      )
    
    val p = new Prover(List())
    
    val t = new p.Transaction
    
    t.commit(assumptions, List(t.let( p.intros(cxcfx) )))
    
    /*
    val expr1 = (x :: (J0 -> R))
    val expr2 = @:(f, x) :: (J0 -> R)
    val expr3 = @:(@:(c, x), i) /: @:(x, i)
    
    val (expr1_id, expr1_env) = TermTranslation.term(env, expr1, Map())
    val (expr2_id, expr2_env) = TermTranslation.term(env, expr2, Map())
    val (expr3_id, expr3_env) = TermTranslation.term(env, expr3, Map())
    println(JR.abs(expr2_env.decl(expr2_id)).toPretty)*/
      
    /*
    import semantics.smt.Z3Sugar._
    
    {
      val F = ctx mkUninterpretedSort "J->R"
      val J = ctx mkUninterpretedSort "J"
      val R = ctx getRealSort
      val B = ctx getBoolSort
      
      val J0 = func ("J₀" :-> (J, B))
      val J1 = func ("J₁" :-> (J, B))
      
      val c = func ("c" :-> (F, J, R))
      val c_def = func ("|c|" :-> (F, J, B))
      val f = func ("f" :-> (F, J, R))
      val f_def = func ("|f|" :-> (F, J, B))
      
      val F_app = func ("@" :-> (F, J, R))
      val F_app_def = func ("|@|" :-> (F, J, B))
      
      val i = const ("i" -> J)
      val j = const ("j" -> J)
      val k = const ("k" -> J)
      val θ_abs = const ("θ#" -> F)
      val ζ_abs = const ("ζ#" -> F)

      val fθ_abs = const ("fθ#" -> F)
      
      val θ_J0R_abs = const ("θ|J0#" -> F)
      val fθ_J0R_abs = const ("fθ|J0" -> F)
      
      val assumptions = List(
          ∀(i)(J0(i) <-> ~J1(i)),
          // c :: (J0 -> R) -> (J1 -> R)
          ∀(θ_abs, i)(c_def(θ_abs, i) -> J1(i)),
          // f := c / I
          ∀(θ_abs, i)(
              ( c_def(θ_abs, i) -> (f_def(θ_abs, i) & (f(θ_abs, i) =:= c(θ_abs, i))) ) &
              ( ~c_def(θ_abs, i) -> ((f(θ_abs, i) =:= F_app(θ_abs, i)) & (f_def(θ_abs, i) <-> F_app_def(θ_abs, i))) )
            ),
          // f θ
          ∀(i)( (F_app(fθ_abs, i) =:= f(θ_abs,i)) & (F_app_def(fθ_abs, i) <-> f_def(θ_abs,i)) ),
          // θ|J0
          ∀(i)( (F_app(θ_J0R_abs, i) =:= F_app(θ_abs, i)) &
              (F_app_def(θ_J0R_abs, i) <-> (F_app_def(θ_abs, i) & J0(i))) ),
          // (f θ)|J0
          ∀(i)( (F_app(fθ_J0R_abs, i) =:= F_app(fθ_abs, i)) &
              (F_app_def(fθ_J0R_abs, i) <-> (F_app_def(fθ_abs, i) & J0(i))) ),
          // F equality
          ∀(θ_abs, ζ_abs)(
            ∀(i)( (F_app_def(θ_abs, i) <-> F_app_def(ζ_abs, i)) &
                  (F_app_def(θ_abs, i) -> (F_app(θ_abs, i) =:= F_app(ζ_abs, i))) ) -> (θ_abs =:= ζ_abs)
          )
        )
          
      val goals = List(
          //F_app_def(θ_J0R_abs, i) <-> F_app_def(fθ_J0R_abs, i),
          //F_app_def(θ_J0R_abs, i) -> (F_app(θ_J0R_abs, i) =:= F_app(fθ_J0R_abs, i))
          c(θ_J0R_abs, i) =:= c(fθ_J0R_abs, i)
        )
      
      solveAndPrint(assumptions, goals)
    } */
  }
 */
}