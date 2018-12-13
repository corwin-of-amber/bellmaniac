package synth.tactics

import syntax.Identifier
import syntax.Tree
import semantics.TypeInference.ConservativeResolve
import semantics.TypeTranslation.Declaration
import semantics.TypedIdentifier
import semantics.Scope.TypingException
import semantics.TypeTranslation.Environment
import semantics.Scope.TypingException
import semantics.TermTranslation
import semantics.TypeInference
import semantics.TypeTranslation
import semantics.Id
import syntax.AstSugar
import semantics.TypePrimitives
import semantics.Prelude
import synth.proof.Prover
import semantics.TypedTerm
import semantics.TypedLambdaCalculus
import java.util.logging.Level
import semantics.Reflection.Consolidated
import scala.collection.mutable.ListBuffer
import semantics.Trench
import semantics.Reflection
import java.util.logging.Logger
import synth.pods.TotalOrderPod
import synth.pods.MinPod
import synth.pods.NilPod
import synth.pods.ConsPod
import semantics.Scope



object Shrink {
  
  import AstSugar._

  class ShrinkStep(val term: Term, constraints: Map[String, Term], assumptions: List[Term]=List())(implicit prover: Prover) {
    //val prover = new Prover(List())(env)
    
    def apply() = {
      val t = new prover.Transaction
      val term_nw = (constraints :\ term) { case ((k, typ), term) =>
        val θ = term ? k
        val θ_nw = TypedTerm(θ, typ)
        TypedLambdaCalculus.beta(θ.root, term, θ_nw, true)
      }
      val cur = t.let(term)
      val des = t.let(term_nw)
      (term =:= term_nw) /: t.commit(assumptions, List(cur =:= des))
    }
  }
  
  def shrinkStep(term: Term, constraints: Map[String, Term])(implicit prover: Prover) = {
    val step = new ShrinkStep(term, constraints)
    step()
  }
  
  
  object InputPod {
    import Prelude.{R,B}
    import examples.Paren.{J,<,K012,K12,K12sq,P1,Q0}
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
  
  class APod(val J: Term, val J0: Term) {
    import Prelude.{ω,R,min,?,cons,nil}
    import examples.Paren.{<,θ,i,j,k,x,w,_1,f}
    
    val A = $TV("A")
    
    val program = TI("program")(
      A :- ω( 
        TI("↦")(
          θ :: ((J x J) ∩ <) ->: R , i , j ,
  
          //(@:(x, i) |! ((i+_1) =:= j)) /:
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
          )  -: TV("compute")
          
        ).foldRight -: f )
    )
  }
    
  def main(args: Array[String]): Unit = {

    import examples.Paren
    import semantics.Binding.{inline,prebind}
    import Prelude.R
            
    val prenv = Paren.env
    implicit val scope = prenv.scope
    
    val A = new APod(Paren.J, Paren.J0)
    
    val (vassign, program) = TypeInference.infer( inline( prebind(InputPod.program(A.program).unfoldRight) ) )
    
    implicit val env = prenv ++ TypeTranslation.decl(scope, vassign + (V("+") -> (R ->: R ->: R)))
    
    println("-" * 80)
    
    import Paren._
    import Prelude._
    import TypeTranslation.TypingSugar._
          
    val assumptions = List()
    
    val conclusions = new ListBuffer[Trench[Term]]
    
     // f|nw
    //
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((J₀ x J₀) ∩ <) -> R
    //conclusions += shrinkStep(program :/ "f|nw" :/ "item", Map("θ" -> ((J0 x J0) -> R)))

    val A0 = new APod(Paren.J0, Paren.K0)
    val (vassign1, program1) = TypeInference.infer( inline ( prebind(A0.program) ), vassign )
    
    val env1 = TypeTranslation.decl(scope, vassign1)
    
    val item0 = TypeInference.infer((program :/ "f") :: (? ->: (J0 x J0) ->: ?))._2
    val item1 = (program1 :/ "f")
    //val item0 = TypedLambdaCalculus.pullOut(program, (program :/ "f|nw" :/ "item")) get
    //val item1 = TypedLambdaCalculus.pullOut(program1, (program1 :/ "f" :/ "item")) get
    
    import report.console.Console
    
    Console.display(item0)
    Console.display(item1)

    val toR = TotalOrderPod(R)
    val nilNR = NilPod(N, R)
    val consR = ConsPod(R)
    val minJR = MinPod(J, R, toR.<)
    val minNR = MinPod(N, R, toR.<)
    
    val p = new Prover(List(toR, nilNR, consR, minJR, minNR))(env ++ env1)

    val t = new p.Transaction
    
    conclusions += t.commit(assumptions, List(t.let(t.intros(item0 =:= item1))))
    
    /*
    // f|nw
    //
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((J₀ x J₀) ∩ <) -> R
    conclusions += shrinkStep(program :/ "f|nw" :/ "item", Map("θ" -> ((J0 x J0) -> R)))
    
    // f|se
    //
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((J₁ x J₁) ∩ <) -> R
    conclusions += shrinkStep(program :/ "f|se" :/ "item", Map("θ" -> ((J1 x J1) -> R)))
    
    // g|sw
    //
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((K₁⋃K₂ x K₁⋃K₂) ∩ <) -> R
    conclusions += shrinkStep(program :/ "g|sw" :/ "item", Map("θ" -> (((J x J) ∩ K12sq) -> R)))

    
    // g|nw
    //
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((K₀xK₀ ⋃ K₀xK₁ ⋃ K₀xK₂ ⋃ K₁xK₂ ⋃ K₂xK₂) ∩ <) -> R
    conclusions += shrinkStep(program :/ "g|nw" :/ "item", Map("θ" -> (((J x J) ∩ P1) -> R)))
    
    // g|nw'
    //
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((K₀xK₁ ⋃ K₁xK₂) ∩ <) -> R
    conclusions += shrinkStep(program :/ "g|nw'" :/ "item2", Map("θ" -> (((J x J) ∩ Q0) -> R)))
    */
    
    println("=" * 60)
    
    Trench.display(new Trench[Term](conclusions flatMap (_.el) toList), "◦")
    
    //Rewrite.display(item)(Paren.env)
    //Rewrite.display(item_nw)(Paren.env)
  }
    
    /*
    val context1 =
      new ShrinkStep(context0, item, 
          Map("θ" -> ((J0 x J0) -> R), "k" -> J0)).verbose()
    
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((K₁⋃K₂ x K₁⋃K₂) ∩ <) -> R
    val context2 =
      new ShrinkStep(context1, program :/ "g|sw" :/ "item", 
          Map("θ" -> (((? x ?) ∩ K12sq) -> ?), "k" -> (? ∩ K12))).verbose()
          
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((K₀⋃K₁⋃K₂ x K₀⋃K₁⋃K₂) ∩ <) -> R
    val context3 =
      new ShrinkStep(context2, program :/ "g|nw" :/ "item", 
          Map("θ" -> (((? x ?) ∩ P1) -> ?), "k" -> (? ∩ K012))).verbose()
          
    val context4 =
      new ShrinkStep(context3, program :/ "g|nw'" :/ "item2", 
          Map("θ" -> (((? x ?) ∩ Q0) -> ?))).verbose()
          
    val context = context4
          
    println("=" * 80)
    for (piece <- List("f|nw", "g|sw", "g|nw", "g|nw'")) {
      println(s"$piece ? θ  ::  " + context.vassign(((program :/ piece) ? "θ").root).toPretty)
      println(s"$piece ? k  ::  " + context.vassign(((program :/ piece) ? "k").root).toPretty)
    }
  }*/
  
  
/*  
import com.microsoft.z3.Context
import com.microsoft.z3.Sort
import com.microsoft.z3.Expr
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.FuncDecl
import com.microsoft.z3.Quantifier
import com.microsoft.z3.Symbol
import com.microsoft.z3.Status
import com.microsoft.z3.Solver
import com.microsoft.z3.ArithExpr
  
  import Z3Sugar._
  def main(args: Array[String]): Unit = {
    val J = ctx mkUninterpretedSort "J"
    val R = ctx getRealSort
    val B = ctx getBoolSort
    
    val i = const ("i" -> J)
    val j = const ("j" -> J)
    val k = const ("k" -> J)
    val θ = func ("θ" :-> (J, J, R))
    val θ_def = func ("θ.def" :-> (J, J, B))
    
    val J0 = func ("J0" :-> (J, B))
    val lt = func ("<" :-> (J, J, B))
    
    // θ i k + θ k j
    val v0 = θ(i,k) + θ(k,j)
    val v0_def = θ_def(i,k) & θ_def(k,j)

    // ┌θ i k + ┌θ k j
    val θ_nw = (i: Expr, j: Expr) => θ(i,j)
    val θ_nw_def = (i: Expr, j: Expr) => J0(i) & J0(j) & θ_def(i, j)
    val v1 = θ_nw(i,k) + θ_nw(k,j)
    val v1_def = θ_nw_def(i,k) & θ_nw_def(k,j)
    
    
    val assumptions = List(
        ∀(i, j, k) (lt(i,j) ->: lt(j,k) ->: lt(i,k)),     // transitivity
        ∀(i, j) (~lt(i,i) & (lt(i,j) -> ~lt(j,i))),       // anti-refl, anti-symm
        ∀(i, j) (θ_def(i,j) -> lt(i,j)),                  // type of θ
        ∀(i, j) (J0(i) ->: ~J0(j) ->: lt(i,j)),           // J0 < J1
        !!(J0(j))                                         // sub-domain restriction
        )
        
    val goals = List(
      v0_def <-> v1_def,
      v0_def -> (ctx mkEq (v0, v1))
    )
    
    solveAndPrint(assumptions, goals)
  }
*/  

}


