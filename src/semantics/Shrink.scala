package semantics

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
import syntax.{Identifier,AstSugar}
import smt.Z3Sugar
import semantics.TypeInference.ConservativeResolve
import syntax.transform.TreeSubstitution
import semantics.TypeTranslation.Declaration
import semantics.TypeTranslation.TypedIdentifier
import semantics.Scope.TypingException
import semantics.smt.Z3Gate
import semantics.TypeTranslation.Environment
import syntax.transform.GenTreeSubstitution
import semantics.Scope.TypingException



object Shrink {
  
  import AstSugar._

  
  def equivCheck(v0: TypedIdentifier, v1: TypedIdentifier): List[Term] = {
    if (v0.typ == v1.typ) {
      val typ = v0.typ
      val vas = 
        if (typ.root == "->") 
          typ.unfoldRight.subtrees dropRight 1 map (TypedIdentifier($_, _)) map (T(_))
        else List()
      val (s0, s1) = (T(v0.untype), T(v1.untype))
      List(∀(vas)(s0(vas) =:= s1(vas)))
    }
    else throw new TypingException(s"incompatible types: '$v0'  ~  '$v1'")
  }
  
  def equivCheck(v0: Declaration, v1: Declaration): List[Term] =
    equivCheck(v0.head, v1.head) ++
    equivCheck(v0.support, v1.support)
  
  
  class ShrinkCheck(env: Environment, vassign: Map[Identifier, Term], tassign: Map[Id[Term], Term]) {
    
    def apply(expr: Term, retypes: Map[Identifier, Term]): (List[Environment], List[Term]) =
      apply(env ++ TypeTranslation.decl(env.scope, vassign), expr, retypes)
    
    private def apply(env: Environment, expr: Term, retypes: Map[Identifier, Term]) = {
      val (eval, eval_env) = TermTranslation.term(env, expr, tassign)
      
      val alt_env = TypeTranslation.shrink(env, retypes)
      val (alt_eval, alt_eval_env) = TermTranslation.term(env ++ alt_env, expr, tassign)
      
      (List(eval_env, alt_eval_env), equivCheck(eval_env(eval), alt_eval_env(alt_eval)))
    }
  }
  
  import syntax.Tree
  
    
  def main(args: Array[String]): Unit = {

    import examples.Paren
    import Binding.{inline,prebind}
      
    val resolve = new ConservativeResolve(Paren.scope)

    val program = inline( prebind(Paren.tree) )
    
    val (vassign, tassign) = TypeInference.infer(Paren.scope, program)
    
    println("-" * 80)
    for ((k,v) <- vassign)
      println(s"$k :: ${v.toPretty}")

    val Anw = program :/ "A|nw"
    val item = Anw :/ "item"

    for (stmt <- List(Anw, item)) println(stmt.toPretty)
    println("=" * 80)
    
    import Paren._
    import TypeTranslation.solveAndPrint
          
    val θ = item ? "θ"
    
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((J₀ x J₀) ∩ <) -> R
    val (assumptions, goals) =
      new ShrinkCheck(env, vassign, tassign)(item, Map(θ ~> (vassign(θ.root)\(J → J0))))
      //shrinkCheck(env, vassign, item, tassign, Map(θ ~> (vassign(θ.root)\(J → J0))))
      
    solveAndPrint(assumptions, goals)
  }
  
  
  
  /*
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


