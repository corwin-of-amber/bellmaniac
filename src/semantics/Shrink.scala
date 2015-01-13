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
  
    
  def shrinkCheck(env: Environment, assign: Map[Identifier, Term], expr: Term,
      retypes: Map[Identifier, Term]): (List[Environment], List[Term]) =
    shrinkCheck(env ++ TypeTranslation.decl(env.scope, assign), expr, retypes)
  
  def shrinkCheck(env: Environment, expr: Term, 
                  retypes: Map[Identifier, Term]) = {
    val (eval, eval_env) = TermTranslation.term(env, expr)
    
    val alt_env = TypeTranslation.shrink(env, retypes)
    val (alt_eval, alt_eval_env) = TermTranslation.term(env ++ alt_env, expr)
    
    (List(eval_env, alt_eval_env), equivCheck(eval_env(eval), alt_eval_env(alt_eval)))
  }
  
    
  def main(args: Array[String]): Unit = {

    import examples.Paren
      
    val resolve = new ConservativeResolve(Paren.scope)

    val program = Paren.tree
    
    val (rootvar, assign) = TypeInference.infer(program)(resolve)
    
    println("-" * 80)
    for ((k,v) <- assign)
      (k.kind, k.literal) match { case ("variable", x:String) => println(s"$k :: ${v.toPretty}") case _ => }

    val Anw = program :/ "A|nw"
    val item = program :/ "item"

    for (stmt <- List(Anw, item)) println(stmt.toPretty)
    println("=" * 80)
    
    import Paren._
    import TypeTranslation.solveAndPrint
          
    val assign0 = assign + (i ~> J0, j ~> J0)
    
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((J₀ x J₀) ∩ <) -> R
    val (assumptions, goals) =
      shrinkCheck(env, assign0, item, Map(θ ~> (assign0(θ.root)\(J → J0))))
      
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


