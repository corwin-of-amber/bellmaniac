package synth.tactics

import syntax.Identifier
import syntax.Tree
import semantics.TypeInference.ConservativeResolve
import semantics.TypeTranslation.Declaration
import semantics.TypeTranslation.TypedIdentifier
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
  
  
  case class Context(env: Environment, vassign: Map[Identifier, Term], tassign: Map[Id[Term], Term])
    
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
  
  class ShrinkStep(context: Context, term: Term, constraints: Map[String, Term]) {
    
    private val shrink =
        new ShrinkCheck(context.env, context.vassign, context.tassign)

    private var _verbose = false
    
    def verbose = { _verbose = true; this }
    
    private var retypes: Map[Identifier, Term] = null
    private var assumptions: List[Environment] = null
    private var goals: List[Term] = null
    
    def prepare = {
      import TypeInference.{mark,unmark, reinforce}
      val scope = context.env.scope
      val dual = new TypeInference.DualResolve(scope)
      retypes = constraints map { case (name, constraint) =>
          val id = (term ? name).root
          val List(x,y) = reinforce(List(context.vassign(id),constraint) map mark)(dual.meet) map unmark
          id -> TypePrimitives.intersection(scope, List(x,y))
        }
      shrink(term, retypes) match { case (a,g) =>
        assumptions = a; goals = g; 
      }
    }
    
    def solve = {
      /**/ assume(retypes != null && assumptions != null && goals != null) /**/
      import semantics.smt.Z3Sugar.ProverStatus._
      if (TypeTranslation.solve(assumptions, goals, _verbose) forall (_ == VALID)) {
        if (_verbose) {
          println
          for ((k,v) <- retypes) println(s"$k :: ${v.toPretty}")
        }
        Context(context.env, context.vassign ++ retypes, context.tassign)
      }
      else context
    }
    
    def apply() = { prepare ; solve }
  }
  
  def shrinkStep(context: Context, term: Term, constraints: Map[String, Term]) = {
    val step = new ShrinkStep(context, term, constraints)
    step()
  }
    
  def main(args: Array[String]): Unit = {

    import examples.Paren
    import semantics.Binding.{inline,prebind}
            
    val prenv = Paren.env
    implicit val scope = prenv.scope
    
    //val resolve = new ConservativeResolve(Paren.scope)
    
    TypeInference.log.setLevel(Level.INFO)

    val (vassign, program) = TypeInference.infer( inline( prebind(Paren.tree) ) )
    
    val env = prenv ++ TypeTranslation.decl(scope, vassign)
    
    println("-" * 80)
    
    /*
    val litem_+ = item.subtrees(1).subtrees(0)
    val litem = item.subtrees(1).subtrees(0).subtrees(1)
    val ritem = item.subtrees(1).subtrees(1)
    
    for (stmt <- List(defn, item)) println(stmt.toPretty)

    println("~" * 40)
    
    for (symbol <- symbols(defn); tpe <- vassign get symbol)
      println(s"$symbol :: ${tpe.toPretty}")
    */

    println("=" * 80)
    
    import Paren._
    import Prelude._
    import TypeTranslation.TypingSugar._
          
    val p = new Prover(List())(env)
    val assumptions = List()
    
    val conclusions = new ListBuffer[Trench[Term]]
    
    // f|nw
    //
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((J₀ x J₀) ∩ <) -> R
    {
      val item = program :/ "f|nw" :/ "item"

      val t = new p.Transaction
      val θ = item ? "θ"
      val θ_nw = TypedTerm(θ, (J0 x J0) -> R)
      val item_nw = TypedLambdaCalculus.beta(θ.root, item, θ_nw, true)
      //TypeInference.log.setLevel(Level.INFO)
      val cur = t.let(item)
      val des = t.let(item_nw)
      
      conclusions += (item =:= item_nw) /: t.commit(assumptions, List(cur =:= des))
    }
    
    // f|se
    //
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((J₁ x J₁) ∩ <) -> R
    {
      val item = program :/ "f|se" :/ "item"
      val t = new p.Transaction
      val θ = item ? "θ"
      val θ_nw = (TypedTerm(θ, ((J1 x J1)) -> R))
      val item_nw = TypedLambdaCalculus.beta(θ.root, item, θ_nw, true)
      val cur = t.let(item)
      val des = t.let(item_nw)
      
      conclusions += (item =:= item_nw) /: t.commit(assumptions, List(cur =:= des))
    }

    // g|sw
    //
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((K₁⋃K₂ x K₁⋃K₂) ∩ <) -> R
    {
      val item = program :/ "g|sw" :/ "item"
      val t = new p.Transaction
      val θ = item ? "θ"
      val θ_nw = TypedTerm(θ, ((J x J) ∩ K12sq) -> R)
      val item_nw = TypedLambdaCalculus.beta(θ.root, item, θ_nw, true)
      val cur = t.let(item)
      val des = t.let(item_nw)
      
      conclusions += (item =:= item_nw) /: t.commit(assumptions, List(cur =:= des))
    }
    
    // g|nw
    //
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((K₀xK₀ ⋃ K₀xK₁ ⋃ K₀xK₂ ⋃ K₁xK₂ ⋃ K₂xK₂) ∩ <) -> R
    {
      val item = program :/ "g|nw" :/ "item"
      val t = new p.Transaction
      val θ = item ? "θ"
      val θ_nw = TypedTerm(θ, ((J x J) ∩ P1) -> R)
      val item_nw = TypedLambdaCalculus.beta(θ.root, item, θ_nw, true)
      val cur = t.let(item)
      val des = t.let(item_nw)
      
      conclusions += (item =:= item_nw) /: t.commit(assumptions, List(cur =:= des))
    }
    
    // g|nw'
    //
    // Current typing is:
    //   θ :: ((J x J) ∩ <) -> R
    // desired typing is:
    //   θ :: ((K₀xK₁ ⋃ K₁xK₂) ∩ <) -> R
    {
      val item = program :/ "g|nw'" :/ "item2"
      Rewrite.display(item)(env)
      val t = new p.Transaction
      val θ = item ? "θ"
      val θ_nw = TypedTerm(θ, ((J x J) ∩ Q0) -> R)
      val item_nw = TypedLambdaCalculus.beta(θ.root, item, θ_nw, true)
      val cur = t.let(item)
      val des = t.let(item_nw)
      
      conclusions += (item =:= item_nw) /: t.commit(assumptions, List(cur =:= des))
    }
    
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


