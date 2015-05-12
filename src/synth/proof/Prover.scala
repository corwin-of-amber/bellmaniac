package synth.proof

import syntax.AstSugar._
import semantics.UntypedTerm
import semantics.pattern.Expansion
import semantics.TermTranslation.TermBreak
import semantics.Binding
import semantics.TypeInference
import semantics.TypeTranslation.Environment
import semantics.pattern.MacroMap
import semantics.Reflection
import synth.pods.Pod
import semantics.TypeTranslation
import semantics.TypePrimitives
import semantics.TypedTerm
import semantics.Scope
import semantics.TypedLambdaCalculus
import semantics.TypeTranslation.Declaration
import syntax.Identifier



/**
 * Carries out automatic proofs employing macro expansion, term translation,
 * and reflection.
 */
class Prover(val pods: List[Pod])(implicit env: Environment) {

  import TypeTranslation.TypingSugar._
  import TypedTerm.typeOf_!
  import TypePrimitives.{shape, args}
  
  implicit val scope = env.scope
  val typedecl = env.typedecl
  val expand = new Expansion(pods map (_.macros) reduceOption (_ ++ _) getOrElse MacroMap.empty)
    
  def intros(goal: Term): (List[Term], Term) = {
    if (goal =~ ("=", 2)) {
      val List(lhs, rhs) = goal.subtrees
      val ftype = shape(env.typeOf_!(lhs))
      if (ftype != shape(env.typeOf_!(rhs)))
        throw new Scope.TypingException(s"incompatible types in equality, '${typeOf_!(lhs) toPretty}'  =  '${typeOf_!(rhs) toPretty}")
      val vars = qvars(args(ftype))
      (vars, TypedLambdaCalculus.simplify((lhs:@(vars:_*)) =:= (rhs:@(vars:_*))))
    }
    else if (goal.root == "∀") {
      val vars = goal.subtrees.dropRight(1)
      val (more_vars, g) = intros(goal.subtrees.last)
      (vars ++ more_vars, g)
    }
    else (List(), goal)
  }
    
  
  def e(term: Term) = {
    val (vassign, typed) = TypeInference.infer(/*Binding.prebind*/(term), typedecl)
    (TypeTranslation.decl(env.scope, vassign), expand(typed))
  }
  
  class Transaction {
    val termb = new TermBreak(env)
    val termlings = collection.mutable.ListBuffer[(Environment, List[Term])]()
    val locals = collection.mutable.Set[Identifier]()
    
    def let(term: Term) = {
      val (v_env, (v, v_t)) = be(term)
      termlings += ((v_env, v_t))
      v
    }
    
    def intros(goal: Term) = {
      val (vars, g) = Prover.this.intros(goal)
      locals ++= vars map (_.leaf)
      g
    }
    
    def commit(assumptions: List[Term], goals: List[Term]) = {
      val symbols = typedecl.keys ++ (pods flatMap (_.decl.symbols)) ++ termb.intermediates ++ locals
      val env1 = (env /: termlings) { case (env, (env1, _)) => env ++ env1 }
      val terms1 = termlings map (_._2)
      
      val reflect = new Reflection(env1, typedecl)
      reflect.currying ++= symbols filter (x => Reflection.isFuncType(env1.typeOf_!(x))) map 
                                          (symbol => (symbol, reflect.overload(symbol))) toMap
  
      for (variants <- reflect.currying.values)
        reflect.alwaysDefined ++= (variants dropRight 1)
                                      
      println("· " * 25)
  
      reflect.solve((terms1.toList flatten) ++ assumptions ++ (pods flatMap (_.decl.precondition)), goals)    
    }
    
    def be(term: Term) = {
      val (env1, typed) = e(term)
      (env1, termb(typed))
    }
    
  }
}
