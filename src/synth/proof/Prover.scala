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



/**
 * Carries out automatic proofs employing macro expansion, term translation,
 * and reflection.
 */
class Prover(val pods: List[Pod])(implicit env: Environment) {


  implicit val scope = env.scope
  val typedecl = env.typedecl
  val expand = new Expansion(pods map (_.macros) reduceOption (_ ++ _) getOrElse MacroMap.empty)
    
  def e(term: Term) = expand(TypeInference.infer(Binding.prebind(term), typedecl)._2)
  
  class Transaction {
    val termb = new TermBreak(env)
    val termlings = collection.mutable.ListBuffer[List[Term]]()
    
    def let(term: Term) = {
      val (v, v_t) = be(term)
      termlings += v_t
      v
    }
    
    def commit(assumptions: List[Term], goals: List[Term]) = {
      val symbols = typedecl.keys ++ (pods flatMap (_.decl.symbols)) ++ termb.intermediates
      
      val reflect = new Reflection(env, typedecl)
      reflect.currying ++= symbols filter (x => Reflection.isFuncType(env.typeOf_!(x))) map 
                                          (symbol => (symbol, reflect.overload(symbol))) toMap
  
      for (variants <- reflect.currying.values)
        reflect.alwaysDefined ++= (variants dropRight 1)
                                      
      println("· " * 25)
  
      reflect.solve((termlings.toList flatten) ++ assumptions ++ (pods flatMap (_.decl.precondition)), goals)    
    }
    
    def be(term: Term) = termb(e(term))
    
  }
}
