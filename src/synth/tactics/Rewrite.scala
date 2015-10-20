package synth.tactics

import syntax.Tree
import syntax.AstSugar._
import semantics.TypedTerm
import semantics.Scope
import semantics.TypeTranslation
import semantics.TypeInference
import semantics.Id
import report.console.NestedListTextFormat
import syntax.Identifier
import semantics.TypeTranslation.Environment
import semantics.TermTranslation.TermBreak
import semantics.Binding
import semantics.Prelude
import semantics.TypedLambdaCalculus
import semantics.Reflection
import semantics.pattern.ExactMatch
import semantics.TypeTranslation.Declaration
import synth.pods._
import syntax.transform.ExtrudedTerms
import semantics.pattern.Matched
import semantics.TypedTerm.typeOf_!


object Rewrite {
  

  def display(term: Term)(implicit env: Environment) {
    val format = new NestedListTextFormat[Identifier]()()
    format.layOutAndAnnotate(term, (env.typeOf(_) map (_.toPretty)), (_.toPretty))
  }

  import syntax.transform.Extrude
  import TypedLambdaCalculus.{pullOut,simplify}
  import semantics.pattern.{ExactMatch, SimplePattern}
  import synth.pods.{MinDistribPod,SlicePod}
  
  class Rewrite(val fromTo: List[(Term, Term)]) {
    private val ematch = fromTo map { case (from, to) => (new ExactMatch(from), to) }
    
    def apply(term: Term)(implicit env: Environment): Option[Term] = apply(term, Some(term))
    
    def apply(term: Term, within: Iterable[Term])(implicit env: Environment) = {
      implicit val scope = env.scope
      val matches = 
        for ((from, to) <- ematch; subterm <- within; m <- from find subterm)
          yield (m, Binding.prebind(to))
      Some(TypeInference.infer(TypedTerm.replaceDescendants(term, matches))._2)
    }
  }
  
  object Rewrite {
    def apply(from: Term, to: Term) = new Rewrite(List((from, to)))
    def apply(equation: Term) = new Rewrite(List(splitEq(equation)))
    def apply(equations: Iterable[Term]) = new Rewrite(equations map splitEq toList)
    def splitEq(equation: Term) = {
      if (equation =~ ("=", 2)) (equation.subtrees(0), equation.subtrees(1))
      else throw new Exception(s"expected an equation of the form 'from = to', got '${equation toPretty}")
    }
  }

  implicit class PodRewrite(x: Rewrite.type) {
    def apply(pod: Pod) = Rewrite(pod.program.split(Prelude.program.root))
    def apply(pods: Iterable[Pod]) = Rewrite(pods flatMap (_.program.split(Prelude.program.root)))
  }
  
  
  
  def proveEquality(lhs: Term, rhs: Term, typedecl: Map[Identifier, Term])(implicit env: Environment) = {
    val termb = new TermBreak(env)
    val (lhs_id, lhs_t) = termb(lhs)
    val (rhs_id, rhs_t) = termb(rhs)
    val assumptions = lhs_t ++ rhs_t
    val goals = List(lhs_id =:= rhs_id)
    val reflect = new Reflection(env, typedecl)
    val symbols = typedecl.keys ++ termb.intermediates
    reflect.currying ++= symbols filter (x => Reflection.isFuncType(env.typeOf_!(x))) map 
                                        (symbol => (symbol, reflect.overload(symbol))) toMap
                                        
    reflect.solve(assumptions, goals)
  }
  
  def instantiate(term: Term, vassign: Map[Identifier, Term]=Map())(implicit scope: Scope) = {
    println("-" * 60)
    for (conj <- term.conjuncts)
      println(" <> " + conj.toPretty)
    println("-" * 60)
    TypeInference.infer(Binding.prebind(term), vassign)
  }

  def instantiate(pod: Pod)(implicit scope: Scope)
  : (Map[Identifier, Term], Term) = instantiate(pod.program)

  def instantiate(pod: Pod, vassign: Map[Identifier, Term])(implicit scope: Scope)
    : (Map[Identifier, Term], Term) = instantiate(pod.program, vassign)
    
  
  
  
}