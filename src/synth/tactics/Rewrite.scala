package synth.tactics

import syntax.Tree
import syntax.AstSugar._
import syntax.transform.ExtrudedTerms
import semantics.TypedTerm
import semantics.Scope
import semantics.TypeTranslation
import semantics.TypeInference
import semantics.Id
import syntax.Identifier
import semantics.TypeTranslation.Environment
import semantics.TermTranslation.TermBreak
import semantics.Binding
import semantics.Prelude
import semantics.TypedLambdaCalculus
import semantics.Reflection
import semantics.pattern.ExactMatch
import semantics.TypeTranslation.Declaration
import semantics.pattern.Matched
import synth.pods._



object Rewrite {
  
  import syntax.Piping._
  
  class Rewrite(val fromTo: List[(Term, Term)])(implicit env: Environment) {
    
    private val ematch = fromTo map { case (from, to) => (new ExactMatch(from), to) }
    
    def apply(term: Term)(implicit env: Environment): Option[Term] = apply(term, Some(term))
    
    def apply(term: Term, within: Iterable[Term]) = {
      implicit val scope = env.scope
      val matches = 
        for ((from, to) <- ematch; 
             m <- (within flatMap from.findInBodies_cast) |-- (warnIfEmpty(_, from.pattern, within)))
          yield (m, TypedTerm.preserveBoth(m, Binding.prebind(to)))
      Some(TypeInference.infer(TypedTerm.replaceDescendants(term, matches))._2)
    }
    
    def warnIfEmpty(seq: Iterable[Term], lookingFor: Term, within: Iterable[Term]) {
      if (seq.isEmpty) {
        println(s"WARN: No match for ${lookingFor toPretty}")
        showNearMatches(lookingFor, within);
      }
    }
    
    def showNearMatches(lookingFor: Term, within: Iterable[Term]) {
      val y = lookingFor
      for (x <- within flatMap (_.nodes) if x.toPretty == y.toPretty) {
        println("INFO: Near match -")
        import semantics.TypedTerm.typeOf
        for ((xn,yn) <- x.nodes zip y.nodes)
          if (typeOf(xn) != typeOf(yn)) {
            println(s" + ${xn toPretty}  ::  ${typeOf(xn) map (_ toPretty)}")
            println(s" + ${yn toPretty}  ::  ${typeOf(yn) map (_ toPretty)}")
          }
      }
    }
  }
  
  object Rewrite {
    def apply(from: Term, to: Term)(implicit env: Environment) = new Rewrite(List((from, to)))
    def apply(equation: Term)(implicit env: Environment) = new Rewrite(List(splitEq(equation)))
    def apply(equations: Iterable[Term])(implicit env: Environment) = new Rewrite(equations map splitEq toList)
    def splitEq(equation: Term) = {
      if (equation =~ ("=", 2)) (equation.subtrees(0), equation.subtrees(1))
      else throw new Exception(s"expected an equation of the form 'from = to', got '${equation toPretty}")
    }
  }

  implicit class PodRewrite(x: Rewrite.type)(implicit env: Environment) {
    def apply(pod: Pod) = Rewrite(pod.program.split(Prelude.program.root))
    def apply(pods: Iterable[Pod]) = Rewrite(pods flatMap (_.program.split(Prelude.program.root)))
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