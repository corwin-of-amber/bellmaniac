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
import semantics.pattern.DownCastCoercion



object Rewrite {
  
  import syntax.Piping._
  
  class Rewrite(val fromTo: List[(Term, Term)], val opts: Rewrite.Options=Rewrite.Options.default)(implicit env: Environment) {
    
    private val ematch = fromTo map { case (from, to) => opts.withDownCast match {
      case true => (new ExactMatch(from) with DownCastCoercion, to) 
      case false => (new ExactMatch(from), to) 
    } }
    
    def apply(term: Term)(implicit env: Environment): Option[Term] = apply(term, Some(term))
    
    def apply(term: Term, within: Iterable[Term]) = {
      implicit val scope = env.scope
      val matches = 
        for ((from, to) <- ematch; 
             m <- (within flatMap from.findInBodies) |-- (warnIfEmpty(_, from.pattern, within)))
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
    case class Options(val withDownCast: Boolean=true)
    object Options { val default = Options() }
    
    def apply(from: Term, to: Term)(implicit env: Environment): Rewrite = apply(from, to, Options.default)
    def apply(equation: Term)(implicit env: Environment): Rewrite = apply(equation, Options.default)
    def apply(equations: Iterable[Term])(implicit env: Environment): Rewrite = apply(equations, Options.default)

    def apply(from: Term, to: Term, opts: Options)(implicit env: Environment) = new Rewrite(List((from, to)), opts)
    def apply(equation: Term, opts: Options)(implicit env: Environment) = new Rewrite(List(splitEq(equation)), opts)
    def apply(equations: Iterable[Term], opts: Options)(implicit env: Environment) = new Rewrite(equations map splitEq toList, opts)
    def splitEq(equation: Term) = {
      if (equation =~ ("=", 2)) (equation.subtrees(0), equation.subtrees(1))
      else throw new Exception(s"expected an equation of the form 'from = to', got '${equation toPretty}")
    }
  }

  implicit class PodRewrite(x: Rewrite.type)(implicit env: Environment) {
    import Rewrite.Options
    def apply(pod: Pod): Rewrite = apply(pod, Options.default)
    def apply(pods: Iterable[Pod]): Rewrite = apply(pods, Options.default)
    def apply(pod: Pod, opts: Options) = Rewrite(pod.program.split(Prelude.program.root), opts)
    def apply(pods: Iterable[Pod], opts: Options) = Rewrite(pods flatMap (_.program.split(Prelude.program.root)), opts)
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