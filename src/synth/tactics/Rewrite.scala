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
import synth.pods.StratifyPod
import syntax.transform.ExtrudedTerms
import synth.pods.MinAssocPod
import semantics.pattern.Matched
import synth.pods.LetPod
import synth.pods.StratifyLetPod
import semantics.TypedTerm.typeOf_!
import synth.pods.StratifyReducePod



object Rewrite {
  

  def display(term: Term)(implicit env: Environment) {
    val format = new NestedListTextFormat[Identifier]()()
    format.layOutAndAnnotate(term, (env.typeOf(_) map (_.toPretty)), (_.toPretty))
  }
  
  def display(xterm: Tree[Term]) {
    val format = new NestedListTextFormat[String]()()
    format.layOut(xterm map { x => TypedTerm.typeOf(x) match {
      case Some(typ) => s"${annotateWithTypes(x) toPretty}      〔 ${typ toPretty} 〕"
      case _ => x toPretty
    }})
  }
  
  def annotateWithTypes(term: Term, top: Boolean=true): Term = {
    if (term =~ ("↦", 2)) {
      val List(arg, body) = term.subtrees
      val targ = if (top) arg else arg :: typeOf_!(arg)
      T(term.root, List(targ, body) map (annotateWithTypes(_, top)))
    }
    else if (term =~ ("@", 2) && term.subtrees(0) =~ ("↦", 2))
      T(term.root, List(annotateWithTypes(term.subtrees(0), false),
          annotateWithTypes(term.subtrees(1), true)))
    else {
      val ttop = 
        if (term =~ (":", 2)) top else false
      T(term.root, term.subtrees map (annotateWithTypes(_, ttop)))
    }
  }
  
  def display(xterm: ExtrudedTerms) { display(xterm.terms) }

  import syntax.transform.Extrude
  import TypedLambdaCalculus.{pullOut,simplify}
  import semantics.pattern.{ExactMatch, SimplePattern}
  import synth.pods.{MinDistribPod,SlicePod}
  
  class Rewrite(val fromTo: List[(Term, Term)]) {
    private val ematch = fromTo map { case (from, to) => (new ExactMatch(from), to) }
    def apply(term: Term)(implicit env: Environment=Environment.empty) = {
      val matches = ematch flatMap { case (from, to) => from find term map ((_, Binding.prebind(to))) }
      Some(TypeInference.infer(TypedTerm.replaceDescendants(term, matches))(env.scope)._2)
      //for (s <- ematch find term) yield TypeInference.infer(TypedTerm.replaceDescendant(term, (s, subst)))(env.scope)._2
    }
    //def subst = Binding.prebind(to)
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
    println(" <> " + term.toPretty)
    println("-" * 60)
    TypeInference.infer(Binding.prebind(term), vassign)
  }
    
  
  
  
}