package synth.tactics

import syntax.AstSugar._
import semantics.Scope
import semantics.TypeTranslation

import synth.pods.NilPod
import synth.pods.NatPod
import synth.pods.ConsPod
import synth.pods.MinPod
import synth.pods.TotalOrderPod
import synth.pods.Pod
import synth.proof.Prover



object Split {

  import semantics.Domains._
  import semantics.Prelude._
  import semantics.TermTranslation.TermBreak
  import semantics.UntypedTerm

  
  def main(args: Array[String]): Unit = {
    import examples.Paren._
    implicit val scope = new Scope
    
    scope.sorts.declare(N.root)
    scope.sorts.declare(J.root)
    scope.sorts.declare(R.root)
    scope.sorts.declare(J0.root :<: J.root)
    scope.sorts.declare(J1.root :<: J.root)

    val g = TV("g")
    val h = TV("h")
    
    val prenv = (TypeTranslation.subsorts(scope) where (compl(J)(J0, J1)))
    val typedecl = Map(
        g ~> (J0 -> R),
        h ~> (J1 -> R))
        
    implicit val env = prenv ++ TypeTranslation.decl(scope, typedecl)
    
    import java.util.logging.Level
    //TypeInference.log.setLevel(Level.INFO)
    
    val termb = new TermBreak(env)
    
    val nilNR = NilPod(N, R)
    val consR = ConsPod(R)
    val toR = TotalOrderPod(R)
    val minNR = MinPod(N, R, toR.<)
    val minJR = MinPod(J, R, toR.<)
    
    val pods = List(NatPod, nilNR, consR, toR, minNR, minJR)
    
    val prover = new Prover(pods)
    val t = new prover.Transaction
    
    t.let(min :@ h)
    t.let(min :@ g)
    val mingh = t.let(min :@ (g /: h))
    val minxy = t.let( min :@ (cons :@ (min :@ g, cons :@ (min :@ h, nil))) )
    
    val assumptions = List()
    
    val goals = List(
        mingh =:= minxy
        )
        
    t.commit(assumptions, goals)
    
  }
  
}

