package synth.tactics

import syntax.AstSugar._
import semantics.Prelude.?

import semantics._
import semantics.TypeTranslation.TypingSugar._
import semantics.TypedScheme.TermWithHole
import syntax.Identifier

import synth.pods.NilPod
import synth.pods.NatPod
import synth.pods.ConsPod
import synth.pods.MinPod
import synth.pods.TotalOrderPod
import synth.pods.Pod
import synth.proof.Prover



object Slice {

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


class SlicePod(val f: Term, val subdomains: List[Term]) extends Pod {

  val slices = subdomains map (_ -> ?)
  override val program =
    f =:= /::(slices map (f :: _))

  override val obligations = {
    val fabs = $TyTV("f", TypedTerm.typeOf_!(f))
    fabs =:= /::(slices map (fabs :: _))
  }

}

object SlicePod {

  def apply(f: Term, subdomains: List[Term]) = new SlicePod(f, subdomains)
/*
  def splitSkip(term: Term, sep: Identifier): List[Term] =
    if (term =~ (":", 2)) splitSkip(term.subtrees(1), sep)
    else if (term.root == sep) term.subtrees flatMap (splitSkip(_, sep))
    else List(term)

  def slices(term: Term) = splitSkip(term, I("/"))*/
}


/**
 * Combines Slice, SlashDistrib, and SlashToReduce (indirectly).
 * e(f) = reduce < e(f1), e(f2), ... >
 *   where fi = f :: (Xi -> ?)
 * @param e
 * @param f
 * @param subdomains X1 ... Xn
 * @param combine term list combinator (e.g. x => min:@
 */
class SliceAndDicePod(val e: TermWithHole, val f: Term, val subdomains: List[Term],
                      val combine: Iterable[Term] => Term) extends Pod
{
  val slices = subdomains map (_ -> ?)
  override val program =
    e(f) =:= combine(slices map (f :: _) map (e(_)))

}

object SliceAndDicePod {

  def apply(e: TermWithHole, f: Term, subdomains: List[Term],
            combine: Iterable[Term] => Term) =
    new SliceAndDicePod(e, f, subdomains, combine)

  def apply(h: Term, f: Term, subdomains: List[Term],
            combine: Iterable[Term] => Term)(implicit scope: Scope) =
    new SliceAndDicePod(TermWithHole.puncture(h, f), f, subdomains, combine)
}