package synth.pods

import syntax.AstSugar._
import semantics.TypeTranslation.TypingSugar._
import semantics.Prelude
import semantics.Scope
import semantics.TypeTranslation.TypedTerm



object SlicePod {
  import Prelude.?
  
  def apply(f: Term, subdomains: List[Term])(implicit scope: Scope) = {
    val slices = subdomains map (_ -> ?)
    f =:= /::(slices map (f :: _) toList)
  }
  
}

object MinPod {
  
  val ↓ = TV("↓")
  
  def apply(domain: Term, range: Term) = {
    val D = domain
    val R = range
    val min = $TV(s"min.$D")
    val argmin = $TV(s"argmin.$D")
    val < = $TV("<")
    List(min :: ((domain -> range) -> range),
        min =:= { val g = T($v("g")) ; TypedTerm(g ↦ (g :@ TypedTerm(argmin :@ g, D)), (D->R) -> R) },
        ∀:(D->R, D, (g, i) => (↓(g :@ i) -> (↓(min :@ g) & ~(< :@ (g :@ i) :@ (min :@ g)))) )
    )
  }
}

object MinDistribPod {
  import Prelude.{min,cons,nil}
  
  def apply(fs: List[Term])(implicit scope: Scope) = {
    (min :@ (/::(fs))) =:= (min :@ (((fs map (min :@ _)) :\ nil)(cons :@ _ :@ _)))
  }
}
