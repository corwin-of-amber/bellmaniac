package synth.pods

import syntax.Identifier
import syntax.AstSugar._
import semantics.TypeTranslation.TypingSugar._
import semantics.Prelude
import semantics.Scope
import semantics.TypedTerm
import semantics.pattern.SimpleTypedPattern
import semantics.pattern.MacroMap
import javax.lang.model.`type`.DeclaredType
import semantics.TypeTranslation.Declaration
import semantics.TypeTranslation.Environment



object SlicePod {
  import Prelude.?
  
  def apply(f: Term, subdomains: List[Term])(implicit scope: Scope) = {
    val slices = subdomains map (_ -> ?)
    f =:= /::(slices map (f :: _) toList)
  }
  
}

class MinPod(domain: Term, range: Term, < : Term)(implicit env: Environment) {
  import Prelude.{B,↓}
  
  val D = domain
  val R = range
  val min = $TyTV(s"min.$D", (D -> R) -> R)
  val argmin = $TyTV(s"argmin.$D", (D -> R) -> D)

  private val X = V("x")
  val MINPAT = SimpleTypedPattern(TypedTerm(Prelude.min, (D -> R) -> R))(env.scope)
  
  val macros = MacroMap(Prelude.min ~> {
    x =>
      println(s"MINPAT($x) = ${MINPAT(x)}")
      MINPAT(x) map (m => min)
    })
  
  val decl = new Declaration(min, argmin) where List(
      min =:= { val g = T($v("g")) ; TypedTerm(g ↦ (g :@ TypedTerm(argmin :@ g, D)), (D->R) -> R) },
      ∀:(D->R, D, (g, i) => (↓(g :@ i) -> (↓(min :@ g) & ~(< :@ (g :@ i) :@ (min :@ g)))) )
    )
  
}

object MinPod {
  def apply(domain: Term, range: Term, < : Term)(implicit env: Environment) = new MinPod(domain, range, <)
}

object MinDistribPod {
  import Prelude.{min,cons,nil}
  
  def apply(fs: List[Term])(implicit scope: Scope) = {
    (min :@ (/::(fs))) =:= (min :@ (((fs map (min :@ _)) :\ nil)(cons :@ _ :@ _)))
  }
}
