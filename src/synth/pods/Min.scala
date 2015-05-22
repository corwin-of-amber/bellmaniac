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

class MinPod(domain: Term, range: Term, < : Term)(implicit env: Environment) extends Pod {
  import Prelude.{B,↓}
  
  val D = domain
  val R = range
  val min = $TyTV(s"min.$D", (D -> R) -> R)
  val argmin = $TyTV(s"argmin.$D", (D -> R) -> D)
  val min2 = $TyTV(s"min[2].$R", R -> (R -> R))

  private val X = V("x")
  val MINPAT = SimpleTypedPattern(TypedTerm(Prelude.min, (D -> R) -> R))(env.scope)
  val MIN2PAT = SimpleTypedPattern(TypedTerm(Prelude.min, R -> (R -> R)))(env.scope)
  
  override val macros = MacroMap(Prelude.min ~> {
    x => MINPAT(x) map (_ => min)
    }) ++
    MacroMap(Prelude.min ~> { x => MIN2PAT(x) map (_ => min2) })
  
  override val decl = new Declaration(min, argmin) where List(
      min =:= { val g = $TyTV("g", D -> R) ; TypedTerm(g ↦ (g :@ TypedTerm(argmin :@ g, D)), (D->R) -> R) },
      ∀:(D->R, D, (g, i) => (↓(g :@ i) -> (↓(min :@ g) & ~(< :@ (g :@ i) :@ (min :@ g)))) ) /*,
      ∀:(R, R, (a,b) => ((min2:@(a,b)) =:= a) | ((min2:@(a,b)) =:= b))*/
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
