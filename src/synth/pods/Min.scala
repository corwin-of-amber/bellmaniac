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



class MinPod(domain: Term, range: Term, < : Term, opaque: Boolean=false)(implicit env: Environment) extends Pod {
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
  
  override val decl = new Declaration(min, argmin) where (if (opaque) List() else List(
      min =:= { val g = $TyTV("g", D -> R) ; TypedTerm(g ↦ (g :@ TypedTerm(argmin :@ g, D)), (D->R) -> R) },
      ∀:(D->R, D, (g, i) => (↓(g :@ i) -> (↓(min :@ g) & ~(< :@ (g :@ i) :@ (min :@ g)))) )/*,
      ∀:(R, R, (a,b) => ((min2:@(a,b)) =:= a) | ((min2:@(a,b)) =:= b)) */
    ))
  
}

object MinPod {
  def apply(domain: Term, range: Term, < : Term, opaque: Boolean=false)(implicit env: Environment) = new MinPod(domain, range, <, opaque)
}

object MinDistribPod {
  import Prelude.{min,cons,nil}
  import ConsPod.`⟨ ⟩`
  
  def apply(fs: List[Term]) = {
    (min :@ (/::(fs))) =:= (min :@ `⟨ ⟩`(fs map (min :@ _)))
  }
}

object MinAssocPod {
  import Prelude.{min,cons,nil}
  import ConsPod.{`⟨ ⟩`, `⟨ ⟩?`}
  import semantics.LambdaCalculus.isAppOf
  
  def apply(fs: List[Term]) = {
    def flatten(t: Term): List[Term] = isAppOf(t, min) match {
      case Some(List(arg)) => `⟨ ⟩?`(arg) match {
        case Some(elements) => elements flatMap flatten
        case _ => List(t)
      }
      case _ => List(t)
    }
    (min :@ `⟨ ⟩`(fs)) =:= (min :@ `⟨ ⟩`(fs flatMap flatten))
  }
}


object SlashToReducePod {
  
  import ConsPod.`⟨ ⟩`
  
  // Expect fs to be of scalar type (otherwise reduce(`⟨ ⟩`(fs)) does not type-check)
  
  def apply(fs: List[Term], reduce: Term) = {
    /::(fs) =:= (reduce:@(`⟨ ⟩`(fs)))
  }
}