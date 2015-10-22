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
      ∀:(D->R, D, (g, i) => ↓(g :@ i) -> (↓(min :@ g) & ~(< :@ (g :@ i) :@ (min :@ g))) )/*,
      ∀:(R, R, (a,b) => ((min2:@(a,b)) =:= a) | ((min2:@(a,b)) =:= b)) */
    ))
  
}

object MinPod {
  def apply(domain: Term, range: Term, < : Term, opaque: Boolean=false)(implicit env: Environment) = new MinPod(domain, range, <, opaque)
}

class MinDistribPod(val fs: List[Term]) extends Pod {
  import Prelude.min
  import ConsPod.`⟨ ⟩`
  
  override val program =
    (min :@ /::(fs)) =:= (min :@ `⟨ ⟩`(fs map (min :@ _)))
}

object MinDistribPod {
  def apply(fs: List[Term]) = new MinDistribPod(fs)
}

class MinAssocPod(val fs: List[Term]) extends Pod {
  import Prelude.{min,cons,nil}
  import ConsPod.{`⟨ ⟩`, `⟨ ⟩?`}
  import semantics.LambdaCalculus.isAppOf
  
  def flatten(t: Term): List[Term] = isAppOf(t, min) match {
    case Some(List(arg)) => `⟨ ⟩?`(arg) match {
      case Some(elements) => elements flatMap flatten
      case _ => List(t)
    }
    case _ => List(t)
  }

  override val program =
    (min :@ `⟨ ⟩`(fs)) =:= (min :@ `⟨ ⟩`(fs flatMap flatten))

  val isTrivial = program.subtrees(0) == program.subtrees(1)
}

object MinAssocPod {
  def apply(fs: List[Term]) = new MinAssocPod(fs)
}

class SlashToReducePod(val fs: List[Term], val reduce: Term) extends Pod {
  
  import ConsPod.`⟨ ⟩`
  
  // Expect fs to be of scalar type (otherwise reduce(`⟨ ⟩`(fs)) does not type-check)
  
  override val program =
    /::(fs) =:= (reduce:@`⟨ ⟩`(fs))
}

object SlashToReducePod {
  def apply(fs: List[Term], reduce: Term) = new SlashToReducePod(fs, reduce)
}