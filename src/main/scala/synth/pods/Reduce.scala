package synth.pods

import syntax.AstSugar._
import semantics.TypeTranslation.TypingSugar._
import semantics.{Scope, Prelude, TypedTerm}
import semantics.pattern.SimpleTypedPattern
import semantics.pattern.MacroMap
import semantics.TypeTranslation.Declaration
import semantics.TypeTranslation.Environment



class MinPod(domain: Term, range: Term, < : Term, opaque: Boolean=false)(implicit scope: Scope) extends Pod {
  import Prelude.{B,↓}
  
  val D = domain
  val R = range
  val min = $TyTV(s"min.$D", (D -> R) -> R)
  val argmin = $TyTV(s"argmin.$D", (D -> R) -> D)
  val min2 = $TyTV(s"min[2].$R", R -> (R -> R))

  private val X = V("x")
  val MINPAT = SimpleTypedPattern(TypedTerm(Prelude.min, (D -> R) -> R))(scope)
  val MIN2PAT = SimpleTypedPattern(TypedTerm(Prelude.min, R -> (R -> R)))(scope)
  
  override val macros = MacroMap(Prelude.min ~> {
    x => MINPAT(x) map (_ => min)
    }) ++
    MacroMap(Prelude.min ~> { x => MIN2PAT(x) map (_ => min2) })
  
  override val decl = new Declaration(min, argmin) where (if (opaque) List() else List(
      min =:= { val g = $TyTV("g", D -> R) ; TypedTerm(g ↦ (g :@ TypedTerm(argmin :@ g, D)), (D->R) -> R) },
      ∀:(D->R, D, (g, i) => ↓(g :@ i) -> (↓(min :@ g) & ~(< :@ (g :@ i, min :@ g))) )/*,
      ∀:(R, R, (a,b) => ((min2:@(a,b)) =:= a) | ((min2:@(a,b)) =:= b)) */
    ))
  
}

object MinPod {
  def apply(domain: Term, range: Term, < : Term, opaque: Boolean=false)(implicit scope: Scope) = new MinPod(domain, range, <, opaque)
}

class MaxPod(domain: Term, range: Term, < : Term, opaque: Boolean=false)(implicit scope: Scope) extends Pod {
  import Prelude.{B,↓}
  
  val D = domain
  val R = range
  val max = $TyTV(s"max.$D", (D -> R) -> R)
  val argmax = $TyTV(s"argmax.$D", (D -> R) -> D)
  val max2 = $TyTV(s"max[2].$R", R -> (R -> R))

  private val X = V("x")
  val MAXPAT = SimpleTypedPattern(TypedTerm(Prelude.max, (D -> R) -> R))(scope)
  val MAX2PAT = SimpleTypedPattern(TypedTerm(Prelude.max, R -> (R -> R)))(scope)
  
  override val macros = MacroMap(Prelude.max ~> {
    x => MAXPAT(x) map (_ => max)
    }) ++
    MacroMap(Prelude.max ~> { x => MAX2PAT(x) map (_ => max2) })
  
  override val decl = new Declaration(max, argmax) where (if (opaque) List() else List(
      max =:= { val g = $TyTV("g", D -> R) ; TypedTerm(g ↦ (g :@ TypedTerm(argmax :@ g, D)), (D->R) -> R) },
      ∀:(D->R, D, (g, i) => ↓(g :@ i) -> (↓(max :@ g) & ~(< :@ (max :@ g, g :@ i))) )
    ))
  
}

object MaxPod {
  def apply(domain: Term, range: Term, < : Term, opaque: Boolean=false)(implicit scope: Scope) = new MaxPod(domain, range, <, opaque)
}


class ReduceDistribPod(val reduce: Term, val fs: List[Term]) extends Pod {
  import Prelude.min
  import ConsPod.`⟨ ⟩`

  assert(reduce.isLeaf)

  override val program =
    (reduce :@ /::(fs)) =:= (reduce :@ `⟨ ⟩`(fs map (reduce :@ _)))
}

object ReduceDistribPod {
  def apply(reduce: Term, fs: List[Term]) = new ReduceDistribPod(reduce, fs)
}

class ReduceAssocPod(val reduce: Term, val fs: List[Term]) extends Pod {
  import Prelude.{min,cons,nil}
  import ConsPod.{`⟨ ⟩`, `⟨ ⟩?`}
  import semantics.LambdaCalculus.isAppOf

  assert(reduce.isLeaf)

  def flatten(t: Term): List[Term] = isAppOf(t, reduce) match {
    case Some(List(arg)) => `⟨ ⟩?`(arg) match {
      case Some(elements) => elements flatMap flatten
      case _ => List(t)
    }
    case _ => List(t)
  }

  override val program =
    (reduce :@ `⟨ ⟩`(fs)) =:= (reduce :@ `⟨ ⟩`(fs flatMap flatten))

  val isTrivial = program.subtrees(0) == program.subtrees(1)
}

object ReduceAssocPod {
  def apply(reduce: Term, fs: List[Term]) = new ReduceAssocPod(reduce, fs)
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