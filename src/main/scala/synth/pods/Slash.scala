package synth.pods

import semantics.TypeTranslation.Declaration
import syntax.AstSugar._
import semantics.TypeTranslation.TypingSugar._
import semantics.Scope
import semantics.Prelude
import semantics.TypedTerm
import semantics.TypedLambdaCalculus
import syntax.Identifier


/**
 *        <
 * J = J₀ ⨃ J₁
 *
 * Means that J can be partitioned into J₀, J₁ s.t. every element of J₀ is less than every element of J₁.
 */
class PartitionPod(val J: Term, val < : Term, val J0: Term, val J1: Term)(implicit scope: Scope) extends Pod {
  import Prelude.{partition, allToAll}

  val U = T(scope.sorts.getMasterOf(J.leaf))

  override val decl = new Declaration where (
    partition(U)(J, J0, J1),
    allToAll(U)(J0, <, J1)
  )
}

object PartitionPod {
  def apply(J: Term, < : Term, J0: Term, J1: Term)(implicit scope: Scope) = new PartitionPod(J, <, J0, J1)
}


class OffsetsPod(val J: Term, val arith: IndexArithPod)(implicit scope: Scope) extends Pod {
  import Prelude.{B,↓}

  val U = T(scope.sorts.getMasterOf(J.leaf))
  
  val `J+1` = TypedTerm(T(I(s"${J.leaf.literal}+1", "predicate")), U -> B)
  val `J-1` = TypedTerm(T(I(s"${J.leaf.literal}-1", "predicate")), U -> B)
  val `J∪J+1` = TypedTerm(T(I(s"${J.leaf.literal}∪${`J+1`.leaf.literal}", "predicate")), U -> B)
  val `J∪J-1` = TypedTerm(T(I(s"${J.leaf.literal}∪${`J-1`.leaf.literal}", "predicate")), U -> B)
  
  override val decl = new Declaration(`J+1`, `J-1`, `J∪J+1`, `J∪J-1`) where (
    
    ∀:(U, (x,y) => arith.issuccJ(y,x) -> (`J+1`(x) <-> J(y))),
    ~`J+1`(arith._0J),
    //∀:(U, x => ∀:(U, y => ~arith.issuccJ(y,x)) -> (~`J+1`(x))),
      
    ∀:(U, (x,y) => arith.issuccJ(x,y) -> (`J-1`(x) <-> J(y))),
    ~`J-1`(arith._NJ),
    //∀:(U, x => ∀:(U, y => ~arith.issuccJ(x,y)) -> (~`J-1`(x))),
    
    ∀:(U, x => `J∪J+1`(x) <-> (J(x) | `J+1`(x))),
    ∀:(U, x => `J∪J-1`(x) <-> (J(x) | `J-1`(x)))

    // - this seems to diverge:
    //∀:(U, x => `J-1`(x) <-> (J(arith.succJ(x)) & ↓(arith.succJ:@x) & (arith.issuccJ:@(x,arith.succJ:@x)) ))
  )
}

object OffsetsPod {
  def apply(J0: Term, arith: IndexArithPod)(implicit scope: Scope) = new OffsetsPod(J0, arith)
}


class PadPod(f: Term, padding: List[Term]) extends Pod {

  import TypedTerm.typeOf_!

  override val program =
    f =:= (/::(f :: padding) :: typeOf_!(f))

  override val obligations = {
    val fabs = $TyTV("f", typeOf_!(f))
    fabs =:= (/::(fabs :: padding) :: typeOf_!(f))
  }
}

object PadPod {
  def apply(f: Term, padding: List[Term]) = new PadPod(f, padding)
  def apply(f: Term, padding: Term, subdomains: List[Term]) = {
    import Prelude.?
    val slices = subdomains map (_ -> ?)
    new PadPod(f, slices map (padding :: _))
  }
}


class SlashDistribPod(val f: Term, val box: Term)(implicit scope: Scope) extends Pod {
  import TypedTerm.replaceDescendant
  
  override val program =
    if (f.nodes exists (_ eq box)) {
      f =:= /::(box.split(I("/")) map (x => replaceDescendant(f, (box, x))))
    }
    else throw new TacticalError(s"'${box toPretty}' should be a sub-term of '${f toPretty}'")

}

object SlashDistribPod {
  def apply(f: Term, box: Term)(implicit scope: Scope) = new SlashDistribPod(f, box)
}


object StratifyPod {
  import Prelude.{ω,ℐ,?}
  import TypedTerm.{replaceDescendant,replaceDescendants}

  /*
   * TODO obligations
   * q, g monotonic
   * q nondecreasing
   */
  
  def apply(box: Term, quadrant: Term, sideburns: List[Term]=List())(implicit scope: Scope) = {
    val quadrants = TypedTerm.split(box, I("/"))
    if (quadrants exists (_ eq quadrant)) {
      val θ = $TV("θ")
      val q = /::(quadrant +: (sideburns map (__ => ℐ :: (__ -> ?))))
      val g = replaceDescendant(box, (quadrant, ℐ))
      val strata = List(replaceDescendants(box, (quadrants filter (_ ne quadrant) map ((_, ℐ))) :+(quadrant, ω(q))),
        ω(g))
      ω(box) =:= θ ↦ ((θ /: strata)((x, y) => y :@ x))
    }
    else throw new TacticalError(s"'${quadrant toPretty}' is not a component of '${box toPretty}'")
  }
}



object StratifyLetPod {
  import Prelude.{ω,ℐ,?}
  import TypedLambdaCalculus.{pullOut,enclosure,simplify}
  import TypedTerm.replaceDescendant
  
  /*
   * TODO obligation
   * forall θ (capsule θ = capsule (f θ))
   */
  
  def apply(f: Term, component: Term)(implicit scope: Scope) = {
    val _θ = $TV("θ̲")
    val (capsule, ctx) = (pullOut(f, component) get, enclosure(f, component) get)
    val let = { val ψ = $TV("ψ") ; ψ ↦ ω(replaceDescendant(f, (component, ψ :@ ctx.tail))) }
    ω(f) =:= (_θ ↦ ((TI("let") :- (let :@ simplify(capsule :@ _θ)) :@ _θ)))
  }
}


object LetPod {
  import TypedLambdaCalculus.{pullOut,enclosure}
  import TypedTerm.replaceDescendant
  
  def apply(f: Term, component: Term)(implicit scope: Scope) = {
    val (capsule, ctx) = (pullOut(f, component) get, enclosure(f, component) get)
    val let = { val y = $TV("y") ; y ↦ (replaceDescendant(f, (component, y :@ ctx))) }
    f =:= (let :@ capsule)
  }
}

/*
object StratifyReducePod {
  import Prelude.{ω,ℐ,?}
  import TypedLambdaCalculus.{pullOut,enclosure}
  import TypedTerm.replaceDescendant

  import Prelude.{min,cons,nil}
  import ConsPod.{`⟨ ⟩`, `⟨ ⟩?`}
  
  def findContainingReduction(box: Term, components: List[Term]) =
    box.nodes find (n => n =~ ("@", 2) && n.subtrees(0).root != "cons" && (`⟨ ⟩?`(n.subtrees(1)) match {
      case Some(l) => components forall (x => l exists (_ eq x))
      case None => false
    }))
  
  /*
   * obligation; 
   * forall θ (q θ = q (box θ))
   * g >= q >= I
   * g monotonic
   */
    
  def apply(box: Term, components: List[Term])(implicit scope: Scope) = {
    val f = findContainingReduction(box, components) getOrElse { throw new TacticalError(s"cannot locate reduction containing '${components map (_ toPretty)}'") }
    val (capsule, ctx) = (pullOut(box, f) get, enclosure(box, f) get)
    /**/ assume(!ctx.isEmpty) /**/
    val quadrant = (box split I("/") find (_.hasDescendant(f)) get)
    /**/ assume(f =~ ("@", 2)) /**/
    val (reduce, all_components) = (f.subtrees(0), `⟨ ⟩?`(f.subtrees(1)) get)
    val other_components = all_components filter (x => !(components exists(_ eq x)))
    val θ = $TV("θ")
    val wwtb = ctx.head :@ ctx.tail
    val q = replaceDescendant(box, (f, reduce :@ (`⟨ ⟩`(components))))
    val g = replaceDescendant(box, (f, reduce :@ (`⟨ ⟩`(other_components :+ wwtb))))
    val strata = List(q, ω(g))
    ω(box) =:= θ ↦ ((θ /: strata)((x,y) => y :@ x))
  }
}
*/