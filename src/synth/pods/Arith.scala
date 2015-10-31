package synth.pods

import syntax.AstSugar._
import semantics.{Scope, Prelude, TypedTerm, TraceableException}
import semantics.TypeTranslation.TypingSugar._
import semantics.TypeTranslation.Declaration
import semantics.pattern.{SimpleTypedPattern, MacroMap}


trait Pod {
  val decl = new Declaration()
  val macros = MacroMap.empty
  val program = Prelude.program
  val obligations = Prelude.program
}

object Pod {
  class TacticalError(msg: String) extends TraceableException(msg) {}
}


object NatPod extends Pod {
  import Prelude.{N,B,↓}
  
  val _0 = TyTV("0", N)
  val _1 = TyTV("1", N)
  val _2 = TyTV("2", N)
  val _3 = TyTV("3", N)
  val _4 = TyTV("4", N)
  val z =  TyTV("z", N -> B)
  val nz = TyTV("~z", N -> B)
  val s =  TyTV("s", N -> N)
  val p =  TyTV("p", N -> N) //(N ∩ nz) -> N)
  
  private val i = $TyTV("i", N)
  
  override val decl = new Declaration(_0, _1, z, nz, s, p) where (
      ↓(_0) & ↓(_1) & ↓(_2) & ↓(_3) & ↓(_4) &
      ~(_0 =:= _1) & ~(_0 =:= _2) & ~(_1 =:= _2) & ~(_0 =:= _3) & ~(_1 =:= _3) & ~(_2 =:= _3),
      ~(_0 =:= _4) & ~(_1 =:= _4) & ~(_2 =:= _4) & ~(_3 =:= _4),
      TypedTerm(s :@ _0, N) =:= _1,
      z <-> TypedTerm(i ↦ (i =:= _0), N -> B),
      nz <-> TypedTerm(i ↦ ~(z :@ i), N -> B),
      ∀:(N, i => ↓(s :@ i) -> ~(TypedTerm(s :@ i, N) =:= i) ),
      ∀:(N, i => ↓(s :@ i) -> (TypedTerm(p :@ (s :@ i), N) =:= i) )
    )
}

object RealPod {
  import Prelude.R
  
  val _0 = TyTV("0", R)
}


class TotalOrderPod(D: Term, val < : Term) extends Pod {
  
  override val decl = new Declaration(<) where (
      ∀:(D, (i, j) => (< :@ i :@ j) -> ~(< :@ j :@ i)),                           // anti-symmetry
      ∀:(D, (i, j) => ~(< :@ i :@ j) ->: ~(< :@ j :@ i) ->: (i =:= j)),           // totality
      ∀:(D, (i, j, k) => ~(< :@ i :@ j) ->: ~(< :@ j :@ k) ->: ~(< :@ i :@ k))    // transitivity
    )      
}

object TotalOrderPod {
  import Prelude.B

  def apply(D: Term) = new TotalOrderPod(D, $TyTV("<", D ->: D ->: B))
  def apply(D: Term, < : Term) = new TotalOrderPod(D, TypedTerm(<, D ->: D ->: B))
}


class IndexArithPod(val J: Term, val < : Term, val succ: Term)(implicit scope: Scope) extends Pod {
  import Prelude.{↓,B}
  import IndexArithPod.{_0,_1}

  private val succJ = $TyTI("+1", "predicate", J ->: J ->: B)
  private val predJ = $TyTI("-1", "function", J -> J)
  private val subJ = $TyTI("-", "function", J ->: J ->: J)
  private val _0J = $TyTV("0.J", J)

  private val X = TV("x")
  private val Y = TV("y")

  val MINUSPAT = SimpleTypedPattern((X :- TypedTerm($TV("?"), J)) - (Y :- $TV("?")))
  val MINUS1PAT = SimpleTypedPattern((X :- TypedTerm($TV("?"), J)) - _1)
  val SUCCPAT = SimpleTypedPattern(succ:@(TypedTerm(X :- $TV("?"), J), TypedTerm(Y :- $TV("?"), J)))
  val ZEROPAT = SimpleTypedPattern(TypedTerm(_0, J))

  override val macros = MacroMap(
    I("-") -> { x => MINUS1PAT(x) map (_(X)) match {
      case Some(x) => Some(TypedTerm((predJ:@x) |! (succJ:@(predJ:@x,x)), J))
      case None => MINUSPAT(x) match {
        case Some(mo) => Some(TypedTerm(subJ:@(mo(X), mo(Y)), J))
        case None => None
      }
    } },
    succ ~> { x => SUCCPAT(x) map (m => TypedTerm(succJ:@(m(X), m(Y)), J)) },
    _0 ~> { x => ZEROPAT(x) map (x => _0J)})

  override val decl = new Declaration(_0J, succJ, predJ, subJ) where (
    ↓(_0J),
    ∀:( J, x => ~ <(x,_0J) ),
    ∀:( J, (x,y) => ~ <(x, subJ:@(x, y)) ),
    ∀:( J, (x,y) => <(_0J,x) -> <(subJ:@(x, y), x) ),
    ∀:( J, (x,y,z) => succJ(x,z) -> (<(x,z) & ~(<(x,y) & <(y,z))) )
  )
}


object IndexArithPod {
  val _0 = TI(0)
  val _1 = TI(1)
  val succ = TV("+1")

  def apply(J: Term, < : Term)(implicit scope: Scope) = new IndexArithPod(J, <, succ)
}