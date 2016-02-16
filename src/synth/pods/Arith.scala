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


class TacticalError(msg: String) extends TraceableException(msg) {}



object NatPod extends Pod {
  import Prelude.{N,B,↓}

  val nats = 0 to 8 map (n => TyTV(s"$n", N)) toList
  val _0 = nats(0)
  val _1 = nats(1)
  val _2 = TyTV("2", N)
  val _3 = TyTV("3", N)
  val _4 = TyTV("4", N)
  val z =  TyTV("z", N -> B)
  val nz = TyTV("~z", N -> B)
  val s =  TyTV("s", N -> N)
  val p =  TyTV("p", N -> N) //(N ∩ nz) -> N)
  
  private val i = $TyTV("i", N)
  
  override val decl = new Declaration(_0, _1, z, nz, s, p) where (
      &&(nats map (↓(_))),
      &&(nats.zipWithIndex flatMap {case (n,i) => nats drop (i+1) map (m => ~(n =:= m))}),
      /*↓(_0) & ↓(_1) & ↓(_2) & ↓(_3) & ↓(_4) &
      ~(_0 =:= _1) & ~(_0 =:= _2) & ~(_1 =:= _2) & ~(_0 =:= _3) & ~(_1 =:= _3) & ~(_2 =:= _3),
      ~(_0 =:= _4) & ~(_1 =:= _4) & ~(_2 =:= _4) & ~(_3 =:= _4),*/
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


class TotalOrderPod(val D: Term, val < : Term) extends Pod {
  
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

  val issuccJ = $TyTI("+1", "predicate", J ->: J ->: B)
  val succJ = $TyTI("+1", "function", J ->: J)
  val predJ = $TyTI("-1", "function", J -> J)
  val subJ = $TyTI("-", "function", J ->: J ->: J)
  val _0J = $TyTV("0.J", J)
  val _NJ = $TyTV("N.J", J)

  private val X = TV("x")
  private val Y = TV("y")

  val ? = $TV("?")
  val J_? = TypedTerm(?, J)

  val MINUSPAT = SimpleTypedPattern((X :- J_?) - (Y :- J_?))
  val MINUS1PAT = SimpleTypedPattern((X :- J_?) - _1)
  val PLUS1PAT = SimpleTypedPattern((X :- J_?) + _1)
  val SUCCPAT = SimpleTypedPattern(succ:@(X :- J_?, Y :- J_?))
  val ZEROPAT = SimpleTypedPattern(TypedTerm(_0, J))

  override val macros = MacroMap(
    I("-") -> { x => MINUS1PAT(x) map (_(X)) match {
      case Some(x) => Some(TypedTerm((predJ:@x) |! (<(_0J,x) & (issuccJ:@(predJ:@x,x))), J))
      case None => MINUSPAT(x) match {
        case Some(mo) => Some(TypedTerm(subJ:@(mo(X), mo(Y)), J))
        case None => None
      }
    } },
    I("+") -> { x => PLUS1PAT(x) map (_(X)) map (x => TypedTerm((succJ:@x) |! (issuccJ:@(x,succJ:@x)), J)) },
    succ ~> { x => SUCCPAT(x) map (m => TypedTerm(issuccJ:@(m(X), m(Y)), J)) },
    _0 ~> { x => ZEROPAT(x) map (x => _0J)})

  override val decl = new Declaration(_0J, issuccJ, succJ, predJ, subJ) where (
    ↓(_0J) & ↓(_NJ),
    ∀:( J, x => ~ <(x,_0J) ),
    ∀:( J, x => ~ <(_NJ, x) ),
    ∀:( J, (x,y) => ~ <(x, subJ:@(x, y)) ),
    ∀:( J, (x,y) => <(_0J,x) -> <(subJ:@(x, y), x) ),
    ∀:( J, (x,y,z) => issuccJ(x,z) -> (<(x,z) & ~(<(x,y) & <(y,z))) ),
    /* dangerous territory! */
    ∀:(J, x => ∀:(J, y => ~ <(y,x)) -> (x =:= _0J)),
    ∀:(J, x => ∀:(J, y => ~issuccJ(y,x)) -> (x =:= _0J)), /* - implied by previous ones, but helps the solver */
    ∀:(J, x => ∀:(J, y => ~ <(x,y)) -> (x =:= _NJ)),
    ∀:(J, x => ∀:(J, y => ~issuccJ(x,y)) -> (x =:= _NJ)) /* - implied by previous ones, but helps the solver */
  )
}


object IndexArithPod {
  val _0 = TI(0)
  val _1 = TI(1)
  val succ = TV("+1")

  def apply(J: Term, < : Term)(implicit scope: Scope) = new IndexArithPod(J, <, succ)
}