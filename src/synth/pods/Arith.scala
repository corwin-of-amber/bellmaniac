package synth.pods

import syntax.AstSugar._
import semantics.{Scope, Prelude, TypedTerm}
import semantics.TypeTranslation.TypingSugar._
import semantics.TypeTranslation.Declaration
import semantics.pattern.{SimpleTypedPattern, SimplePattern, MacroMap}


trait Pod {
  val decl = new Declaration()
  val macros = MacroMap.empty
  val program = Prelude.program
  val obligations = Prelude.program
}

object Pod {
  class TacticalError(msg: String) extends Exception(msg) {}
}


object NatPod extends Pod {
  import Prelude.{N,B,↓}
  
  val _0 = TyTV("0", N)
  val _1 = TyTV("1", N)
  val _2 = TyTV("2", N)
  val _3 = TyTV("3", N)
  val z =  TyTV("z", N -> B)
  val nz = TyTV("~z", N -> B)
  val s =  TyTV("s", N -> N)
  val p =  TyTV("p", N -> N) //(N ∩ nz) -> N)
  
  private val i = $TyTV("i", N)
  
  override val decl = new Declaration(_0, _1, z, nz, s, p) where List(
      ↓(_0) & ↓(_1) & ↓(_2) & ↓(_3) &
      ~(_0 =:= _1) & ~(_0 =:= _2) & ~(_1 =:= _2) & ~(_0 =:= _3) & ~(_1 =:= _3) & ~(_2 =:= _3),
      (TypedTerm(s :@ _0, N) =:= _1),
      z <-> TypedTerm(i ↦ (i =:= _0), N -> B),
      nz <-> TypedTerm(i ↦ ~(z :@ i), N -> B),
      ∀:(N, i => (↓(s :@ i) -> ~(TypedTerm(s :@ i, N) =:= i) )),
      ∀:(N, i => (↓(s :@ i) -> (TypedTerm(p :@ (s :@ i), N) =:= i) ))
    )
}

object RealPod {
  import Prelude.R
  
  val _0 = TyTV("0", R)
}


class TotalOrderPod(domain: Term) extends Pod {
  
  import Prelude.B
  
  private val D = domain
  
  val < = $TyTV("<", D ->: D ->: B)
  
  val sym = List(<.root)
  
  override val decl = new Declaration(<) where List(
      ∀:(D, (i, j) => (< :@ i :@ j) -> ~(< :@ j :@ i)),                   // anti-symmetry
      ∀:(D, (i, j) => ~(< :@ i :@ j) ->: ~(< :@ j :@ i) ->: (i =:= j)),    // totality
      ∀:(D, (i, j, k) => ~(< :@ i :@ j) ->: ~(< :@ j :@ k) ->: ~(< :@ i :@ k))    // transitivity
    )      
}

object TotalOrderPod {
  def apply(domain: Term) = new TotalOrderPod(domain)
}


class IndexArithPod(J: Term, < : Term, succ: Term)(implicit scope: Scope) extends Pod {
  import Prelude.↓

  val _0 = TI(0)
  val _1 = TI(1)

  private val pred = $TyTV("-1", J -> J)
  private val _0J = $TyTV("0.J", J)

  private val X = TV("x")

  val MINUSPAT = SimplePattern((X :- $TV("?")) - _1)
  val ZEROPAT = SimpleTypedPattern(TypedTerm(_0, J))

  override val macros = MacroMap(
    I("-") -> { x => MINUSPAT(x) map (_(X)) map (x => (pred:@x) |! succ(pred(x),x)) },
    _0 ~> { x => ZEROPAT(x) map (x => _0J)})

  override val decl = new Declaration(_0J, pred) where List(
    ↓(_0J),
    ∀:( J, x => ~ <(x,_0J) ),
    ∀:( J, (x,y,z) => succ(x,z) -> (<(x,z) & ~(<(x,y) & <(y,z))) )
  )
}
