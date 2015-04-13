package synth.pods

import syntax.Identifier
import syntax.AstSugar._
import semantics.Prelude
import semantics.TypedTerm
import semantics.TypedTerm.typeOf_!
import semantics.TypeTranslation.TypingSugar._
import semantics.TypeTranslation.Declaration
import semantics.TypeTranslation.TypedIdentifier
import semantics.pattern.SimpleTypedPattern
import semantics.Scope
import semantics.TypeTranslation.Environment
import semantics.pattern.MacroMap



class NilPod(val domain: Term, val range: Term) {
  
  import Prelude.↓
  
  val nil = $TyTV(s"nil.${domain}${range}", domain -> range)
  val decl = 
      new Declaration(nil) where ∀:(domain, i => ~(↓(nil :@ i)))
      
  val NILPAT = SimpleTypedPattern(TypedTerm(Prelude.nil, typeOf_!(nil)))
  val macros = MacroMap(Prelude.nil ~> { x => NILPAT(x) map (m => nil) })
}

object NilPod {
  def apply(domain: Term, range: Term) = new NilPod(domain, range)
}


object NatPod {
  import Prelude.{N,B,↓}
  
  val _0 = TyTV("0", N)
  val _1 = TyTV("1", N)
  val z =  TyTV("z", N -> B)
  val nz = TyTV("~z", N -> B)
  val s =  TyTV("s", N -> N)
  val p =  TyTV("p", N -> N) //(N ∩ nz) -> N)
  
  val axioms = List(
        ↓(_0) & ↓(_1) & (TypedTerm(s :@ _0, N) =:= _1),
        ∀:(N, i => (↓(s :@ i) -> ~(TypedTerm(s :@ i, N) =:= i) )),
        ∀:(N, i => (↓(s :@ i) -> (TypedTerm(p :@ (s :@ i), N) =:= i) ))
    )
}

class ConsPod(val range: Term)(implicit env: Environment) {
  
  import Prelude.N
  
  val consType = range ->: (N -> range) ->: (N -> range)
  //val cons = $TyTV(s"cons.${range}", N -> range)
  
  private val X = V("x")
  private val L = V("l")
  
  val CONSPAT = SimpleTypedPattern(TypedTerm(Prelude.cons, consType) :@ (T(X) :- $TV("?"), T(L) :- $TV("?")))
  val macros = MacroMap(Prelude.cons ~> { 
    x => CONSPAT(x) map (m => ConsPod.consM(m(X), m(L))(env.scope)) 
    })
}

object ConsPod {
  
  import Prelude.N
  import NatPod.{z,p}
  import semantics.TypePrimitives
  
  def apply(range: Term)(implicit env: Environment) = new ConsPod(range)
  
  def singleton(x: Term) = {
    val r = typeOf_!(x)
    val i = T(TypedIdentifier($v("i"), N))
    TypedTerm(i ↦ x, (N ∩ z) -> r)
  }
  def compose(f: Term, g: Term)(implicit scope: Scope) = {
    val (tf, tg) = (typeOf_!(f), typeOf_!(g))
    val ((af, rf), (ag, rg)) = (TypePrimitives.curry(tf), TypePrimitives.curry(tg))
    val i = T(TypedIdentifier($v("j"), N))
    TypedTerm(i ↦ (g :@ (f :@ i)), af -> rg)
  }
  def consM(x: Term, l: Term)(implicit scope: Scope) = TypedTerm(singleton(x) /: compose(p, l), typeOf_!(l))
}

