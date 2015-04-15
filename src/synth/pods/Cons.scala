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



class NilPod(val domain: Term, val range: Term)(implicit env: Environment) extends Pod {
  
  import Prelude.↓
  
  val nil = $TyTV(s"nil.${domain}${range}", domain -> range)
  override val decl = 
      new Declaration(nil) where ∀:(domain, i => ~(↓(nil :@ i)))
      
  val NILPAT = SimpleTypedPattern(TypedTerm(Prelude.nil, typeOf_!(nil)))(env.scope)
  override val macros = MacroMap(Prelude.nil ~> { x => NILPAT(x) map (m => nil) })
}

object NilPod {
  def apply(domain: Term, range: Term)(implicit env: Environment) = new NilPod(domain, range)
}

class ConsPod(val range: Term)(implicit env: Environment) extends Pod {
  
  import Prelude.N
  
  val consType = range ->: (N -> range) ->: (N -> range)
  //val cons = $TyTV(s"cons.${range}", N -> range)
  
  private val X = V("x")
  private val L = V("l")
  
  val CONSPAT = SimpleTypedPattern(TypedTerm(Prelude.cons, consType) :@ (T(X) :- $TV("?"), T(L) :- $TV("?")))(env.scope)
  override val macros = MacroMap(Prelude.cons ~> { 
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

