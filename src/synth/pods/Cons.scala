package synth.pods

import semantics.pattern.`package`.Superposition
import syntax.AstSugar._
import semantics._
import semantics.TypedTerm.typeOf_!
import semantics.TypeTranslation.TypingSugar._
import semantics.TypeTranslation.Declaration
import semantics.pattern.SimpleTypedPattern
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

/**
 * Translates cons(x, xs) into (ι ↦ x|ι=0) / (p » xs)
 * where p : N -> N is the nat predecessor function and » is (left-to-right) function composition.
 * @param range type of list elements to apply transformation to (lists will have type N -> range).
 */
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
  
  import Prelude.{N,nil,cons}
  import NatPod.{z,p}
  import semantics.TypePrimitives
  import semantics.LambdaCalculus.isAppOf
  
  def apply(range: Term)(implicit env: Environment) = new ConsPod(range)
  
  def `⟨ ⟩`(elements: List[Term]): Term = `⟨ ⟩`(elements:_*)
    
  def `⟨ ⟩`(elements: Term*) = 
    (elements :\ nil)(cons :@ _ :@ _)
    
  def `⟨ ⟩?`(t: Term): Option[List[Term]] =
    isAppOf(t, cons) match {
      case Some(List(head, tail)) => `⟨ ⟩?`(tail) map (head +: _)
      case _ => if (t == nil) Some(List()) else None
    }
  
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


/**
 * Converts lists up to length 4 (currently) into "tuples".
 * A tuple is a function term of the form
 * ι ↦ x|ι=0 / y|ι=1 / z|ι=2 / ...
 */
object TuplePod extends Pod {
  import LambdaCalculus.isAppOf
  import Prelude.{cons,nil,N}

  def `⟨ ⟩?`(t: Term)(implicit was: Superposition): Option[List[Term]] =
    isAppOf(t, cons) match {
      case Some(List(head, tail)) => `⟨ ⟩?`(tail) map (head +: _)
      case _ => if (t == nil) Some(List()) else was get t match {
        case Some(t) => `⟨ ⟩?`(t)
        case _ => None
      }
    }

  override val macros = MacroMap.+(cons ~> { x =>
    `⟨ ⟩?`(x.term)(x.was) map (x => tuple(x))
  })


  def tuple(x: Term) = {
    import NatPod.{_0}
    val ι = $TyTV("ι", N)
    ι ↦ (x |! (ι =:= _0))
  }

  def tuple(x: Term, y: Term) = {
    import NatPod.{_0,_1}
    val ι = $TyTV("ι", N)
    ι ↦ /::(x |! (ι =:= _0), y |! (ι =:= _1))
  }

  def tuple(x: Term, y: Term, z: Term) = {
    import NatPod.{_0,_1,_2}
    val ι = $TyTV("ι", N)
    ι ↦ /::(x |! (ι =:= _0), y |! (ι =:= _1), z |! (ι =:=  _2))
  }

  def tuple(x: Term, y: Term, z: Term, w: Term) = {
    import NatPod.{_0,_1,_2,_3}
    val ι = $TyTV("ι", N)
    ι ↦ /::(x |! (ι =:= _0), y |! (ι =:= _1), z |! (ι =:=  _2), w |! (ι =:=  _3))
  }

  def tuple(xs: List[Term]): Term = xs match {
    case List(x) => tuple(x)
    case List(x,y) => tuple(x,y)
    case List(x,y,z) => tuple(x,y,z)
    case List(x,y,z,w) => tuple(x,y,z,w)
    case _ => ??? /* not enough Nats? */
  }
}
