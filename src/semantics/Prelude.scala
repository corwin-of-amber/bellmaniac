package semantics

import syntax.Scheme
import syntax.Identifier



object Prelude {
  
  import syntax.AstSugar._
  import TypeTranslation.TypingSugar._
  
  val B = TS("")
  val N = TS("N")
  val R = TS("R")
  val TRUE = TI(true)
  val FALSE = TI(false)

  val ∩ = TI("∩")
  def min = TI("min")
  def max = TI("max")
  val fix = TI("fix")
  val ω = TI("ω")
  def nil = TI("nil")
  def cons = TI("cons")
  def ℐ = TI("I")

  val ↓ = TV("↓")

  def ? = T(new Identifier("?", "type variable", new Uid))
    
  val program = TV("program")
  
  def transitive(elType: Term)(r: Term) = 
    ∀:(elType, (x,y,z) => (r(x,y) ->: r(y,z) ->: r(x,z)))
  
  def antirefl(elType: Term)(r: Scheme) = ∀:(elType, x => ~r(x,x))
  def antisymm(elType: Term)(r: Scheme) = ∀:(elType, (x,y) => r(x,y) -> ~r(y,x))
  def compl(elType: Term)(P: Scheme, nP: Scheme) = ∀:(elType, x => nP(x) <-> ~P(x))
  def partition(elType: Term)(U: Scheme, P: Scheme, nP: Scheme) = ∀:(elType, x => (U(x) <-> (nP(x) | P(x))) & ~(P(x) & nP(x)))
  def allToAll(elType: Term)(P: Scheme, r: Scheme, Q: Scheme) = ∀:(elType, (x,y) => P(x) ->: Q(y) ->: r(x,y))
 
}