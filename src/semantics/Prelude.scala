package semantics

import syntax.Scheme



object Prelude {
  
  import syntax.AstSugar._
  import TypeTranslation.TypingSugar._
  
  val B = T(S(""))
  val TRUE = TI(true)
  val FALSE = TI(false)

  val ∩ = TI("∩")
  def min = TI("min")
  val fix = TI("fix")
  val ω = TI("ω")
  def nil = TI("nil")
  def cons = TI("cons")

  def transitive(elType: Term)(r: Term) = 
    ∀:(elType, (x,y,z) => (r(x,y) ->: r(y,z) ->: r(x,z)))
  
  def antirefl(elType: Term)(r: Scheme) = ∀:(elType, x => ~r(x,x))
  def antisymm(elType: Term)(r: Scheme) = ∀:(elType, (x,y) => r(x,y) -> ~r(y,x))
  def compl(elType: Term)(P: Scheme, nP: Scheme) = ∀:(elType, x => nP(x) <-> ~P(x))
  def partition(elType: Term)(U: Scheme, P: Scheme, nP: Scheme) = ∀:(elType, x => (U(x) <-> (nP(x) | P(x))) & ~(P(x) & nP(x)))
  def allToAll(elType: Term)(P: Scheme, r: Scheme, Q: Scheme) = ∀:(elType, (x,y) => P(x) ->: Q(y) ->: r(x,y))
 
}