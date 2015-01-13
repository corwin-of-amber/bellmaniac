package semantics

import syntax.Scheme



object Prelude {
  
  import syntax.AstSugar._
  import TypeTranslation.TypingSugar._
  
  val B = T(S(""))
  
  def transitive(r: Term, elType: Term) = 
    ∀:(elType, (x,y,z) => (r(x,y) ->: r(y,z) ->: r(x,z)))
  
  def antirefl(r: Scheme, elType: Term) = ∀:(elType, x => ~r(x,x))
  def antisymm(r: Scheme, elType: Term) = ∀:(elType, (x,y) => r(x,y) -> ~r(y,x))
  def compl(P: Scheme, nP: Scheme, elType: Term) = ∀:(elType, x => nP(x) <-> ~P(x))
  def allToAll(P: Scheme, r: Scheme, Q: Scheme, elType: Term) = ∀:(elType, (x,y) => P(x) ->: Q(y) ->: r(x,y))
 
}