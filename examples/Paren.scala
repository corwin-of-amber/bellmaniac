
package examples

import syntax.Tree
import syntax.Identifier
import semantics.Scope



object Paren {
  
  import syntax.AstSugar._
  import semantics.Domains._
  import semantics.Prelude.B
  
  val R = T(S("R"))
  val J = T(S("J"))
  val J0 = T(S("J₀"))
  val J1 = T(S("J₁"))
  
  val scope = new Scope
  scope.sorts.declare(R.root)
  scope.sorts.declare(J.root)
  scope.sorts.declare(J0.root :<: J.root)
  scope.sorts.declare(J1.root :<: J.root)

  def A = TV("A")
  def θ = TV("θ")
  def i = TV("i")
  def j = TV("j")
  def k = TV("k")
  def w = TV("w")
  def < = TV("<")
  val ∩ = TI("∩")
  
  def ? = T(new Identifier("?", "type variable", new Uid))
  
  def TT(v: Any) = T(new Identifier(v, "type variable"))
  
  val tree = TI("program")(
      
      TV("+") :: (R x R) ->: R ,
      < :: (J x J) ->: B , 
      
      ( TI("↦")(
        θ :: ∩(J x J, <) ->: R , i , j ,

        TI("min")(
          TI("↦")(
            k,
            (:@(:@(θ, i), k) + :@(:@(θ, k), j) + :@(:@(:@(w, i), k), j)) -: TV("item")
          ) 
        ) -: TV("compute")
      ).foldRight ) -: A ,
      
      TV("A|nw") :- ( A :: (? ->: J0 ->: J0 ->: R) ) , 
      TV("A|ne") :- ( A :: (? ->: J0 ->: J1 ->: R) ) ,
      TV("A|se") :- ( A :: (? ->: J1 ->: J1 ->: R) )
    )
    
    
  def env = {
    import semantics.Prelude._
    import semantics.TypeTranslation
    TypeTranslation.subsorts(scope) where 
          (transitive(<, J), antisymm(<, J),
           compl(J0, J1, J), allToAll(J0, <, J1, J))
  } 
          
}