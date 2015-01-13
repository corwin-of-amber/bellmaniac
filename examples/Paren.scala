
package examples

import syntax.Tree
import syntax.Identifier
import semantics.Scope



object Paren {
  
  import syntax.AstSugar._
  import semantics.Domains._
  
  val :: = TI("::")

  
  val R = T(S("R"))
  val J = T(S("J"))
  val J0 = T(S("J₀"))
  val J1 = T(S("J₁"))
  
  val scope = new Scope
  scope.declareSort(R.root)
  scope.declareSort(J.root)
  scope.declareSort(J0.root :<: J.root)
  scope.declareSort(J1.root :<: J.root)

  def θ = TV("θ")
  def i = TV("i")
  def j = TV("j")
  def k = TV("k")
  def w = TV("w")
  def < = TV("<")
  val ∩ = TI("∩")
  
  def ? = T(new Identifier("?", "variable", new Uid))
  
  val tree = TI("program")(
      TV("+") :: (R x R) ->: R ,

      (TI("↦")(
        θ :: ∩(J x J, <) ->: R , i , j ,

        TI("min")(
          TI("↦")(
            k,
            (:@(:@(θ, i), k) + :@(:@(θ, k), j) + :@(:@(:@(w, i), k), j)) -: TV("item")
          ) 
        ) -: TV("compute")
      ).foldRight :: (? ->: J0 ->: J0 ->: R)  ) -: TV("A|nw")
    )
    
    
  def env = {
    import semantics.Prelude._
    import semantics.TypeTranslation
    TypeTranslation.subsorts(scope) ++
          TypeTranslation.decl(scope, Map(< ~> ((J x J) -> B))) where
          (transitive(<, J), antisymm(<, J),
                compl(J0, J1, J), allToAll(J0, <, J1, J))
  } 
          
}