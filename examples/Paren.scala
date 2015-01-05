
package examples

import syntax.Tree
import syntax.Identifier
import semantics.Scope



object Paren {
  
  import syntax.AstSugar._
  import semantics.Domains._
  
  val :@ = TI("@")
  val :: = TI("::")

  
  val R = T(S("R"))
  val J = T(S("J"))
  val J0 = T(S("J₀"))
  
  val scope = new Scope
  scope.declareSort(R.root)
  scope.declareSort(J.root)
  scope.declareSort(J0.root :<: J.root)

  implicit class DSL(private val term: Term) extends AnyVal {
    def ::(that: Term) = Paren.::(that, term)
    def -:(that: Term) = TI(":")(term, that)
    def ->(that: Term) = TI("->")(term, that)
    def ->:(that: Term) = TI("->")(that, term)
    def x(that: Term) = TI("x")(term, that)
    def +(that: Term) = :@(:@(TI("+"), term), that)
  }
  
  def θ = TV("θ")
  def i = TV("i")
  def j = TV("j")
  def k = TV("k")
  def w = TV("w")
  def < = TV("<")
  val ∩ = TI("∩")
  
  val tree = TI("program")(
      TV("+") :: (R x R) ->: R ,

      TI("↦")(
        θ :: ∩(J0 x J, <) ->: R , i , j ,

        TI("min")(
          TI("↦")(
            k,
            (:@(:@(θ, i), k) + :@(:@(θ, k), j)  + :@(:@(:@(w, i), k), j)) -: TV("item")
          ) 
        ) -: TV("compute")
      ).foldRight
    )
}