
package examples

import syntax.Tree
import syntax.Identifier
import semantics.Scope



object Paren {
  
  import syntax.AstSugar._
  import semantics.Domains._
  import semantics.Prelude._
  
  val R = T(S("R"))
  val J = T(S("J"))
  val J0 = T(S("J₀"))
  val J1 = T(S("J₁"))
  val K0 = T(S("K0"))
  val K1 = T(S("K1"))
  val K2 = T(S("K2"))
  val K3 = T(S("K3"))
  
  val scope = new Scope
  scope.sorts.declare(R.root)
  scope.sorts.declare(J.root)
  scope.sorts.declare(J0.root :<: J.root)
  scope.sorts.declare(J1.root :<: J.root)
  scope.sorts.declare(K0.root :<: J0.root)
  scope.sorts.declare(K1.root :<: J0.root)
  scope.sorts.declare(K2.root :<: J1.root)
  scope.sorts.declare(K3.root :<: J1.root)

  def A = TV("A")
  def `A'` = TV("A'")
  def f = TV("f")
  def g = TV("g")
  def θ = TV("θ")
  def i = TV("i")
  def j = TV("j")
  def k = TV("k")
  def w = TV("w")
  def < = TV("<")
  def P1 = TV("P1")
  
  def x = TV("x")
  def _1 = TI(1)
  
  def ? = T(new Identifier("?", "type variable", new Uid))
  
  def TT(v: Any) = T(new Identifier(v, "type variable"))
  
  val tree = TI("program")(
      
      TV("+") :: (R x R) ->: R ,
      < :: (J x J) ->: B , 
      
      P1 :: (J x J) ->: B ,
      
      A :- fix( 
        TI("↦")(
          θ :: ∩(J x J, <) ->: R , i , j ,
  
          (:@(x, i) |! ((i+_1) =:= j)) /:
          min(k ↦
              ((:@(:@(θ, i), k) + :@(:@(θ, k), j) + :@(:@(:@(w, i), k), j)) -: TV("item"))
          ) -: TV("compute")
        ).foldRight -: f ) ,
      
      TV("f|nw") :- ( f :: (? ->: (J0 x J0) ->: ?) ) ,
      TV("f|ne") :- ( f :: (? ->: (J0 x J1) ->: ?) ) ,
      TV("f|sw") :- ( f :: (? ->: (J1 x J0) ->: ?) ) ,
      TV("f|se") :- ( f :: (? ->: (J1 x J1) ->: ?) ) ,
      
      //`A'` :- fix( TV("f|nw") /: TV("f|ne") /: TV("f|se") ) ,
      
      
      g :- TV("f|ne") ,
      
      TV("g|nw") :- ( g :: (? ->: (K0 x K2) ->: ?) ) ,
      TV("g|sw") :- ( g :: (? ->: (K1 x K2) ->: ?) ) 
    )
    
    
  def env = {
    import semantics.Prelude._
    import semantics.TypeTranslation
    import semantics.TypeTranslation.TypingSugar._

    TypeTranslation.subsorts(scope) where 
         ( transitive(J)(<), antisymm(J)(<),
           compl(J)(J0, J1), allToAll(J)(J0, <, J1),
           partition(J)(J0, K0, K1), partition(J)(J1, K2, K3),
           allToAll(J)(K0, <, K1), allToAll(J)(K2, <, K3),
           ∀:( J, (x,y) => P1(x,y) <-> ((K1(x) | K2(x)) & (K1(y) | K2(y))) ) )
  } 
          
}