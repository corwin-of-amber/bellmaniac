package synth.tactics

import syntax.AstSugar._

import semantics.Scope
import semantics.FunctionType
import semantics.TypeTranslation
import semantics.TypeTranslation.{TypedIdentifier,TypedTerm}
import semantics.Reflection



object Split {

  import semantics.Domains._
  import semantics.Prelude._
  

  def main(args: Array[String]): Unit = {
    import examples.Paren._
    implicit val scope = new Scope
    
    scope.sorts.declare(J.root)
    scope.sorts.declare(R.root)
    scope.sorts.declare(J0.root :<: J.root)
    scope.sorts.declare(J1.root :<: J.root)
    
    val f = TV("f")
    val c = TV("c")
    val x = TV("x")
    val i = TV("i")

    val prenv = (TypeTranslation.subsorts(scope) where (compl(J)(J0, J1)))
    val typedecl = Map(
        f ~> ((J -> R) -> (J -> R)),
        c ~> ((J0 -> R) -> (J1 -> R)),
        x ~> (J -> R),
        i ~> J )
    
    val env = prenv ++ TypeTranslation.decl(scope, typedecl)

    val JR = new FunctionType(List(J.root), R.root)
    val JRJR = new FunctionType(List(JR.faux, J.root), R.root)
    scope.functypes += (((J -> R), JR))
    scope.functypes += (((J -> R) -> (J -> R), JRJR))

    // f := c / I := \x i. c x i / x i
    
    // need to prove
    // c x = c (f x)
    val Ijr = T(TypedIdentifier(I("I"), (J->R) -> (J->R)))
    val xj0 = T(TypedIdentifier(I("x|J0"), (J -> R)))
    val cx = T(TypedIdentifier(I("cx"), J -> R))
    val fx = T(TypedIdentifier(I("fx"), J -> R))
    val fxj0 = T(TypedIdentifier(I("fx|J0"), J -> R))
    val cfx = T(TypedIdentifier(I("cfx"), J -> R))
    
    import TypeTranslation.UntypedTerm
    
    
    val assumptions = List(
        Ijr =:= { val x = $v ; T(x) ↦ T(x) },
        f =:= TypedTerm(c /: Ijr, (J->R) -> (J->R)),
        xj0 =:= T(TypedIdentifier(x.root, J0 -> R)),
        cx =:= TypedTerm(c :@ xj0, J -> R),
        fx =:= TypedTerm(f :@ x, J -> R),
        fxj0 =:= T(TypedIdentifier(fx.root, J0 -> R)),
        cfx =:= TypedTerm(c :@ fxj0, J -> R)
      )
      
    
    val goals = List(cx =:= cfx)
        
    val symbols = List(Ijr, c, f, x, xj0, cx, fx, fxj0, cfx)
    
    val reflect = new Reflection(env, typedecl)
    
    reflect.currying ++= symbols map (symbol => (symbol.root, reflect.overload(symbol.root))) toMap

    for (symbol <- symbols) {
      println(s"${symbol.untype} :: ${env.typeOf(symbol.root).get toPretty}")
      /*
      val variants = reflect.currying(symbol.root)
      for (variant <- variants)
        println(s"   ${variant toPretty}")
      for (axiom <- reflect.curryAxioms(variants))
        println(s"   ***  ${axiom toPretty}")
      */
    }
    
    println("· " * 25)

    reflect.solve(assumptions, goals)
    
    /*
    val expr1 = (x :: (J0 -> R))
    val expr2 = @:(f, x) :: (J0 -> R)
    val expr3 = @:(@:(c, x), i) /: @:(x, i)
    
    val (expr1_id, expr1_env) = TermTranslation.term(env, expr1, Map())
    val (expr2_id, expr2_env) = TermTranslation.term(env, expr2, Map())
    val (expr3_id, expr3_env) = TermTranslation.term(env, expr3, Map())
    println(JR.abs(expr2_env.decl(expr2_id)).toPretty)*/
      
    /*
    import semantics.smt.Z3Sugar._
    
    {
      val F = ctx mkUninterpretedSort "J->R"
      val J = ctx mkUninterpretedSort "J"
      val R = ctx getRealSort
      val B = ctx getBoolSort
      
      val J0 = func ("J₀" :-> (J, B))
      val J1 = func ("J₁" :-> (J, B))
      
      val c = func ("c" :-> (F, J, R))
      val c_def = func ("|c|" :-> (F, J, B))
      val f = func ("f" :-> (F, J, R))
      val f_def = func ("|f|" :-> (F, J, B))
      
      val F_app = func ("@" :-> (F, J, R))
      val F_app_def = func ("|@|" :-> (F, J, B))
      
      val i = const ("i" -> J)
      val j = const ("j" -> J)
      val k = const ("k" -> J)
      val θ_abs = const ("θ#" -> F)
      val ζ_abs = const ("ζ#" -> F)

      val fθ_abs = const ("fθ#" -> F)
      
      val θ_J0R_abs = const ("θ|J0#" -> F)
      val fθ_J0R_abs = const ("fθ|J0" -> F)
      
      val assumptions = List(
          ∀(i)(J0(i) <-> ~J1(i)),
          // c :: (J0 -> R) -> (J1 -> R)
          ∀(θ_abs, i)(c_def(θ_abs, i) -> J1(i)),
          // f := c / I
          ∀(θ_abs, i)(
              ( c_def(θ_abs, i) -> (f_def(θ_abs, i) & (f(θ_abs, i) =:= c(θ_abs, i))) ) &
              ( ~c_def(θ_abs, i) -> ((f(θ_abs, i) =:= F_app(θ_abs, i)) & (f_def(θ_abs, i) <-> F_app_def(θ_abs, i))) )
            ),
          // f θ
          ∀(i)( (F_app(fθ_abs, i) =:= f(θ_abs,i)) & (F_app_def(fθ_abs, i) <-> f_def(θ_abs,i)) ),
          // θ|J0
          ∀(i)( (F_app(θ_J0R_abs, i) =:= F_app(θ_abs, i)) &
              (F_app_def(θ_J0R_abs, i) <-> (F_app_def(θ_abs, i) & J0(i))) ),
          // (f θ)|J0
          ∀(i)( (F_app(fθ_J0R_abs, i) =:= F_app(fθ_abs, i)) &
              (F_app_def(fθ_J0R_abs, i) <-> (F_app_def(fθ_abs, i) & J0(i))) ),
          // F equality
          ∀(θ_abs, ζ_abs)(
            ∀(i)( (F_app_def(θ_abs, i) <-> F_app_def(ζ_abs, i)) &
                  (F_app_def(θ_abs, i) -> (F_app(θ_abs, i) =:= F_app(ζ_abs, i))) ) -> (θ_abs =:= ζ_abs)
          )
        )
          
      val goals = List(
          //F_app_def(θ_J0R_abs, i) <-> F_app_def(fθ_J0R_abs, i),
          //F_app_def(θ_J0R_abs, i) -> (F_app(θ_J0R_abs, i) =:= F_app(fθ_J0R_abs, i))
          c(θ_J0R_abs, i) =:= c(fθ_J0R_abs, i)
        )
      
      solveAndPrint(assumptions, goals)
    } */
  }
  
}