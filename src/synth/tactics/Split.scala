package synth.tactics

import syntax.AstSugar
import semantics.TypeTranslation
import semantics.TypePrimitives
import semantics.FunctionType
import semantics.TermTranslation
import semantics.Scope
import semantics.TypeTranslation.TypedIdentifier
import syntax.Identifier
import semantics.TypeTranslation.Environment



object Split {
  
  import AstSugar._
  import semantics.Domains._
  import semantics.Prelude._
  
  class Reflection(val env: Environment) {
    
    val funcSymbols = (for ((_, d) <- env.decl; s <- d.symbols if isFunc(s)) yield s).toSet
    val funcSymbolsU = funcSymbols map {x => x.untype -> x} toMap
    
    def isFunc(v: TypedIdentifier) = v.typ.root == "->"
        
    def maybeFunc(v: Identifier) = v match {
      case t: TypedIdentifier => if (isFunc(t)) Some(t) else None
      case _ => throw new Scope.TypingException(s"can't figure out the type of $v")
    }
    
    def collectQuantified(phi: Term) = {
      for (n <- phi.nodes if n.root == "∀"; s <- n.subtrees dropRight 1; f <- maybeFunc(s.root))
        yield f
    }
    
    def collectConsts(phi: Term) = {
      for (n <- phi.nodes if n.isLeaf; f <- funcSymbolsU get n.root) yield f
    }
  }
  
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

    val env = (TypeTranslation.subsorts(scope) where (compl(J)(J0, J1))) ++
      TypeTranslation.decl(scope, 
          Map(f ~> ((J -> R) -> (J -> R)),
              c ~> ((J0 -> R) -> (J1 -> R)),
              x ~> (J -> R) )) 

    // f := c /I := \x i. c x i / x i
    
    // need to prove
    // c x = c (f x)
    val JR = new FunctionType(List(J.root), R.root)
    scope.functypes += (((J -> R), JR))
    
    val expr1 = (x :: (J0 -> R))
    val expr2 = @:(f, x) :: (J0 -> R)
    
    val (expr1_id, expr1_env) = TermTranslation.term(env, expr1, Map())
    val (expr2_id, expr2_env) = TermTranslation.term(env, expr2, Map())
    for ((_, d) <- expr1_env.decl) println(d.toPretty)
    for ((_, d) <- expr2_env.decl) println(d.toPretty)
    println(JR.abs(expr2_env.decl(expr2_id)).toPretty)
    
    val reflect = new Reflection(expr1_env ++ expr2_env)
    for ((k, v) <- (expr1_env ++ expr2_env).decl)
      for (phi <- v.precondition) {
        for (typed <- reflect.collectQuantified(phi))
          println(typed)
        for (typed <- reflect.collectConsts(phi))
          println(typed)
      }
    
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