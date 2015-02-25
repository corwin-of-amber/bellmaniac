package synth.tactics

import syntax.Identifier
import syntax.AstSugar._
import semantics.Scope
import semantics.FunctionType
import semantics.TypeTranslation
import semantics.TypeTranslation.Environment
import semantics.TypeTranslation.{TypedIdentifier,TypedTerm}
import semantics.Reflection
import semantics.TypePrimitives



object Split {

  import semantics.Domains._
  import semantics.Prelude._
  

  class TermBreak(val env: Environment) {
    
    import TypeTranslation.UntypedTerm
    
    val leaves = collection.mutable.Set[Term]()
    
    def apply(term: Term): (Term, List[Term]) = {
      val (id, eqs) = term0(term)
      if (id.isLeaf) leaves += id
      (id, eqs)
    }
    
    def term0(term: Term): (Term, List[Term]) = {
      if (term.isLeaf) {
        env typeOf term match {
          case Some(typ) => (term, List())
          case _ => throw new Scope.TypingException(s"undeclared: '$term'")
        }
      }
      else if (term =~ ("@", 2)) {
        val List((func_id, func_terms), (arg_id, arg_terms)) = term.subtrees map apply
        val (func_par, func_ret) = TypePrimitives.curry(env.typeOf_!(func_id))(env.scope)
        val app = T(TypedIdentifier($v(s"${func_id.untype}${arg_id.untype}"), func_ret))
        (app, func_terms ++ arg_terms :+ (app =:= TypedTerm(func_id :@ arg_id, func_ret)))
      }
      else if (term =~ ("::", 2)) {
        val List(expr, typ) = term.subtrees
        val (expr_id, expr_terms) = this(expr)
        val cast = T(TypedIdentifier($v(s"${expr_id.untype}'"), env.typeOf_!(expr_id)))
        assert(expr_id.isLeaf)
        (cast, expr_terms :+ (cast =:= T(TypedIdentifier(expr_id.root, typ))))
      }
      else if (term =~ ("↦", 2)) {
        val fun = T(TypedIdentifier($v("↦"), env.typeOf_!(term)))
        (fun, List(fun =:= term)) // TODO
      }
      else throw new Scope.TypingException(s"don't quite know what to do with ${term toPretty}")
    }
    
  }
  

  import TypeTranslation.UntypedTerm
    
  
  def main(args: Array[String]): Unit = {
    import examples.Paren._
    implicit val scope = new Scope
    
    val N = T(S("N"))
    
    scope.sorts.declare(N.root)
    scope.sorts.declare(J.root)
    scope.sorts.declare(R.root)
    scope.sorts.declare(J0.root :<: J.root)
    scope.sorts.declare(J1.root :<: J.root)
    
    def _0 = TV("0")
    val z = TV("z")
    val s = TV("s")
    val argmin = TV("argmin")
    val ↓ = TV("↓")

    val prenv = (TypeTranslation.subsorts(scope) where (compl(J)(J0, J1)))
    val typedecl = Map(
        < ~> ((N x N) -> B),
        _0 ~> N,
        z ~> (N -> B),
        s ~> (N -> N),
        min ~> ((N -> R) -> R),
        argmin ~> ((N -> R) -> N),
        g ~> (N -> R),
        i ~> N,
        x ~> R)
        
    val env = prenv ++ TypeTranslation.decl(scope, typedecl)

    // f := c / I    ( := \x i. c x i / x i )
    
    // need to prove
    // c x = c (f x)
    
    val termb = new TermBreak(env)

    val (g0, g0_t) = termb(TypedTerm(i ↦ x, N -> R) :: ((N ∩ z) -> R))
    val (cx, cx_t) = termb(min :@ g)
    val (zi, zi_t) = termb(z :@ i)
    
   
    import TypeTranslation.TypingSugar._
    
    val assumptions = cx_t ++ g0_t ++ zi_t ++ List(g =:= g0,
        ∀:(N, (i => (z :@ i) <-> (i =:= _0))),
        min =:= { val g = T($v("g")) ; TypedTerm(g ↦ (g :@ TypedTerm(argmin :@ g, N)), (N->R) -> R) } )
    
    val goals = List(↓(g :@ i) -> (_0 =:= i),
        ↓(cx) -> ↓(TypedTerm(argmin :@ g, N)),
        ↓(cx) -> ((cx =:= x) & (_0 =:= TypedTerm(argmin :@ g, N))))
        
    
    val symbols = (typedecl.keys map (T(_))) ++ termb.leaves
    
    val reflect = new Reflection(env, typedecl)
    
    reflect.currying ++= symbols filter (x => Reflection.isFuncType(env.typeOf_!(x))) map 
                                        (symbol => (symbol.root, reflect.overload(symbol.root))) toMap

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
    
  }
  
}