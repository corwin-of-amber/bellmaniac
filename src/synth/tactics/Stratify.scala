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
import semantics.TypeTranslation.TypingSugar
import semantics.TypedLambdaCalculus
import semantics.TypeInference


object Stratify {

  import semantics.Domains._
  import semantics.Prelude._
  

  import TypeTranslation.UntypedTerm

  import Split.TermBreak
  
  class Intros(implicit env: Environment) {
    val intermediates = new collection.mutable.HashSet[TypedIdentifier]
    def apply(goal: Term) = {
      if (goal =~ ("=", 2)) {
        val List(lhs, rhs) = goal.subtrees
        env.typeOf(lhs) match {
          case Some(typ) if Reflection.isFuncType(typ) =>
            val rawtyp = TypePrimitives.rawtype(env.scope, typ)
            val qv = TypingSugar.qvars(TypePrimitives.args(rawtyp))
            val ret = TypePrimitives.ret(rawtyp)
            intermediates ++= (qv map (_.root.asInstanceOf[TypedIdentifier]))
            TypedTerm(lhs :@ (qv:_*), ret) =:= TypedTerm(rhs :@ (qv:_*), ret)
          case _ => goal
        }
      }
      else goal
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
    val i = TV("i")
    val Ijr = TV("Ijr")

    val prenv = (TypeTranslation.subsorts(scope) where (compl(J)(J0, J1)))
    val typedecl = Map(
        //< ~> ((J x J) -> B),
        Ijr ~> (((J x J)->R) -> ((J x J)->R)),
        f ~> (((J x J) -> R) -> (((J x J) /*∩ <*/) -> R)),
        c ~> (((J0 x J0) -> R) -> ((J1 x J1) -> R)),
        x ~> ((J x J) -> R) )
    
    val env = prenv ++ TypeTranslation.decl(scope, typedecl)

    // f := c / I    ( := \x i. c x i / x i )
    
    // need to prove
    // c x = c (f x)
    
    val termb = new TermBreak(env)

    val (_, cxcfx) = 
      TypeInference.infer( (x ↦ (c :@ (x :: (J0 -> (J0 -> R))))) =:= (x ↦ (c :@ ((f :@ x) :: (J0 -> (J0 -> R))))), typedecl )
      
    println(cxcfx)
      //  TypedTerm(c :@ (x :: (J0 -> (J0 -> R))), J -> (J -> R)) =:=
      //  TypedTerm(c :@ ((f :@ x) :: (J0 -> (J0 -> R))), J -> (J -> R))
      //TypedTerm(x ↦ (c :@ (x :: (J0 -> (J0 -> R)))), (J -> (J -> R)) -> (J -> (J -> R))) =:=
       //         TypedTerm(x ↦ (c :@ ((f :@ x) :: (J0 -> (J0 -> R)))), (J -> (J -> R)) -> (J -> (J -> R)))
                
    val intros = new Intros()(env)
    val eq = TypedLambdaCalculus.simplify(intros(cxcfx))
    println(eq toPretty)
    
    //System.exit(0)
    
    val (eq_id, eq_t) = termb(eq) //.subtrees(0))
    //val (cfx, cfx_t) = termb(eq.subtrees(1))
    //val (cx, cx_t) = termb(TypedLambdaCalculus.simplify((x ↦ (c :@ (x :: (J0 -> (J0 -> R))))) :@ x))
    //val (cfx, cfx_t) = termb(TypedLambdaCalculus.simplify((x ↦ (c :@ ((f :@ x) :: (J0 -> (J0 -> R))))) :@ x))
    //val (cx, cx_t) = termb(c :@ (x :: (J0 -> (J0 -> R))))
    //val (cfx, cfx_t) = termb(c :@ ((f :@ x) :: (J0 -> (J0 -> R))))
    
    val assumptions = eq_t/*cx_t ++ cfx_t*/ ++ List(
        Ijr =:= { val x = T($v("α")) ; x ↦ x },
        f =:= TypedTerm(c /: Ijr, (J->(J->R)) -> (J->(J->R)))
      )
    
    val goals = List(eq_id) //cx =:= cfx)
        
    
    val symbols = typedecl.keys ++ termb.intermediates // List(<, Ijr, c, f) ++ (termb.intermediates map (T(_)))
    
    val reflect = new Reflection(env, typedecl)
    
    reflect.currying ++= symbols filter (x => Reflection.isFuncType(env.typeOf_!(x))) map 
                                        (symbol => (symbol, reflect.overload(symbol))) toMap

    for (symbol <- symbols) {
      println(s"${T(symbol).untype} :: ${env.typeOf(symbol).get toPretty}")
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