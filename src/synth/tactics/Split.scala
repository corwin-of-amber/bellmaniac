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
import semantics.TypeTranslation.Declaration
import semantics.TypeTranslation.TypedTerm
import semantics.Scope.TypingException
import semantics.smt.Z3Gate
import semantics.LambdaCalculus



object Split {
  
  import AstSugar._
  import semantics.Domains._
  import semantics.Prelude._
  
  object Reflection {
    case class Consolidated(term: Term) extends Term(term.root, term.subtrees)
    def isConsolidated(term: Term) = term match {
      case Consolidated(_) | TypedTerm(_, Consolidated(_)) => true
      case _ => false
    }
  }
  
  class Reflection(val env: Environment) {

    import TypeTranslation.Declaration
    import Reflection._

    val funcSymbols = (for ((_, d) <- env.decl; s <- d.symbols if isFunc(s)) yield s).toSet
    val funcSymbolsU = funcSymbols map {x => x.untype -> x} toMap
    
    def isFuncType(typ: Term) = typ.root == "->"
    def isFunc(v: TypedIdentifier) = isFuncType(v.typ)
        
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
    
    val quantified = (for ((k,v) <- env.decl; phi <- v.precondition; q <- collectQuantified(phi)) yield q) toSet
    val consts = (for ((k,v) <- env.decl; phi <- v.precondition; c <- collectConsts(phi)) yield c) toSet
    /*
    val abstracts = collection.mutable.Map[Identifier,TypedIdentifier]()
    val capsules = collection.mutable.Map[Identifier,TypedIdentifier]()
    */
    //-----------------
    // Abstraction Part
    //-----------------
    
    import TypePrimitives.rawtype
    
    def abstype(typ: Term): Term = {
      if (isFuncType(typ)) T(env.scope.functypes(rawtype(env.scope, typ)).faux)
      else typ
    }
   /*
    def turnAbstract0(decl: Declaration) = {
      val ftype = env.scope.functypes(decl.head.typ)
      val absdecl = ftype.abs(decl)
      abstracts += decl.head -> absdecl.head
      abstracts += decl.support -> absdecl.support
      absdecl
    }
    
    def turnAbstract0(symbol: Identifier) =  env typeOf symbol match {
      case Some(typ) =>
        val ftype = env.scope.functypes(typ)
        val abssymbol = ftype.abs(symbol)
        abstracts += symbol -> abssymbol
        abssymbol
      case _ => throw new Scope.TypingException(s"can't figure out the type of $symbol")
    }
    
    def turnAbstract(symbol: Identifier): TypedIdentifier = {
      abstracts get symbol match {
        case Some(abs) => abs
        case _ =>
          if (consts.toSeq contains symbol) {
            turnAbstract0(env(symbol))
            abstracts(symbol)  // should contain it now
          }
          else turnAbstract0(symbol)
      }
    }
    
    def turnAbstract(phi: Term): Term = {
      if (phi.isLeaf && ((quantified ++ consts).toSeq contains phi.root)) T(turnAbstract(phi.root))
      else T(phi.root, phi.subtrees map turnAbstract _)
    }
    
    def turnAbstract(decl: Declaration): Declaration = {
      Declaration(decl.symbols, decl.precondition map turnAbstract _)
    }
    
    def turnAbstract(env: Environment): Environment = 
      new Environment(env.scope, env.decl map { case (k,v) => (k, turnAbstract(v)) })    

    //-------------------
    // Encapsulation Part
    //-------------------
    
    def captype(typ: Term): Term =
      if (typ.root == "->") T(typ.root)(typ.subtrees dropRight 1 map abstype _)(captype(typ.subtrees.last))
      else typ
    
    def captype(symbol: Identifier): Term = env typeOf symbol match {
      case Some(typ) => captype(typ)
      case _ => throw new Scope.TypingException(s"can't figure out the type of $symbol")
    }
    
    def encapsulate(symbol: Identifier): TypedIdentifier = {
      capsules get symbol match {
        case Some(cap) => cap
        case _ =>
          val cap = TypedIdentifier(new Identifier(s"${symbol.literal}°", symbol.kind, new Uid), captype(symbol))
          capsules += (symbol -> cap)
          cap
      }
    }
    
    def encapsulate(phi: Term): Term = {
      if ((phi.root.kind == "variable" || phi.root.kind == "function" || phi.root.kind == "predicate") && 
          (phi.subtrees exists (x => abstracts.values exists (_ == x.root))))
        T(encapsulate(phi.root))(phi.subtrees map (x => if (x.isLeaf) T(abstracts get x.root getOrElse x.root) else encapsulate(x) ))
      else
        T(phi.root)(phi.subtrees map encapsulate _)
    }
    
    def encapsulate(decl: Declaration): Declaration = {
      Declaration(decl.symbols, decl.precondition map encapsulate _)
    }
    
    def encapsulate(env: Environment): Environment = 
      new Environment(env.scope, env.decl map { case (k,v) => (k, encapsulate(v)) })
    
    def reflEnv = encapsulate(turnAbstract(env))
    */
    
    //-------------------
    // Consolidation Part
    //-------------------
    
    def consolidate(term: Term) = consolidate1(term)
    
    def consolidate1(term: Term): Term = {
      def preserve(newterm: Term) = term match {
        case typed: TypedTerm => TypedTerm(newterm, typed.typ)
        case _ => newterm
      }
      if (isConsolidated(term)) term
      else preserve(consolidate0(term))
    }
    
    def consolidate0(term: Term): Term = {
      def sub = term.subtrees map consolidate1
      if (term =~ ("@", 2)) {
        val List(fun, arg) = sub
        if (currying contains fun.root) fun(arg)
        else if (fun.root == "/") {    /* distribute '@' over '/' */
          consolidate1(T(fun.root, fun.subtrees map (_ :@ arg)))
        }
        else if (fun =~ ("↦", 2)) {    /* beta reduction */
          consolidate1(LambdaCalculus.beta(fun, arg))
        }
        else throw new Exception(s"application term cannot be consolidated: '${fun toPretty} @ ${arg toPretty}'")
      }
      else if (term =~ ("=", 2)) {
        val List(lhs, rhs) = sub
        val typ = env.typeOf_!(lhs)
        if (typ =~ ("->", 2)) {
          val va = T(TypedIdentifier(new Identifier("$" + lhs.subtrees.length, "variable", new Uid), typ.subtrees(0)))
          if (isFuncType(env.typeOf_!(va)))
            currying += (va.root -> (overload(va.root) take 1))  /* quantified var: has only one version */
          ∀(va)(consolidate1(TypedTerm(lhs :@ va, typ.subtrees(1)) =:= TypedTerm(rhs :@ va, typ.subtrees(1))))
        }
        else if (rhs =~ ("/", 2)) {
          val List(trueB, falseB) = rhs.subtrees
          val cond = TI("↓")(trueB)
          && (List(cond -> (lhs =:= trueB), (~cond) -> (lhs =:= falseB)) map consolidate1)
        }
        else {
          (TI("↓")(lhs) <-> TI("↓")(rhs)) & (TI("↓")(lhs) -> (lhs =:= rhs))
        }
      }
      else if (term =~ ("∀", 2)) {
        term.subtrees(0).root match {
          case tid: TypedIdentifier => if (isFuncType(tid.typ))
            currying += (tid -> (overload(tid) take 1))  /* quantified var: has only one version */
        }
        T(term.root, sub)
      }
      else T(term.root, sub)
    }
    
    //--------------
    // Currying Part
    //--------------
    
    import TypeTranslation.{MicroCode,In,Out,Check}
    import TypePrimitives.arity
    
    val currying = collection.mutable.Map[Identifier, List[TypedIdentifier]]()
    
    def overload(typ: Term): List[Term] = overload(TypeTranslation.emit(env.scope, typ)) map (TypeTranslation.canonical(env.scope, _))
    
    def overload(symbol: Identifier): List[TypedIdentifier] = {
      val ns = new Uid
      val typ = env.typeOf(symbol).get
      for (otyp <- overload(typ)) yield {
        TypedIdentifier(new Identifier(s"${symbol.literal}[${arity(otyp)}]", "function", ns), otyp)
      }
    }
      
    def overload(micro: List[MicroCode]): List[List[MicroCode]] = List(Out(abstype(TypeTranslation.canonical(env.scope, micro)))) ::
      (micro match {
        case In(typ) :: tail => 
          val arg = abstype(typ)
          (overload(tail) map (In(arg) :: _))
        case _ => Nil
      })

   import syntax.Scheme
      
   def uncurry(term: Term): Term = {
     if (term =~ ("↓",1)) {
       val atom = term.subtrees(0)
       val checks = atom.root match {
         case tid: TypedIdentifier =>
           val (vars, ret, assertions) = TypeTranslation.contract(tid.untype, TypeTranslation.emit(env.scope, tid.typ))
           if (assertions.isEmpty) List()
           else List(new Scheme.Template(vars, &&(assertions))(atom.subtrees))
         case _ => List()
       }
       &&(T(term.root)(uncurry(atom)) :: checks)
     }
     else if (term.root == "@") {
       uncurry1(term.subtrees(0), term.subtrees drop 1)
     }
     else uncurry0(term)
    }
      
    def uncurry0(term: Term): Term = currying get term.root match {
      case Some(oset) => oset find (x => arity(x.typ) == term.subtrees.length) match {
        case Some(variant) => T(variant, term.subtrees map uncurry _)
        case _ => term.subtrees match {
          case args :+ last => 
            val fun = uncurry(T(term.root, args))
            val typ = env.typeOf_!(fun)
            env.scope.functypes.values find (_.faux == typ.root) match {
              case Some(functype) => T(functype.app.head, List(fun, uncurry(last)))
              case _ => throw new Scope.TypingException(s"unrecognized reflection type '$typ'")
            }
          case _ =>
            throw new Scope.TypingException(s"no overloaded variant, in '${term toPretty}'")
        }
      }
      case _ => T(term.root, term.subtrees map uncurry _)
    }
      
    def uncurry1(fun: Term, args: List[Term]) = {
      val ucfun = uncurry(fun)
      val typ = env.typeOf_!(ucfun)
      env.scope.functypes.values find (_.faux == typ.root) match {
        case Some(functype) => T(functype.app.head, ucfun :: (args map uncurry))
        case _ => throw new Scope.TypingException(s"unrecognized reflection type '$typ'")
      }
    }
    
    //-------------
    // Support Part
    //-------------
    
    val supports = collection.mutable.Map[Identifier, TypedIdentifier]()
    
    def supportType(typ: Term): Term =
      if (typ.root == "->") T(typ.root, (typ.subtrees dropRight 1) :+ supportType(typ.subtrees.last))
      else B
    
    def support(symbol: Identifier) = supports get symbol match {
      case Some(supp) => supp
      case _ =>
        val supp = TypedIdentifier(new Identifier(s"|${symbol.literal}|", "predicate", new Uid),
                                   supportType(env.typeOf_!(symbol)))
        supports += symbol -> supp
        supp
    }
    
    def support(term: Term): Term =
      if (term =~ ("↓",1)) {
        val atom = term.subtrees(0)
        T(support(atom.root), atom.subtrees map support)
      }
      else
        T(term.root, term.subtrees map support)
    
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

    val prenv = (TypeTranslation.subsorts(scope) where (compl(J)(J0, J1)))
    
    val env = prenv ++
      TypeTranslation.decl(scope, 
          Map(f ~> ((J -> R) -> (J -> R)),
              c ~> ((J0 -> R) -> (J1 -> R)),
              x ~> (J -> R),
              i ~> J )) 

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
    
    import TypeTranslation.TypingSugar._
    import Split.Reflection.Consolidated
    
    val assumptions = List(
        Ijr =:= { val x = $v ; T(x) ↦ T(x) },
        f =:= TypedTerm(c /: Ijr, (J->R) -> (J->R)),
        xj0 =:= T(TypedIdentifier(x.root, J0 -> R)),
        cx =:= TypedTerm(c :@ xj0, J -> R),
        fx =:= TypedTerm(f :@ x, J -> R),
        fxj0 =:= T(TypedIdentifier(fx.root, J0 -> R)),
        cfx =:= TypedTerm(c :@ fxj0, J -> R),
        
        // (these should be autogenerated by TypeTranslation / Reflection)
        ∀:(J, i => J0(i) <-> ~J1(i)),
        ∀:(J -> R, J, (x, i) => (TI("↓")(c(x, i)) -> J1(i))),     // c :: (J0 -> R) -> J1 -> R
        // currying
        ∀:(J, (i) => (TypedTerm(fxj0(i), R) =:= TypedTerm(fxj0 :@ i, Consolidated(R)))),
        ∀:(J, (i) => (TypedTerm(xj0(i), R) =:= TypedTerm(xj0 :@ i, Consolidated(R)))),
        ∀:(J, (i) => (TypedTerm(x(i), R) =:= TypedTerm(x :@ i, Consolidated(R)))),
        ∀:(J->R, (x,y) => ∀:(J, i => TypedTerm(x(i), R) =:= TypedTerm(y(i), R)) -> Consolidated(x =:= y))
      )
    
    val goal = (cx =:= cfx)
        
    val symbols = List(Ijr, c, f, x, xj0, cx, fx, fxj0, cfx)
    
    import TypeTranslation.{UntypedTerm}
    
    val reflect = new Reflection(env)
    
    reflect.currying ++= symbols map (symbol => (symbol.root, reflect.overload(symbol.root))) toMap
    
    for (symbol <- symbols) {
      println(s"${symbol.untype} :: ${env.typeOf(symbol.root).get toPretty}")
      for (variant <- reflect.currying(symbol.root))
        println(s"   ${variant toPretty}")
    }
      
    println("· " * 25)
    
    
    val (z3g, _) = TypeTranslation toSmt List(prenv) // new Z3Gate
    
    val fo_assumptions =
      for (atn <- assumptions) yield {
        println(atn.untype toPretty)
        val atn_c = reflect.consolidate(atn)
        println(s"  ${atn_c toPretty}")
        val atn_u = reflect.uncurry(atn_c)
        println(s"  ${atn_u toPretty}")
        val atn_s = reflect.support(atn_u)
        println(s"  ${atn_s toPretty}")
        atn_s
      } 
    
    import syntax.Piping._
    val fo_goal = goal |> reflect.consolidate |> reflect.uncurry |> reflect.support
    
    println("-" * 60)
    
    
    
    val status =
      z3g.solveAndPrint(
        for (atn <- fo_assumptions) yield {
          println(s" * ${atn.untype toPretty}")
          z3g.formula(atn)
        },
        List(z3g.formula(fo_goal)))
        
    
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