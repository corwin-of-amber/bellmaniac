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
import syntax.transform.TreeSubstitution
import synth.pods.NilPod



object Split {

  import semantics.Domains._
  import semantics.Prelude._
  

  class TermBreak(val env: Environment) {
    
    import TypeTranslation.UntypedTerm
    def rawtype(typ: Term) = TypePrimitives.rawtype(env.scope, typ)
    def isRaw(typ: Term) = TypePrimitives.isRaw_shallow(env.scope, typ)
    
    val intermediates = collection.mutable.Set[Identifier]()
    val perceivedType = collection.mutable.Map[Identifier, Term]()
    
    def apply(term: Term): (Term, List[Term]) = {
      val (id, eqs) = term0(term)
      if (id.isLeaf) intermediates += id.root
      env.typeOf(term) match {
        case Some(typ) if id.isLeaf && !isRaw(typ) && perceivedType.get(id.root) != Some(typ) =>
          val cast = T(TypedIdentifier($v(s"${id.untype}'"), rawtype(typ)))
          intermediates += cast.root
          perceivedType += (cast ~> typ)
          (cast, eqs :+ (cast =:= TypedTerm(T(TypedIdentifier(id.root, typ)), typ)))
        case _ =>
          (id, eqs)
      }
    }
    
    def term0(term: Term): (Term, List[Term]) = {
      def reapply(term: Term) = apply(term)
      if (term.isLeaf) {
        env typeOf term match {
          case Some(typ) => (term, List())
          case _ => throw new Scope.TypingException(s"undeclared: '$term'")
        }
      }
      else if (term =~ ("@", 2)) {
        val List((func_id, func_terms), (arg_id, arg_terms)) = term.subtrees map reapply
        val (func_par, func_ret) = TypePrimitives.curry(rawtype(env.typeOf_!(func_id)))(env.scope)
        val app = T(TypedIdentifier($v(s"${func_id.untype}${arg_id.untype}"), func_ret))
        (app, func_terms ++ arg_terms :+ (app =:= TypedTerm(func_id :@ arg_id, func_ret)))
      }
      else if (term =~ ("/", 2)) {
        val List((fore_id, fore_t), (back_id, back_t)) = term.subtrees map reapply
        val ore = T(TypedIdentifier($v(s"${fore_id.untype}/${back_id.untype}"), rawtype(env.typeOf_!(fore_id))))
        (ore, fore_t ++ back_t :+ (ore =:= TypedTerm(fore_id /: back_id, env.typeOf_!(ore))))
      }
      else if (term =~ ("=", 2)) {
        val List((lhs_id, lhs_t), (rhs_id, rhs_t)) = term.subtrees map reapply
        val eq = T(TypedIdentifier($v(s"${lhs_id.untype}=${rhs_id.untype}"), B))
        (eq, lhs_t ++ rhs_t :+ (eq <-> TypedTerm(lhs_id =:= rhs_id, B)))
      }
      else if (term =~ ("::", 2)) {
        val List(expr, typ) = term.subtrees
        val (expr_id, expr_terms) = this(expr)
        val cast = T(TypedIdentifier($v(s"${expr_id.untype}'"), rawtype(env.typeOf_!(expr_id))))
        assert(expr_id.isLeaf)
        (cast, expr_terms :+ (cast =:= TypedTerm(T(TypedIdentifier(expr_id.root, typ)), typ)))
      }
      else if (term =~ ("↦", 2)) {
        val (body_id, body_t) = apply(term.subtrees(1))
        val fun = T(TypedIdentifier($v("↦"), rawtype(env.typeOf_!(body_id))))
        val arg = term.subtrees(0)
        println(s"**** ${term toPretty}")
        val (genbody_syms, genbody_t) = generalize(body_t :+ (fun =:= body_id), arg)
        (T(genbody_syms(fun.root)), genbody_t) // TODO
      }
      else if (term =~ (":", 2)) {
        term0(term.subtrees(1))
      }
      else throw new Scope.TypingException(s"don't quite know what to do with ${term toPretty}")
    }
    
    import semantics.TypedLambdaCalculus.{preserve=>preserve0,typecheck0}
    
    def generalize(eqs: List[Term], arg: Term): (Map[Identifier,Identifier], List[Term]) = {
      /**/ assume(eqs forall (_ =~ ("=", 2))) /**/
      /**/ assume(eqs forall (_.subtrees(0).isLeaf)) /**/
      val sym = eqs map (_.subtrees(0).root)
      val gensym = sym map (x => (x, TypedIdentifier(x, rawtype(env.typeOf_!(arg) -> env.typeOf_!(x))))) toMap
      val subst = new TreeSubstitution(sym map (x => (T(x), T(gensym(x)) :@ arg))) {
        override def preserve(old: Term, new_ : Term) = preserve0(old, new_)
      }
      val geneqs =
      for (eq <- eqs) yield {
        println(eq toPretty)
        val lhs = T(gensym(eq.subtrees(0).root))
        val rhs = eta(typecheck0(arg ↦ subst(eq.subtrees(1))))
        println(s"   ${lhs } = ${rhs }")
        lhs =:= rhs
      }
      intermediates --= gensym.keys
      intermediates ++= gensym.values
      //if (!eqs.isEmpty) System.exit(0)
      (gensym, geneqs)
    }
    
    def eta(term: Term) =
      if (term =~ ("↦", 2) && term.subtrees(1) =~ ("@", 2) && term.subtrees(1).subtrees(1) == term.subtrees(0))
        preserve0(term, term.subtrees(1).subtrees(0))
      else
        term
    
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
    def _1 = TV("1")
    val z = TV("z")
    val nz = TV("~z")
    val s = TV("s")
    val p = TV("p")
    //val nilN = TV("nil.N")
    val minN = TV("min.N")
    val argminN = TV("argmin.N")
    //val nilJ = TV("nil.J")
    val minJ = TV("min.J")
    val argminJ = TV("argmin.J")
    val ↓ = TV("↓")

    val y = TV("y")
    val g = TV("g")
    val h = TV("h")
    
    val prenv = (TypeTranslation.subsorts(scope) where (compl(J)(J0, J1)))
    val typedecl = Map(
        < ~> ((R x R) -> B),
        _0 ~> N,
        _1 ~> N,
        z ~> (N -> B), nz ~> (N -> B),
        s ~> (N -> N),
        p ~> ((N ∩ nz) -> N),
        cons ~> (R -> ((N -> R) -> (N -> R))),
        //nilN ~> (N -> R),
        minN ~> ((N -> R) -> R),
        argminN ~> ((N -> R) -> N),
        //nilJ ~> (J -> R),
        minJ ~> ((J -> R) -> R),
        argminJ ~> ((J -> R) -> J),
        i ~> J,
        g ~> (J0 -> R),
        h ~> (J1 -> R),
        x ~> R, y ~> R)
        
    val env = prenv ++ TypeTranslation.decl(scope, typedecl)
    
    val termb = new TermBreak(env)
    
    def singleton(x: Term) = {
      val r = env.typeOf_!(x)
      val i = T(TypedIdentifier($v("i"), N))
      //TypedTerm(i ↦ x, N -> r) :: ((N ∩ z) -> r)
      TypedTerm(i ↦ x, (N ∩ z) -> r)
    }
    def compose(f: Term, g: Term) = {
      val (tf, tg) = (env.typeOf_!(f), env.typeOf_!(g))
      val ((af, rf), (ag, rg)) = (TypePrimitives.curry(tf), TypePrimitives.curry(tg))
      val i = T(TypedIdentifier($v("j"), N))
      TypedTerm(i ↦ (g :@ (f :@ i)), af -> rg)
    }
    def consM(x: Term, l: Term) = TypedTerm(singleton(x) /: compose(p, l), env.typeOf_!(l))
    
    def pair(x: Term, y: Term) = {
      val r = env.typeOf_!(x)
      (TypedTerm(i ↦ x, N -> r) :: ((N ∩ z) -> r)) /: TypedTerm(i ↦ y, N -> r)
    }
    
    /*
    //val (h, h_t) = termb(cons(y, nil))
    val (gh, gh_t) = termb(g /: h)
    val (minh, minh_t) = termb(minJ :@ h)
    //val (g, g_t) = termb(TypedTerm(singleton(x) /: h, N -> R)) //cons(x, h))//cons(y, nil)))
    val (ming, ming_t) = termb(minJ :@ g)
    //val (mingh, mingh_t) = termb(minJ :@ gh)
    val (xy, xy_t) = termb(cons(ming, cons(minh, nilN)))
    //val (minxy, minxy_t) = termb(minN :@ xy)
    //val (minxy, minxy_t) = termb(minN :@ pair(ming, minh))
   */
    
    val (cons_id, cons_t) = {
      val (x, xs) = (T(TypedIdentifier($v("x"), R)), T(TypedIdentifier($v("xs"), N -> R)))
      //termb(cons =:= (x ↦ singleton(x)))
      termb(cons =:= (x ↦ (xs ↦ (singleton(x) /: compose(p, xs)))))
    }
    
    //val assumptions = cons_t
    //val goals = List()
    
    val nilN = NilPod(N, R)
    
    val mac = nilN.macros
    import semantics.TypedLambdaCalculus
    def expand(term: Term): Term = {
      val eterm = TypedLambdaCalculus.preserve(term, T(term.root, term.subtrees map expand))
      mac get eterm.root flatMap (_(eterm)) match {
       case Some(newTerm) => newTerm
       case _ => eterm
      }
    }
    
    import semantics.Binding
    import semantics.TypeInference
    import syntax.Unify
    
    import java.util.logging.Level
    TypeInference.log.setLevel(Level.INFO)
    
    def e(term: Term) = expand(TypeInference.infer(Binding.prebind(term), typedecl)._2)
    def be(term: Term) = termb(e(term))

    //println(minN :@ (consM(TypedTerm(minJ :@ g, R), consM(TypedTerm(minJ :@ h, R), TypedTerm(nil, N->R)))))
    //println(e( minN :@ (consM(TypedTerm(minJ :@ g, R), consM(TypedTerm(minJ :@ h, R), TypedTerm(nil, N->R)))) ))
    
    
    val (mingh, mingh_t) = be(minJ :@ (g /: h))
    val (xy, xy_t) = be(minJ :@ g)
    val (xx, xx_t) = be(minJ :@ h)
    val (minxy, minxy_t) = //be(minN :@ consM(TypedTerm(minJ :@ g, R), TypedTerm(nil, N -> R)))
      //be(minN :@ (consM(TypedTerm(minJ :@ g, R), TypedTerm(nil, N -> R))))
      //be(minN :@ (consM(xy/*TypedTerm(minJ :@ g, R)*/, consM(xx, TypedTerm(nil, N -> R)))))
      be( minN :@ (consM(TypedTerm(minJ :@ g, R), consM(TypedTerm(minJ :@ h, R), TypedTerm(nil, N->R)))) )
      //termb(minN :@ (consM(TypedTerm(minJ :@ g, R), consM(TypedTerm(minJ :@ h, R), nilN.nil))))
    
    //System.exit(0)
    
    import TypeTranslation.TypingSugar._
    
    
    
    val assumptions = /*gh_t ++ ming_t ++ minh_t ++ mingh_t ++*/ xx_t ++ xy_t /*++ cons_t*/ ++ mingh_t ++ minxy_t ++ List(
        ↓(_0) & ↓(_1) & (TypedTerm(s :@ _0, N) =:= _1),
        ∀:(N, i => (↓(s :@ i) -> ~(TypedTerm(s :@ i, N) =:= i) )),
        ∀:(N, i => (↓(s :@ i) -> (TypedTerm(p :@ (s :@ i), N) =:= i) )),
        //∀:(N, i => ~(↓(nilN :@ i))),
        //cons_id,
        //∀:(J, i => ~(↓(nilJ :@ i))),
        ∀:(R, (i, j) => (< :@ i :@ j) -> ~(< :@ j :@ i)),
        ∀:(R, (i, j) => ~(< :@ i :@ j) ->: ~(< :@ j :@ i) ->: (i =:= j)),
        z <-> (i ↦ (i =:= _0)),
        nz <-> (i ↦ ~(z :@ i)),
        minN =:= { val g = T($v("g")) ; TypedTerm(g ↦ (g :@ TypedTerm(argminN :@ g, N)), (N->R) -> R) },
        minJ =:= { val g = T($v("g")) ; TypedTerm(g ↦ (g :@ TypedTerm(argminJ :@ g, J)), (J->R) -> R) },
        ∀:(N->R, N, (g, i) => (↓(g :@ i) -> (↓(minN :@ g) & ~(< :@ (g :@ i) :@ (minN :@ g)))) ),
        ∀:(J->R, J, (g, i) => (↓(g :@ i) -> (↓(minJ :@ g) & ~(< :@ (g :@ i) :@ (minJ :@ g)))) )
      ) ++ nilN.decl.precondition
    
    val goals = List(
        //((minxy =:= ming) | (minxy =:= minh)) , //↓(TypedTerm(argmin :@ g, N)),
        //(↓(< :@ ming :@ minh) & (< :@ ming :@ minh)) -> (minxy =:= ming),
        mingh =:= minxy
        )
        
    
    val symbols = typedecl.keys ++ List(nilN.nil.root) ++ termb.intermediates
    
    val reflect = new Reflection(env, typedecl)
    
    reflect.currying ++= symbols filter (x => Reflection.isFuncType(env.typeOf_!(x))) map 
                                        (symbol => (symbol, reflect.overload(symbol))) toMap

    for (variants <- reflect.currying.values)
      reflect.alwaysDefined ++= (variants dropRight 1)
                                        
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
    
  }
  
}