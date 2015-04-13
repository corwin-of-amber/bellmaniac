package synth.tactics

import syntax.Identifier
import syntax.AstSugar._
import semantics.Scope
import semantics.FunctionType
import semantics.TypedTerm
import semantics.TypeTranslation
import semantics.TypeTranslation.Environment
import semantics.TypeTranslation.TypedIdentifier
import semantics.Reflection
import semantics.TypePrimitives
import syntax.transform.TreeSubstitution
import synth.pods.NilPod
import synth.pods.NatPod
import synth.pods.ConsPod
import semantics.TypedLambdaCalculus
import synth.pods.MinPod
import semantics.pattern.MacroMap



object Split {

  import semantics.Domains._
  import semantics.Prelude._
  

  class TermBreak(val env: Environment) {
    
    import semantics.UntypedTerm
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
        //println(s"**** ${term toPretty}")
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
        //println(eq toPretty)
        val lhs = T(gensym(eq.subtrees(0).root))
        val rhs = eta(typecheck0(arg ↦ subst(eq.subtrees(1))))
        //println(s"   ${lhs } = ${rhs }")
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
  

  import semantics.UntypedTerm
    
  
  def main(args: Array[String]): Unit = {
    import examples.Paren._
    implicit val scope = new Scope
    
    val N = T(S("N"))
    
    scope.sorts.declare(N.root)
    scope.sorts.declare(J.root)
    scope.sorts.declare(R.root)
    scope.sorts.declare(J0.root :<: J.root)
    scope.sorts.declare(J1.root :<: J.root)
    
    //val _0 = TV("0")
    //val _1 = TV("1")
    //val z = TV("z")
    //val nz = TV("~z")
    //val s = TV("s")
    //val p = TV("p")
    //val nilN = TV("nil.N")
    val minN = TV("min.N")
    val argminN = TV("argmin.N")
    //val nilJ = TV("nil.J")
    val minJ = TV("min.J")
    val argminJ = TV("argmin.J")
    //val ↓ = TV("↓")

    val y = TV("y")
    val g = TV("g")
    val h = TV("h")
    
    import NatPod.{_0,_1,z,nz,s,p}
    
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
        
    implicit val env = prenv ++ TypeTranslation.decl(scope, typedecl)
    
    val termb = new TermBreak(env)
    
    //val assumptions = cons_t
    //val goals = List()
    
    val nilNR = NilPod(N, R)
    val consR = ConsPod(R)
    val minNR = MinPod(N, R, <)
    val minJR = MinPod(J, R, <)
    
    def liftedOrElse[A,B,C](m1: Map[A, B => Option[C]], m2: Map[A, B => Option[C]]) = {
      m1 ++ (m2 map { case(k,v2) =>
          m1 get k match {
            case Some(v1) => (k, { (b: B) => v1(b) orElse { v2(b) } })
            case _ => (k, v2)
          }
        })
    }
    
    val mac = MacroMap.empty ++ nilNR.macros ++ consR.macros ++ minNR.macros ++ minJR.macros
    import semantics.TypedLambdaCalculus
    def expand(term: Term): Term = {
      val eterm = TypedLambdaCalculus.preserve(term, T(term.root, term.subtrees map expand))
      def head(term: Term): Identifier = if (term =~ ("@", 2)) head(term.subtrees(0)) else term.root
      mac get head(eterm) flatMap (_(eterm)) match {
       case Some(newTerm) => newTerm
       case _ => eterm
      }
    }
    
    import semantics.Binding
    import semantics.TypeInference
    import syntax.Unify
    
    import java.util.logging.Level
    //TypeInference.log.setLevel(Level.INFO)
    
    def e(term: Term) = expand(TypeInference.infer(Binding.prebind(term), typedecl)._2)
    def be(term: Term) = termb({ val x = e(term); println(x toPretty); x})

    //println(minN :@ (consM(TypedTerm(minJ :@ g, R), consM(TypedTerm(minJ :@ h, R), TypedTerm(nil, N->R)))))
    //println(e( minN :@ (consM(TypedTerm(minJ :@ g, R), consM(TypedTerm(minJ :@ h, R), TypedTerm(nil, N->R)))) ))
    
    import TypeTranslation.TypingSugar._
    
    val (mingh, mingh_t) = be(minJR.min :@ (g /: h))
    val (xy, xy_t) = be(minJR.min :@ g)
    val (xx, xx_t) = be(minJR.min :@ h)
    val (minxy, minxy_t) = 
      be( min :@ (cons :@ (TypedTerm(minJR.min :@ g, R), cons :@ (TypedTerm(minJR.min :@ h, R), TypedTerm(nil, N->R)))) )
    
    
    
    val assumptions = /*gh_t ++ ming_t ++ minh_t ++ mingh_t ++*/ xx_t ++ xy_t /*++ cons_t*/ ++ mingh_t ++ minxy_t ++ List(
        //↓(_0) & ↓(_1) & (TypedTerm(s :@ _0, N) =:= _1),
        //∀:(N, i => (↓(s :@ i) -> ~(TypedTerm(s :@ i, N) =:= i) )),
        //∀:(N, i => (↓(s :@ i) -> (TypedTerm(p :@ (s :@ i), N) =:= i) )),
        //∀:(N, i => ~(↓(nilN :@ i))),
        //cons_id,
        //∀:(J, i => ~(↓(nilJ :@ i))),
        ∀:(R, (i, j) => (< :@ i :@ j) -> ~(< :@ j :@ i)),
        ∀:(R, (i, j) => ~(< :@ i :@ j) ->: ~(< :@ j :@ i) ->: (i =:= j)),
        z <-> (i ↦ (i =:= _0)),
        nz <-> (i ↦ ~(z :@ i))
        //minN =:= { val g = T($v("g")) ; TypedTerm(g ↦ (g :@ TypedTerm(argminN :@ g, N)), (N->R) -> R) },
        //minJ =:= { val g = T($v("g")) ; TypedTerm(g ↦ (g :@ TypedTerm(argminJ :@ g, J)), (J->R) -> R) },
        //∀:(N->R, N, (g, i) => (↓(g :@ i) -> (↓(minN :@ g) & ~(< :@ (g :@ i) :@ (minN :@ g)))) ),
        //∀:(J->R, J, (g, i) => (↓(g :@ i) -> (↓(minJ :@ g) & ~(< :@ (g :@ i) :@ (minJ :@ g)))) )
      ) ++ nilNR.decl.precondition ++ NatPod.axioms ++ minNR.axioms ++ minJR.axioms
    
    val goals = List(
        //((minxy =:= ming) | (minxy =:= minh)) , //↓(TypedTerm(argmin :@ g, N)),
        //(↓(< :@ ming :@ minh) & (< :@ ming :@ minh)) -> (minxy =:= ming),
        mingh =:= minxy
        )
        
    
    val symbols = typedecl.keys ++ List(nilNR.nil.root, minNR.min.root, minNR.argmin.root, minJR.min.root, minJR.argmin.root) ++ termb.intermediates
    
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