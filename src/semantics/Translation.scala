package semantics

import syntax.{Tree,Identifier,AstSugar,Scheme}
import syntax.transform.TreeSubstitution
import scala.collection.mutable.ArrayBuffer
import semantics.smt.Z3Gate



object TypeTranslation {
  
  import AstSugar._
  
  case class TypedIdentifier(symbol: Identifier, val typ: Term) 
    extends Identifier(symbol.literal, symbol.kind, symbol.ns) {
    override def toString = s"${super.toString} :: $typ"
    def toPretty = s"${super.toString} :: ${typ.toPretty}"
    def untype = new Identifier(symbol.literal, symbol.kind, symbol.ns)
  }
  
  case class Declaration(val symbols: List[TypedIdentifier], 
                         val precondition: List[Term]) {
    def this(symbols: Term*) =
      this(symbols map (_.leaf.asInstanceOf[TypedIdentifier]) toList, List())
      
    def head = symbols.head
    def support = symbols.tail find (_.kind == "predicate") getOrElse 
      { throw new Scope.TypingException(s"no support found for '$head'") }
    
    def where(fact: Term): Declaration = where(List(fact))
    def where(facts: List[Term]) = Declaration(symbols, precondition ++ facts)
    
    def toPretty = s"Declaration(${symbols map (_.toPretty) mkString ", "}; " +
                   s"${precondition map (_.untype.toPretty) mkString ", "})"
  }
  
  class Environment(val scope: Scope, val decl: Map[Identifier, Declaration]) {
    def ++(that: Environment) =
      if (scope eq that.scope) E(scope, decl ++ that.decl)
      else throw new Exception("incompatible scopes for environment merge")
    
    def ++(that: Map[_ <: Identifier, Declaration]) =  E(scope, decl ++ that)
    def +(that: (_ <: Identifier, Declaration)) =      E(scope, decl + that)
    
    def apply(symbol: Identifier) : Declaration = decl get symbol getOrElse {
        for ((_,v) <- decl; s <- v.symbols) if (s == symbol) return v
        throw new NoSuchElementException(s"symbol $symbol")
      }
    
    def typedSymbols: Stream[TypedIdentifier] =
      (for ((k,v) <- decl; s <- v.symbols) yield s) toStream
    
    def typeOf(symbol: Identifier) = symbol match {
        case t: TypedIdentifier => Some(t.typ)
        case _ => typedSymbols find (_ == symbol) map (_.typ)
      }
    
    def typeOf(term: Term): Option[Term] = term match {
      case typed: TypedTerm => Some(typed.typ)
      case _ =>
        if (term.isLeaf) typeOf(term.root) else None
    }
    
    def typeOf_!(symbol: Identifier) = typeOf(symbol) getOrElse { throw new Scope.TypingException(s"type needed for $symbol") }
    def typeOf_!(term: Term) = typeOf(term) getOrElse { throw new Scope.TypingException(s"type needed for $term") }
        
    def where(facts: Term*) = this + ($_ -> Declaration(List(), facts.toList))
  }
  
  object Environment {
    val Empty = new Environment(new Scope, Map())
  }
  
  private def E(scope: Scope, decl: Map[Identifier, Declaration]=Map()) =
    new Environment(scope, decl)
  
  def decl(scope: Scope, types: Map[Identifier, Term]): Environment =
    E(scope, types map { case (k,v) => k -> decl(scope, k, v) })
  
  def decl(scope: Scope, symbol: Identifier, typ: Term): Declaration =
    decl(symbol, emit(scope, typ))
  
  def decl(symbol: Identifier, micro: List[MicroCode]) = {
    val inner = new Namespace
    val supp = new Identifier(s"|$symbol|", "predicate", inner)
    val (vars, ret, assertions) = contract(symbol, micro)
    // symbol :: vars -> ret
    val symbol_type = TI("->", (vars map (_.typ)).toList :+ ret.typ).foldRight
    // |symbol| :: vars -> (bool)
    val supp_type = TI("->", (vars map (_.typ)).toList :+ TI("")).foldRight
    // forall vars. supp(vars) -> assertions
    val lvars = vars map (T(_))
    val precondition =
      if (assertions.isEmpty) None
      else Some( ∀(lvars)(T(supp, lvars) -> &&(assertions)) )
    new Declaration(List(TypedIdentifier(symbol, symbol_type),
                         TypedIdentifier(supp, supp_type)),
        precondition.toList)
  }
  
  def contract(symbol: Identifier, micro: List[MicroCode]) = {
    val inner = new Namespace
    val vars = new ArrayBuffer[TypedIdentifier]
    var ret: TypedTerm = null
    def freshvar = new Identifier(s"$$${vars.length}", "variable", inner)
    val assertions = new ArrayBuffer[Term]
    micro foreach {
      case In(t) => vars += (TypedIdentifier(freshvar,t))
      case Out(t) => ret = TypedTerm(T(symbol, (vars map (T(_))).toList), t)
      case Check(pred, arity) =>
        val args = if (ret != null) List(ret) else (vars takeRight arity map (T(_))).toList
        assertions += pred(args:_*)
    }
    assert(ret != null)
    (vars.toList, ret, assertions.toList)
  }
  
  def checks(symbol: Identifier, micro: List[MicroCode], args: List[Term]) = {
    val (vars, ret, assertions) = contract(symbol, micro)
    for (assertion <- assertions)
      yield new Scheme.Template(vars, assertion)(args)
  }
  
  def checks(scope: Scope, symbol: TypedIdentifier, args: List[Term]): List[Term] = 
    checks(symbol.untype, emit(scope, symbol.typ), args)
  
  def subsorts(scope: Scope) = E(scope, {
    import TypingSugar._
    val masterTypes = scope.sorts.masters
    def pred(dom: Identifier) = TI("->")(T(dom), T(S("")))
    for (master <- masterTypes; slave <- master.nodes if slave.root != Domains.⊥)
      yield slave.root -> Declaration(List(TypedIdentifier(slave.root, pred(master.root))), 
          if (slave eq master) List(∀:(T(master.root), x => T(master.root)(x))) else List()) 
  }.toMap)
  
  /**
   * Used to associate more restrictive types with existing definitions.
   * Each new symbol will converge with the existing one, where it is defined;
   * an will have the more restrictive semantic type.
   */
  def shrink(env: Environment, types: Map[Identifier, Term]): Environment =
    E(env.scope,
      types map { case (k,v) => k -> shrink(env.decl(k), emit(env.scope, v)) })
  
  def shrink(decl: Declaration, subdecl: List[TypeTranslation.MicroCode]) = {
    // Create a second version of the support predicate
    val inner = new Namespace
    val (head, supp) = (decl.head, decl.support)
    val shrunk_head = TypedIdentifier(new Identifier(s"${head.literal}'", head.kind, inner), head.typ)
    val shrunk_supp = TypedIdentifier(new Identifier(s"${supp.literal}'", supp.kind, inner), supp.typ)
    // Construct the intersection of original support and new contract
    val (vars, ret, assertions) = TypeTranslation.contract(decl.head.untype, subdecl)
    if (assertions.isEmpty) decl
    else {
      val args = vars map (T(_)) 
      Declaration(List(shrunk_head, shrunk_supp), List(
        ∀(args)( (T(shrunk_head.untype)(args) =:= T(head.untype)(args)) &
                 (T(shrunk_supp.untype)(args) <-> (T(supp.untype)(args) & &&(assertions))) )))
    }
  }
  
  abstract class MicroCode
  case class In(typ: Term) extends MicroCode {}
  case class Out(typ: Term) extends MicroCode {}
  case class Check(pred: Term, arity: Int) extends MicroCode {}
  
  

  object InOut extends Enumeration {
    val IN, OUT = Value
  }
  
  /**
   * (internal) Creates micro-code for processing a type spec.
   * This would include sorts for the arguments (In), the result
   * value (Out), and any contracts (Check).
   */
  def emit(scope: Scope, term: Term, dir: InOut.Value = InOut.OUT): List[MicroCode] = {
    if (term.isLeaf && (scope.sorts contains term.root)) {
      val master = T(scope.sorts getMasterOf term.root)
      val check = if (master != term) List(Check(term, 1)) else List()
      List(if (dir == InOut.IN) In(master) else Out(master)) ++ check
    }
    else if (term == T(S(""))) {
      List(Out(term))
    }
    else if (term.root == "->" && term.subtrees.length == 2) {
      if (dir == InOut.IN)
        List(In(term))
      else {
        val List(l,r) = term.subtrees
        emit(scope, l, InOut.IN) ::: emit(scope, r, InOut.OUT)
      }
    }
    else if (term.root == "x") {
      if (dir == InOut.IN) term.subtrees flatMap (emit(scope, _, dir))
      else throw new Scope.TypingException(s"tuple type '$term' not permitted here")
    }
    else if (term.root == "∩") {
      val (subemit, subassert) = term.subtrees map {
        x => (x, try Some(emit(scope, x, dir))
                 catch { case _: Scope.TypingException => None }) } partition (_._2.isDefined)
      if (subemit.isEmpty) 
        throw new Scope.TypingException(s"non of '${term.subtrees mkString "' '"}' is a type")
      //val (_, Some(x)) = subemit.head
      val x = TypePrimitives.intersection(subemit map (_._2.get))(scope)
      val arity = dir match { case InOut.IN => x count { case In(_) => true case _ => false } case InOut.OUT => 1 }
      //for (y <- subemit.tail) {
      //  println(subemit)
      //  ???   /* merge two type domains (interleave checks) */
      //}
      x ::: (subassert map (x => Check(x._1, arity)))
    }
    else throw new Scope.TypingException(s"'$term' is not a type")
  }

  def canonical(micro: List[MicroCode]): Term = {
    val args = new ArrayBuffer[(Int, Term)]
    var ret: Option[Term] = None
    def insort(it: List[MicroCode]): List[MicroCode] = it match {
      case (x@Check(a,i)) :: (y@Check(b,j)) :: xs =>
        if (i > j) y :: insort(x :: xs)
        else x :: insort(y :: xs)
      case x :: xs => x :: insort(xs)
      case Nil => Nil
    }
    for (ins <- insort(micro)) ins match {
      case In(tpe) => args += ((1, tpe))
      case Out(tpe) => ret = Some(tpe)
      case Check(pred, arity) => 
        ret match { 
          case Some(t) =>
            if (arity == 1) ret = Some(t ∩ pred)
            else throw new Scope.TypingException(s"check arity mismatch in '$micro'")
          case _ =>
            if ((args map (_._1) sum) < arity) throw new Scope.TypingException(s"check underflow in '$micro'")
            val popped = new ArrayBuffer[(Int, Term)]
            while ((popped map (_._1) sum) < arity) {
              popped.insert(0, args.last)
              args.trimEnd(1)
            }
            if ((popped map (_._1) sum) > arity) throw new Scope.TypingException(s"overlapping checks in '$micro'")
            args += ((arity, TI("∩")(TI("x")(popped.toList map (_._2)).foldLeft, pred)))
        }
    }
    if (ret.isEmpty) throw new Scope.TypingException(s"return missing: $micro")
    TI("->")((args.toList map (_._2)) :+ (ret.get)).foldRight
  }
  
  def canonical(scope: Scope, micro: List[MicroCode]): Term =
    simplify(scope, canonical(micro))
  
  def simplify(scope: Scope, tpe: Term): Term = {
    if (tpe.root == "∩") {
      val tset = (tpe.unfold.subtrees map (simplify(scope, _)) toSet)
      val (types, nontypes) = tset partition (x => x.isLeaf && scope.sorts.contains(x.root))
      val meet = if (types.isEmpty) None
        else Some(T(types map (_.root) reduce scope.sorts.meet _))
      T(tpe.root)(meet ++: (nontypes toList)).foldLeft
    }
    else T(tpe.root)(tpe.subtrees map (simplify(scope, _)))
  }

  // --------
  // DSL part
  // --------
  object TypingSugar {
    import syntax.Strip.greek
    
    def TyTV(literal: String, typ: Term) = T(TypedIdentifier(V(literal), typ))
    def $TyTV(literal: String, typ: Term) = T(TypedIdentifier($v(literal), typ))
    
    def qvars(names: List[String], typ: Term) = {
      val ns = new Namespace
      for (name <- names) yield T(TypedIdentifier( new Identifier(name, "variable", ns), typ ))
    }
    def qvars(types: List[Term]) = {
      val ns = new Namespace
      for ((typ, i) <- types.zipWithIndex)
        yield T(TypedIdentifier( new Identifier(greek(i), "variable", ns), typ ))
    }
    
    def qvars(types: List[Term], strip: PartialFunction[Int, Any]) = {
      val ns = new Namespace
      for ((typ, i) <- types.zipWithIndex)
        yield T(TypedIdentifier( new Identifier(strip(i), "variable", ns), typ ))
    }
    
    def ∀:(domain: Term, body: Term => Term) = qvars(List(domain)) match {
      case List(x) => ∀(x)(body(x))
    }
    def ∀:(domain: Term, body: (Term,Term) => Term) = qvars(List(domain, domain)) match {
      case List(x,y) => ∀(x,y)(body(x,y))
    }
    def ∀:(domain: Term, body: (Term,Term,Term) => Term) = qvars(List(domain, domain, domain)) match {
      case List(x,y,z) => ∀(x,y,z)(body(x,y,z))
    }

    def ∀:(xdomain: Term, ydomain: Term, body: (Term,Term) => Term) = qvars(List(xdomain, ydomain)) match {
      case List(x,y) => ∀(x,y)(body(x,y))
    }
  }

  // -----------
  // Z3Gate part
  // -----------
  
  def toSmt(env: List[Environment]) = {
    import semantics.smt.SmtNotFirstOrder
    
    val smt = new Z3Gate
    for (e <- env; d <- e.decl.values; s <- d.symbols)
      try smt.declare(s.untype, s.typ)
      catch { case _: SmtNotFirstOrder =>  }
      
    val assumptions = 
      for (e <- env; d <- e.decl.values; a <- d.precondition) yield a

    (smt, assumptions flatMap (x => try Some(smt.formula(x)) 
        catch { case e: SmtNotFirstOrder => println("WARN " + e.getMessage) ; None}))
  }
  
  def solveAndPrint(assumptionEnvs: List[Environment], goals: List[Term]) = {
    val (smt, assumptions) = toSmt(assumptionEnvs)
    smt solveAndPrint (assumptions, goals map smt.formula)
  }
  
  def solve(assumptionEnvs: List[Environment], goals: List[Term], verbose: Boolean=false) = {
    val (smt, assumptions) = toSmt(assumptionEnvs)
    smt solve (assumptions, goals map smt.formula, verbose)
  }
  
}


object TermTranslation {
  
  import AstSugar._
  import TypeTranslation.{TypedIdentifier,Declaration}
  import TypeTranslation.Environment
  import TypeTranslation.TypingSugar._
  
  object combine {
    
    def app(func: Declaration, arg: Declaration) = {
      val freshns = new Uid
      val result = new Identifier("@", "function", freshns)
      val support = new Identifier("|@|", "predicate", freshns)
      def behead(typ: Term) =
        if (typ.root == "->" && typ.subtrees.length == 2) typ.subtrees(1)
        else throw new Scope.TypingException(s"not a function type: '$typ'")
      val result_type = behead(func.head.typ)
      val support_type = behead(func.support.typ)
      def vartypes_(typ: Term): List[Term] = 
        if (typ.root == "->" && typ.subtrees.length == 2) typ.subtrees(0) :: vartypes_(typ.subtrees(1))
        else List()
      val vartypes = vartypes_(result_type)
      val vars = for ((t,i) <- vartypes.zipWithIndex) yield 
        T(TypedIdentifier(new Identifier(s"$$$i", "variable", freshns), t))
      Declaration(List(TypedIdentifier(result, result_type),
                       TypedIdentifier(support, support_type)),
          List(
            ∀(vars)(
                (T(result)(vars) =:= T(func.head, T(arg.head) :: vars)) &
                (T(support, vars) <->
                  (T(arg.support) &
                   T(func.support, T(arg.head) :: vars)))
            )
          ))
    }
    
    def retype(scope: Scope, value: Declaration, typ: Term) = {
      val redecl = TypeTranslation.shrink(value, TypeTranslation.emit(scope, typ))
      (redecl.head, redecl)
    }
    
    def slash(scope: Scope, fore: Declaration, back: Declaration) = {
      val ns = new Uid
      val result = new Identifier("/", "function", ns)
      val support = new Identifier("|/|", "predicate", ns)
      val (varids, _, _) = TypeTranslation.contract(result, TypeTranslation.emit(scope, fore.head.typ))
      val vars = varids map (T(_))
      Declaration(List(TypedIdentifier(result, fore.head.typ),
                       TypedIdentifier(support, fore.support.typ)),
         List(
            ∀(vars)(
                (T(fore.support)(vars) -> (T(result)(vars) =:= T(fore.head)(vars))) &
                (~T(fore.support)(vars) -> (T(result)(vars) =:= T(back.head)(vars))) &
                (T(support)(vars) <-> (T(fore.support)(vars) | T(back.support)(vars)))
            )
         ))
    }
    
    /*
    def abs(va: Declaration, decl: Declaration): Declaration = {
      val ns = new Uid
      val result = new Identifier(s"${va.head.literal}↦${decl.head.literal}", "function", ns)
      val support = new Identifier(s"|${va.head.literal}↦${decl.head.literal}|", "predicate", ns)
      def gener(phi: Term): Term =
        if (phi.root == va.head) T(result)(T(va.head))(phi.subtrees map gener)
        else if (phi.root == va.support) T(support)(T(va.head))(phi.subtrees map gener)
        else T(phi.root)(phi.subtrees map gener)
      Declaration(List(TypedIdentifier(result, va.head.typ -> decl.head.typ),
                       TypedIdentifier(support, va.head.typ -> decl.support.typ)),
          for (phi <- decl.precondition) yield ∀(T(va.head))(phi))
    }

    def abs(va: Declaration, env: Environment): Environment =
      new Environment(env.scope, env.decl map { case (k,v) => 
        (k, if (v eq va) v else abs(va, v)) })*/
    
  }
  
  def term(env: Environment, term: Term, annot: Map[Id[Term], Term] = Map()): (Identifier, Environment) = {
    val (id, termEnv) = term1(env, term, annot)
    (id, env ++ termEnv)
  }

  def term1(env: Environment, term: Term, annot: Map[Id[Term], Term] = Map()): (Identifier, Environment) = {
    (term0(env, term, annot), annot get term) match {
      case ((va, va_env), Some(typ)) => 
        val (aid, a) = combine.retype(env.scope, va_env(va), typ)
        (aid, va_env + (aid -> a))
      case (v0, _) => v0
    }
  }
  
  def term0(env: Environment, term: Term, annot: Map[Id[Term], Term]): (Identifier, Environment) = {
    val r = term.root
    val arity = term.subtrees.length
    def rechild(x: Term) = term1(env, x, annot)
    def recurse = term.subtrees map rechild
    if (term.isLeaf) env.decl get term.root match {
      case Some(decl) => (r, new Environment(env.scope, Map(r -> decl)))//env)
      case _ => throw new Exception(s"undeclared identifier '$term'")
    }
    else if (r == "@" && arity == 2) {
      val List((f, f_env), (arg, arg_env)) = recurse
      val a = combine.app(f_env(f), arg_env(arg))
      (a.head, f_env ++ arg_env + (a.head -> a))
    }
    else if (r == "::" && arity == 2) {
      val ((va, va_env), typ) = (rechild(term.subtrees(0)), term.subtrees(1))
      val (aid, a) = combine.retype(env.scope, va_env(va), typ)
      (aid, va_env + (aid -> a))
    }
    else if (r == ":" && arity == 2) {
      rechild(term.subtrees(1))
    }
    else if (r == "/" && arity == 2) {
      val List((fore, fore_env), (back, back_env)) = recurse
      val sl = combine.slash(env.scope, fore_env(fore), back_env(back))
      (sl.head, fore_env ++ back_env + (sl.head -> sl))
    }/*
    else if (r == "↦" && arity == 2) {
      val List((va, va_env), (body, body_env)) = recurse
      val abs = combine.abs(va_env(va), body_env)
      (abs.head, abs)
    }*/
    else throw new Exception(s"Cannot translate term '${term.toPretty}'")
  }
  
  /**
   * Eventually all of the term translation mechanism will go through this.
   */
  class TermBreak(val env: Environment) {
    
    import Prelude.B
    
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
    
    import semantics.TypedLambdaCalculus.typecheck0
    
    def generalize(eqs: List[Term], arg: Term): (Map[Identifier,Identifier], List[Term]) = {
      /**/ assume(eqs forall (_ =~ ("=", 2))) /**/
      /**/ assume(eqs forall (_.subtrees(0).isLeaf)) /**/
      val sym = eqs map (_.subtrees(0).root)
      val gensym = sym map (x => (x, TypedIdentifier(x, rawtype(env.typeOf_!(arg) -> env.typeOf_!(x))))) toMap
      val subst = new TreeSubstitution(sym map (x => (T(x), T(gensym(x)) :@ arg))) {
        override def preserve(old: Term, new_ : Term) = TypedTerm.preserve(old, new_)
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
        TypedTerm.preserve(term, term.subtrees(1).subtrees(0))
      else
        term
    
  }  
  
  def proveAndPrint(env: List[Environment], goals: List[Term]) {
    val (smt, assumptions) = TypeTranslation.toSmt(env)
    
    for ((k,v) <- smt.declarations) println(s"$k -> $v    // :: ${smt.typeOf(v).toPretty}")
    println("-" * 80)
    
    smt solveAndPrint (assumptions, goals map smt.formula)
  }
  
  
  def main(args: Array[String]): Unit = {

    import examples.Paren._
    import com.microsoft.z3.Expr
    
    val B = T(S(""))

    def f = TI("f")

    import Prelude._
    import syntax.Scheme._
          
    val prelude = TypeTranslation.subsorts(scope) ++
      TypeTranslation.decl(scope, Map(< ~> ((J x J) -> B))) where
      (transitive(J)(<), antisymm(J)(<),
            compl(J)(J0, J1), allToAll(J)(J0, <, J1))
      
    
    val env = prelude ++ TypeTranslation.decl(scope, 
        Map(f ~> (((J x J) ∩ TV("<")) -> R),
            i ~> J, j ~> J) )
    
    for ((k,v) <- env.decl) println(s"$k -> ${v.toPretty}")
    
    val ff = f
    val annot = Map(new Id(ff) -> (J ->: J0 ->: R))
    val (fij, fij_env) = term(env, ff:@(i, j), annot)
    
    val alt_env = (TypeTranslation.shrink(env, Map(i ~> J0, j ~> J0)))

    for ((k,v) <- alt_env.decl) println(s"$k -> ${v.toPretty}")
    println("-" * 80)

    val (alt_fij, alt_fij_env) = term(env ++ alt_env, f:@(i, j))

    // Put it to the test... with SMT!
    proveAndPrint(List(fij_env, alt_fij_env),
        List(T(fij_env(fij).support) <-> T(alt_fij_env(alt_fij).support)))
  }
  
}
