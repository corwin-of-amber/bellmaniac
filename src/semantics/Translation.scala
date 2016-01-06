package semantics

import com.microsoft.z3.BoolExpr
import syntax.{Tree,Identifier,AstSugar,Scheme}
import syntax.transform.TreeSubstitution
import scala.collection.mutable.ArrayBuffer
import semantics.smt.{CVC4Gate, Z3Gate}



object TypeTranslation {
  
  import AstSugar._
  
  case class Declaration(val symbols: List[TypedIdentifier],
                         val precondition: List[Term]=List.empty,
                         val origin: Map[Identifier, Term]=Map.empty) {
    def this(symbols: Term*) =
      this(symbols map (x => TypedIdentifier(x.leaf, TypedTerm.typeOf_!(x))) toList, List())
      
    def head = symbols.head
    def support = symbols.tail find (_.kind == "predicate") getOrElse 
      { throw new Scope.TypingException(s"no support found for '$head'") }
    
    def where(facts: Term*): Declaration = where(facts toList)
    def where(facts: List[Term]) = Declaration(symbols, precondition ++ facts)
    
    def of(origin: Map[Identifier, Term]) = Declaration(symbols, precondition, origin)

    def shallow = Declaration(symbols)
    
    def toPretty = s"Declaration(${symbols map (_.toPretty) mkString ", "}; " +
                   s"${precondition map (_.untype.toPretty) mkString ", "})"
  }
  
  class Environment(val scope: Scope, val decl: Map[Identifier, Declaration]) {
    def ++(that: Environment) =
      if (scope eq that.scope) E(scope, decl ++ that.decl)
      else throw new Exception("incompatible scopes for environment merge")
    
    def ++(that: Map[_ <: Identifier, Declaration]) =  E(scope, decl ++ that)
    def +(that: (_ <: Identifier, Declaration)) =      E(scope, decl + that)
    def +(that: Declaration) =                         E(scope, decl + ($_ -> that))

    def apply(symbol: Identifier) : Declaration = decl get symbol getOrElse {
        for ((_,v) <- decl; s <- v.symbols) if (s == symbol) return v
        throw new NoSuchElementException(s"symbol $symbol")
      }
    
    def typedecl = decl.values flatMap (_.origin) toMap
    
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
    val empty = new Environment(new Scope, Map())
  }
  
  private def E(scope: Scope, decl: Map[Identifier, Declaration]=Map()) =
    new Environment(scope, decl)
  
  def decl(scope: Scope, types: Map[Identifier, Term]): Environment =
    E(scope, types map { case (k,v) => k -> decl(scope, k, v) })
  
  def decl(scope: Scope, symbol: Identifier, typ: Term): Declaration =
    decl(symbol, emit(scope, typ)) of Map(symbol -> typ)
  
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
  
  /**
   * Generates input precondition
   * @param nargs: generates contract for the first nargs arguments
   */
  def contract(micro: List[MicroCode], nargs: Int) = {
    val inner = new Namespace
    val vars = new ArrayBuffer[TypedIdentifier]
    var ret: Boolean = false
    def freshvar = new Identifier(s"$$${vars.length}", "variable", inner)
    val assertions = new ArrayBuffer[Term]
    micro foreach {
      case In(t) => vars += (TypedIdentifier(freshvar,t))
      case Out(t) => ret = true
      case Check(pred, arity) =>
        if (!ret) {
          if (vars.length <= nargs) {
            val args = (vars takeRight arity map (T(_)) toList)
            assertions += pred(args:_*)
          }
          else {
            if (arity > vars.length - nargs)
              throw new NotImplementedError(s"dependent types: $micro, (as $nargs-ary)")
          }
        }
    }
    (vars.toList, assertions.toList)
  }

  /**
   * Generates input and output conditions
   */
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
  
  def checks(micro: List[MicroCode], args: List[Term]) = {
    val (vars, assertions) = contract(micro, args.length)
    for (assertion <- assertions)
      yield new Scheme.Template(vars, assertion)(args)
  }
  
  def checks(symbol: Identifier, micro: List[MicroCode], args: List[Term]) = {
    val (vars, ret, assertions) = contract(symbol, micro)
    for (assertion <- assertions)
      yield new Scheme.Template(vars, assertion)(args)
  }
  
  def checks(scope: Scope, symbol: TypedIdentifier, args: List[Term]): List[Term] = 
    checks(symbol.untype, emit(scope, symbol.typ), args)
  
  def checks(scope: Scope, typ: Term, args: List[Term]): List[Term] = 
    checks(emit(scope, typ), args)
  
  def subsorts(scope: Scope) = E(scope, {
    import TypingSugar._
    import Domains.⊥
    def pred(dom: Identifier) = T(dom) -> TS("")
    def top(master: Identifier, subsort: Identifier) = ∀:(T(master), x => T(subsort)(x))
    def bot(master: Identifier, subsort: Identifier) = ∀:(T(master), x => ~T(subsort)(x))
    for (master <- scope.sorts.mastersHie; slave <- master.nodes if slave.root != ⊥)
      yield slave.root -> Declaration(List(TypedIdentifier(slave.root, pred(master.root))), 
          if      (slave eq master)    List(top(master.root, slave.root))
          else if (slave.root.ns eq ⊥) List(bot(master.root, slave.root))
          else List())
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
    else if (term.root == "×") {
      if (dir == InOut.IN) term.subtrees flatMap (emit(scope, _, dir))
      else throw new Scope.TypingException(s"tuple type '$term' not permitted here")
    }
    else if (term.root == "∩") {
      val (subemit, subassert) = term.subtrees map {
        x => (x, try Some(emit(scope, x, dir))
                 catch { case _: Scope.TypingException => None }) } partition (_._2.isDefined)
      if (subemit.isEmpty) 
        try emit(scope, term.subtrees.head, dir)
        catch { case e: TraceableException => throw e at term }
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
    /* Sort consequent checks by arity (quadratic :/) */
    def insort_ins(x: MicroCode, xs: List[MicroCode]): List[MicroCode] = (x, xs) match {
      case (Check(a,i), (y@Check(b,j)) :: ys) =>
        if (i <= j) x :: xs else y :: insort_ins(x, ys)
      case _ => x :: xs
    }
    def insort(it: List[MicroCode]): List[MicroCode] = it match {
      case x :: xs => insort_ins(x, insort(xs))
      case Nil => Nil
    }
    /* Scan left-to-right and intersect checks */
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
            args += ((arity, TI("∩")(TI("×")(popped.toList map (_._2))<<, pred)))
        }
    }
    if (ret.isEmpty) throw new Scope.TypingException(s"return missing: $micro")
    TI("->")((args.toList map (_._2)) :+ (ret.get)).foldRight
  }
  
  def canonical(scope: Scope, micro: List[MicroCode]): Term =
    simplify(scope, canonical(micro))
  
  def simplify(scope: Scope, tpe: Term): Term = {
    if (tpe.root == "∩") {
      val tset = tpe.unfold.subtrees map (simplify(scope, _)) toSet
      val (types, nontypes) = tset partition (x => x.isLeaf && scope.sorts.contains(x.root))
      val meet = if (types.isEmpty) None
        else Some(T(types map (_.root) reduce scope.sorts.meet))
      T(tpe.root)(meet ++: nontypes.toList).foldLeft
    }
    else T(tpe.root)(tpe.subtrees map (simplify(scope, _)))
  }

  // --------
  // DSL part
  // --------
  object TypingSugar {
    import syntax.Strip.greek
    
    def TyTV(literal: Any, typ: Term) = T(TypedIdentifier(V(literal), typ))
    def $TyTV(literal: Any, typ: Term) = T(TypedIdentifier($v(literal), typ))
    def TyTI(literal: Any, kind: String, typ: Term) = T(TypedIdentifier(I(literal, kind), typ))
    def $TyTI(literal: Any, kind: String, typ: Term) = T(TypedIdentifier($I(literal, kind), typ))

    def qvars(names: List[String], typ: Term) = {
      val ns = new Namespace
      for (name <- names) yield T(TypedIdentifier( new Identifier(name, "variable", ns), typ ))
    }
    def qvars(types: List[Term], strip: PartialFunction[Int, Any]=greek) = {
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

    def ∀:(domain: Term, body: (Term,Term,Term,Term) => Term) = qvars(List(domain, domain, domain, domain)) match {
      case List(x,y,z,w) => ∀(x,y,z,w)(body(x,y,z,w))
    }

    def ∀:(xdomain: Term, ydomain: Term, body: (Term,Term) => Term) = qvars(List(xdomain, ydomain)) match {
      case List(x,y) => ∀(x,y)(body(x,y))
    }
  }

  // -----------
  // Z3Gate part
  // -----------

  def toSmt(env: List[Environment]): (Z3Gate, List[BoolExpr]) = toSmt(new Z3Gate, env)

  def toSmt(smt: Z3Gate, env: List[Environment]) = {
    import semantics.smt.SmtNotFirstOrder
    
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
  import TypeTranslation.Declaration
  import TypeTranslation.Environment
  import TypeTranslation.TypingSugar._

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
          case Some(typ) => (pushTypeDown(term), List())
          case _ => throw new Scope.TypingException(s"undeclared: '$term'")
        }
      }
      else if (term =~ ("@", 2)) {
        val func :: args = term.unfoldLeft.subtrees
        val (func_id, func_terms) = reapply(func)
        val (arg_ids, arg_terms) = args map reapply unzip
        //val List((func_id, func_terms), (arg_id, arg_terms)) = term.subtrees map reapply
        import TypePrimitives.curry
        val func_ret = (rawtype(env.typeOf_!(func_id)) /: arg_ids)((t, _) => curry(t)(env.scope)._2)
        //val (func_par, func_ret) = TypePrimitives.curry(rawtype(env.typeOf_!(func_id)))(env.scope)
        val app = TypedTerm(T(TypedIdentifier($v(s"${func_id.untype}${arg_ids map (_.untype) mkString}"), func_ret)), func_ret)
        (app, func_terms ++ arg_terms.flatten :+ (app =:= TypedTerm(func_id :@ arg_ids, func_ret)))
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
        val (genbody_syms, genbody_t) = generalize(body_t :+ (fun =:= body_id), arg, fun)
        (T(genbody_syms(fun.root)), genbody_t) // TODO
      }
      else if (term =~ ("|!", 2)) {
        val List(expr, cond) = term.subtrees
        val (expr_id, expr_terms) = this(expr)
        val guard = T(TypedIdentifier($v(s"${expr_id.untype}`"), rawtype(env.typeOf_!(expr_id))))
        assert(expr_id.isLeaf)
        (guard, expr_terms :+ (guard =:= TypedTerm(expr_id |! unguard(cond), env.typeOf_!(expr_id))))
      }
      else if (term =~ (":", 2)) {
        term0(term.subtrees(1))
      }
      else throw new Scope.TypingException(s"don't quite know what to do with ${term toPretty}")
    }

    // @@@ this code repeats in synth.proof.Assistant
    def unguard(cond: Term): Term = {
      implicit val scope = env.scope
      val inner = cond.nodes filter (_ =~ ("|!", 2)) toList
      def hoist = &&(inner map (_.subtrees(1)))
      if (inner.isEmpty) cond
      else
        TypedTerm.replaceDescendants(cond, inner map (n => (n, n.subtrees(0)))) & hoist
    }

    import semantics.TypedLambdaCalculus.typecheck0
    
    def generalize(eqs: List[Term], arg: Term, target: Term): (Map[Identifier,Identifier], List[Term]) = {
      /**/ assume(eqs forall (_ =~ ("=", 2))) /**/
      /**/ assume(eqs forall (_.subtrees(0).isLeaf)) /**/
      //val sym = eqs map (_.subtrees(0).root)
      val sym = (reach1(Set(arg.root), dependencies(eqs)) + target.root) toList
      val gensym = sym map (x => (x, TypedIdentifier(x, rawtype(env.typeOf_!(arg) -> env.typeOf_!(x))))) toMap
      val subst = new TreeSubstitution(sym map (x => (T(x), T(gensym(x)) :@ arg))) {
        override def preserve(old: Term, new_ : Term) = TypedTerm.preserve(old, new_)
      }
      val geneqs =
      for (eq <- eqs) yield gensym get eq.subtrees(0).root match { case None => eq case Some(l) =>
        //println(eq toPretty)
        val lhs = T(l)
        val rhs = eta(typecheck0(arg ↦ subst(eq.subtrees(1))))
        //println(s"   ${lhs } = ${rhs }")
        lhs =:= rhs
      }
      intermediates --= gensym.keys
      intermediates ++= gensym.values
      (gensym, geneqs)
    }
    
    def dependencies(eqs: List[Term]) = {
      def syms(rhs: Term) = rhs.leaves map (_.root) /*filter syma.contains*/ toList
      val cab = eqs map (eq => (eq.subtrees(0).root, syms(eq.subtrees(1))))
      ( for ((l,rs) <- cab; r <- rs) yield (r,l) ) groupBy (_._1) mapValues (_.map (_._2))
    }
    
    def reach1[X](origins: Set[X], adj: Map[X, List[X]]) =
      (Stream.iterate(origins)(_ flatMap (adj.getOrElse(_, List()))) drop 1 takeWhile (_.nonEmpty)).flatten toSet
    
    def eta(term: Term) =
      if (term =~ ("↦", 2) && term.subtrees(1) =~ ("@", 2) && term.subtrees(1).subtrees(1) == term.subtrees(0))
        TypedTerm.preserve(term, term.subtrees(1).subtrees(0))
      else
        term

    def pushTypeDown(term: Term) =
      if (term.isLeaf)
        (env.typeOf(term), env.typeOf(term.root)) match {
          case (Some(typ), None) =>
            TypedTerm(T(TypedIdentifier(term.root, typ)), typ)
          case _ => term
        }
      else term

  }  
  
  /*
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
  }*/
  
}


class FormulaTranslation(val termb: TermTranslation.TermBreak) {
  
  import AstSugar._
  import Prelude.B
  import TypeTranslation.TypingSugar._

  private def accum[A,B](l: List[(A, List[B])]) =
    l.unzip match { case (x, y) => (x, y.flatten) }
  
  def apply(phi: Term): (Term, List[Term]) = phi match {
    case typed: TypedTerm if typed.typ == B =>
      if (phi.root == "@") {
        val (components, sub) = accum(phi.unfoldLeft.subtrees map apply)
        (TypedTerm(components.head :@ (components.tail:_*), B), sub)
      }
      else if (phi =~ ("∀", 2)) {
        val forall = $TyTV("A", B)
        val arg = phi.subtrees(0)
        val (body, body_t) = apply(phi.subtrees(1))
        val (genbody_syms, genbody_t) = termb.generalize(body_t :+ (forall =:= body), arg, forall)
        // genbody_t.last is   A = arg ↦ body
        //  and we want        ∀arg (body)
        /**/ assert (genbody_t.last =~ ("=", 2) && genbody_t.last.subtrees(0) =~ (genbody_syms(forall.root), 0) && genbody_t.last.subtrees(1) =~ ("↦", 2)) /**/
        (TypedTerm(T(phi.root)(genbody_t.last.subtrees(1).subtrees), B), genbody_t dropRight 1)
      }
      else {
        val (components, sub) = accum(phi.subtrees map apply)
        (TypedTerm(T(phi.root)(components), B), sub)
      }
    case _ => termb(phi)
  }
    
}



class TraceableException(msg: String) extends Exception(msg) {

  import syntax.AstSugar._

  var where: List[Term] = List.empty

  def at(term: Term): TraceableException = {
    this.where = this.where :+ term
    this
  }

  override def getMessage = (super.getMessage /: this.where)((msg,term) => s"${msg}\n\tin: ${term toPretty}")
}

object TraceableException {
  import syntax.AstSugar._
  def trace[A](term: Term)(op: => A) =
    try op
    catch { case e: TraceableException => throw e at term}
}


class TranslationError(msg: String) extends TraceableException(msg)

