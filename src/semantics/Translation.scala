package semantics

import syntax.{Tree,Identifier,AstSugar}
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
  
  implicit class UntypedTerm(private val term: Term) extends AnyVal {
    def untype = term.map({
      case x: TypedIdentifier => x.untype
      case e => e
    })
  }
  
  case class TypedTerm(term: Term, val typ: Term)
    extends Term(term.root, term.subtrees) {
    override def toString = s"${super.toString} :: $typ"
    def untype = term.untype
  }
  
  case class Declaration(val symbols: List[TypedIdentifier], 
                         val precondition: List[Term]) {
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
    
    def apply(symbol: Identifier) = decl(symbol)
    
    def where(facts: Term*) = this + ($_ -> Declaration(List(), facts.toList))
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
      val (_, Some(x)) = subemit.head
      val arity = dir match { case InOut.IN => x count { case In(_) => true case _ => false } case InOut.OUT => 1 }
      for (y <- subemit.tail) 
        ???   /* merge two type domains (interleave checks) */
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
    TI("->")((args.toList map (_._2)) :+ (ret.get)).foldRight
  }
  
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
    def qvars(names: List[String], typ: Term) = {
      val ns = new Namespace
      for (name <- names) yield T(TypedIdentifier( new Identifier(name, "variable", ns), typ ))
    }
    
    def ∀:(domain: Term, body: Term => Term) = qvars(List("x"), domain) match {
      case List(x) => ∀(x)(body(x))
    }
    def ∀:(domain: Term, body: (Term,Term) => Term) = qvars(List("x", "y"), domain) match {
      case List(x,y) => ∀(x,y)(body(x,y))
    }
    def ∀:(domain: Term, body: (Term,Term,Term) => Term) = qvars(List("x", "y", "z"), domain) match {
      case List(x,y,z) => ∀(x,y,z)(body(x,y,z))
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
      val freshns = new Namespace
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
                TI("=")(T(result)(vars), T(func.head, T(arg.head) :: vars)) &
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
    
  }
  
  def term(env: Environment, term: Term, annot: Map[Id[Term], Term] = Map()): (Identifier, Environment) = {
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
    def rechild(x: Term) = TermTranslation.term(env, x, annot)
    def recurse = term.subtrees map rechild
    if (term.isLeaf) env.decl get term.root match {
      case Some(decl) => (r, env)
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
    else throw new Exception(s"Cannot translate term '${term.toPretty}'")
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
