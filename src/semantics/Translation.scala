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
  
  type Environment = Map[Identifier, Declaration]
  
  
  def decl(scope: Scope, types: Map[Identifier, Term]): Environment =
    types map { case (k,v) => k -> decl(scope, k, v) }
  
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
  
  def subsorts(scope: Scope) = {
    import TypingSugar._
    val masterTypes = scope.sorts.subtrees
    def pred(dom: Identifier) = TI("->")(T(dom), T(S("")))
    for (master <- masterTypes; slave <- master.nodes if slave.root != Domains.⊥)
      yield slave.root -> Declaration(List(TypedIdentifier(slave.root, pred(master.root))), 
          if (slave eq master) List(∀:(T(master.root), x => T(master.root)(x))) else List()) 
  }.toMap
  
  /**
   * Used to associate more restrictive types with an existing definitions.
   * Each new symbol will converge with the existing one, where it is defined;
   * an will have the more restrictive semantic type.
   */
  def shrink(scope: Scope, env: Environment, types: Map[Identifier, Term]): Environment =
    types map { case (k,v) => k -> shrink(env(k), emit(scope, v)) }
  
  def shrink(decl: Declaration, subdecl: List[TypeTranslation.MicroCode]) = {
    // Create a second version of the support predicate
    val inner = new Namespace
    val supp = decl.support
    val shrunk = TypedIdentifier(new Identifier(s"${supp.literal}'", supp.kind, inner), supp.typ)
    // Construct the intersection of original support and new contract
    val (vars, ret, assertions) = TypeTranslation.contract(decl.head.untype, subdecl)
    if (assertions.isEmpty) decl
    else {
      val args = vars map (T(_)) 
      Declaration(List(decl.head, shrunk), List(
        ∀(args)(T(shrunk.untype)(args) <-> (T(supp.untype)(args) & &&(assertions)))))
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
    if (term.isLeaf && scope.containsSort(term.root)) {
      val master = T(scope getDomainOf term.root)
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
      if (dir == InOut.IN) {
        val (subemit, subassert) = term.subtrees map {
          x => (x, try Some(emit(scope, x, dir))
                   catch { case _: Scope.TypingException => None }) } partition (_._2.isDefined)
        if (subemit.isEmpty) throw new Scope.TypingException(s"non of '${term.subtrees mkString "' '"}' is a type")
        else {
          val (_, Some(x)) = subemit.head
          val arity = x count { case In(_) => true case _ => false }
          for (y <- subemit.tail) ???   /* merge two type domains (interleave checks) */
          x ::: (subassert map (x => Check(x._1, arity)))
        }
      }
      else ???  /* intersection as return type */
    }
    else throw new Scope.TypingException(s"'$term' is not a type")
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
    
  }
  
  def term(env: Environment, term: Term): (Identifier, Environment) = {
    val r = term.root
    val arity = term.subtrees.length
    def recurse = term.subtrees map (TermTranslation.term(env, _))
    if (term.isLeaf) env get term.root match {
      case Some(decl) => (r, env)
      case _ => throw new Exception(s"undeclared identifier '$term'")
    }
    else if (r == "@" && arity == 2) {
      val List((f, f_env), (arg, arg_env)) = recurse
      val a = combine.app(f_env(f), arg_env(arg))
      (a.head, Map(a.head -> a) ++ f_env ++ arg_env)
    }
    else throw new Exception(s"Cannot translate term '${term.toPretty}'")
  }
  
  
  def main(args: Array[String]): Unit = {

    import examples.Paren.{scope,R,J,J0,J1}
    import com.microsoft.z3.Expr
    
    val B = T(S(""))

    val lt = TI("<")
    val f = TI("f")
    val i = TI("i")
    val j = TI("j")
    
    def transitive(r: Term, elType: Term) = 
      ∀:(elType, (x,y,z) => (r(x,y) ->: r(y,z) ->: r(x,z)))
    
    import syntax.Scheme
    import syntax.Scheme._
      
    def antirefl(r: Scheme, elType: Term) = ∀:(elType, x => ~r(x,x))
    def antisymm(r: Scheme, elType: Term) = ∀:(elType, (x,y) => r(x,y) -> ~r(y,x))
    def compl(P: Scheme, nP: Scheme, elType: Term) = ∀:(elType, x => nP(x) <-> ~P(x))
    def allToAll(P: Scheme, r: Scheme, Q: Scheme, elType: Term) = ∀:(elType, (x,y) => P(x) ->: Q(y) ->: r(x,y))
    
    def where(facts: Term*) = $_ -> Declaration(List(), facts.toList)
    
    val prelude = TypeTranslation.subsorts(scope) ++
      TypeTranslation.decl(scope, Map(lt ~> ((J x J) -> B))) +
      where(transitive(lt, J), antisymm(lt, J),
            compl(J0, J1, J), allToAll(J0, lt, J1, J))
      
    
    val env = prelude ++ TypeTranslation.decl(scope, 
        Map(f ~> (((J x J) ∩ TV("<")) -> R),
            i ~> J, j ~> J0) )
    
    for ((k,v) <- env) println(s"$k -> ${v.toPretty}")
    
    val (fij, fij_env) = term(env, :@(f, i, j).foldLeft)
    
    val alt_env = (TypeTranslation.shrink(scope, env, Map(i ~> J0)))

    for ((k,v) <- alt_env) println(s"$k -> ${v.toPretty}")
    println("-" * 80)

    val (alt_fij, alt_fij_env) = term(env ++ alt_env, :@(f, i, j).foldLeft)

    val declared_symbols = fij_env.values.toList ++ alt_fij_env.values.toList
    
    // Put it to the test... with SMT!
    val smt = new Z3Gate
    for (d <- declared_symbols; s <- d.symbols)
      smt.declare(s.untype, s.typ)
      
    import semantics.smt.Z3Sugar._
      
    val assumptions = 
      for (d <- declared_symbols; a <- d.precondition) yield a |> smt.formula

    for ((k,v) <- smt.declarations) println(s"$k -> $v    // :: ${smt.typeOf(v).toPretty}")
    
    val goal = T(fij_env(fij).support) <-> T(alt_fij_env(alt_fij).support) |> smt.formula
      
    solveAndPrint(assumptions, List(goal))
  }
  
}
