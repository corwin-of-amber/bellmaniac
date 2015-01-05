package semantics

import syntax.{Tree,Identifier,AstSugar}
import scala.collection.mutable.ArrayBuffer



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
    
    def toPretty = s"Declaration(${symbols map (_.toPretty) mkString ", "}; " +
                   s"${precondition map (_.untype.toPretty) mkString ", "})"
  }
  
  
  def decl(scope: Scope, symbol: Identifier, typ: Term): Declaration =
    decl(symbol, emit(scope, typ))
  
  def decl(symbol: Identifier, micro: List[MicroCode]) = {
    val inner = new Namespace
    val supp = new Identifier(s"|$symbol|", "predicate", inner)
    val vars = new ArrayBuffer[TypedIdentifier]
    var ret: TypedTerm = null
    def freshvar = new Identifier(s"$$${vars.length}", "variable", inner)
    val assertions = new ArrayBuffer[Term]
    micro foreach {
      case In(t) => vars += (TypedIdentifier(freshvar,t))
      case Out(t) => ret = TypedTerm(T(symbol, (vars map (T(_))).toList), t)
      case Check(pred, arity) =>
        val args = (vars takeRight arity map (T(_))).toList
        assertions += pred(args:_*)
    }
    // symbol :: vars -> ret
    val symbol_type = TI("->", (vars map (_.typ)).toList :+ ret.typ).foldRight
    // |symbol| :: vars -> (bool)
    val supp_type = TI("->", (vars map (_.typ)).toList :+ TI("")).foldRight
    // forall vars. supp(vars) -> assertions
    val lvars = (vars map (T(_))).toList
    val precondition =
      if (assertions.isEmpty) None
      //else if (vars.isEmpty) Some(TI("&", assertions.toList).foldLeft)
      else Some(
        TI("∀", lvars :+
            TI("->")(
                T(supp, lvars),
                TI("&", assertions.toList).foldLeft
                )).foldRight)
    new Declaration(List(TypedIdentifier(symbol, symbol_type),
                         TypedIdentifier(supp, supp_type)),
        precondition.toList)
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
      List(if (dir == InOut.IN) In(master) else Out(master))
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
  
}


object TermTranslation {
  
  import AstSugar._
  import TypeTranslation.{TypedIdentifier,Declaration}
  
  
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
            TI("forall", vars)(
              TI("<->")(
                T(support, vars),
                TI("&")(
                  T(arg.support),
                  T(func.support, T(arg.head) :: vars)
                )
              )
            )
          ))
    }
    
  }
  
  
  def main(args: Array[String]): Unit = {
    val scope = new Scope()
    scope.declareSort(S("J"))
    scope.declareSort(S("I"))
    scope.declareSort(S("R"))
    
    val J = T(S("J"))
    val R = T(S("R"))
    
    val JJltR = TI("->")(TI("∩")(TI("x")( T(S("I")), J), TV("<")), R)
    val f = TypeTranslation.decl(scope, I("f"), JJltR) // TI("->")(T(S("J")), TI("->")(T(S("J")), T(S("R"))) ))
    val i = TypeTranslation.decl(scope, I("i"), T(S("J")))
    
    println(s"f :: ${f.toPretty}")
    println(s"i :: ${i.toPretty}")
    
    val fi = combine.app(f, i)
    
    println(s"f i :: ${fi.toPretty}")
  }
  
}
