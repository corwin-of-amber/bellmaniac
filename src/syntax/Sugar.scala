
package syntax


object AstSugar {

  type Term = Tree[Identifier]
  
  def I(a: Any) = new Identifier(a)
  def S(a: Any) = new Identifier(a, "set")
  def V(a: Any) = new Identifier(a, "variable")
  def T(a: Identifier, b: List[Tree[Identifier]]=List()) = new Tree(a, b)
  def TI(a: Any, b: List[Tree[Identifier]]=List()) = T(I(a), b)
  def TS(a: Any, b: List[Tree[Identifier]]=List()) = T(S(a), b)
  def TV(a: Any, b: List[Tree[Identifier]]=List()) = T(V(a), b)

  def symbols[T](t: Tree[T]) = (t.nodes map (_.root) toSet)
  
  implicit class TreeBuild[A](private val t: Tree[A]) extends AnyVal {
    def apply(subtrees: Tree[A]*) = new Tree(t.root, t.subtrees ++ subtrees)
    def apply(subtrees: List[Tree[A]]) = new Tree(t.root, t.subtrees ++ subtrees)
  }
  
  implicit class FormulaDisplay(private val term: Term) extends AnyVal {
    def toPretty: String = Formula.display(term)
  }
  
  // --------
  // DSL Part
  // --------
  
  val @: = TI("@")
  
  def ∀(vars: Term*)(body: Term): Term = ∀(vars.toList)(body)
  def ∀(vars: List[Term])(body: Term) = TI("∀")(vars)(body).foldRight

  implicit class DSL(private val term: Term) extends AnyVal {
    def ::(that: Term) = TI("::")(that, term)
    def -:(that: Term) = TI(":")(term, that)
    def :-(that: Term) = TI(":")(term, that)
    def |:(that: Term) = TI("|_")(that, term)
    def |!(that: Term) = TI("|!")(term, that)
    def /:(that: Term) = TI("/")(that, term)
    def ->(that: Term) = TI("->")(term, that)
    def ->:(that: Term) = TI("->")(that, term)
    def ↦(that: Term) = TI("↦")(term, that)
    def &(that: Term) = TI("&")(term, that)
    def |(that: Term) = TI("|")(term, that)
    def <->(that: Term) = TI("<->")(term, that)
    def unary_~ = TI("~")(term)
    def x(that: Term) = TI("x")(term, that)
    def ∩(that: Term) = TI("∩")(term, that)
    def +(that: Term) = @:(@:(TI("+"), term), that)
    def =:=(that: Term) = TI("=")(term, that)
    
    def :@(that: Term*) = @:(term)(that:_*).foldLeft
    
    def ~>[A](that: A) = if (term.isLeaf) term.root -> that
      else throw new Exception(s"mapping from non-leaf '$term'")
    
    def =~(root: Any, arity: Int) =
      term.root == root && term.subtrees.length == arity
      
    def ?(symbol: Any) =
      term.nodes find (_ =~ (symbol, 0)) getOrElse
      { throw new Exception(s"symbol '$symbol' not found in '$term'") }
      
    def :/(label: Any) =
      term.nodes find (t => t =~ (":", 2) && t.subtrees(0).root == label) getOrElse
      { throw new Exception(s"label '$label' not found in '$term'") }
    
    def :/(label: Any, subst: Term): Term =
      term.replaceDescendant((term :/ label).subtrees(1) → subst)
      
     def \(whatWith: (Term, Term)): Term =
       new syntax.transform.TreeSubstitution(List(whatWith))(term)
       
     def << : Term =
       if (term.subtrees.length == 1 && term.subtrees(0) == `...`) term
       else term.foldLeft
  }
  
  def &&(conjuncts: Term*): Term = &&(conjuncts.toList)
  def &&(conjuncts: List[Term]) = TI("&")(conjuncts)<<

  def /::(conjuncts: Term*): Term = /::(conjuncts.toList)
  def /::(conjuncts: List[Term]) = TI("/")(conjuncts)<<
  
  val `...` = TI("...")

  class Uid {}
  def $_ = new Identifier("_", "placeholder", new Uid)
  def $v = new Identifier("?", "variable", new Uid)
  def $v(name: String) = new Identifier(name, "variable", new Uid)
 
  def $TV = T($v)
  def $TV(name: String) = T($v(name))
}


object Formula {
  
  import AstSugar.{Term,DSL}
  
  object Assoc extends Enumeration {
    type Assoc = Value
    val Left, Right, None = Value
  }
  import Assoc.Assoc
  
  class InfixOperator(val literal: String, val priority: Int, val assoc: Assoc=Assoc.None) {
    def format(term: AstSugar.Term) = {
      /**/ assume(term.subtrees.length == 2) /**/
      val op = if (literal == null) display(term.root) else literal
      s"${display(term.subtrees(0), priority, Assoc.Left)} $op ${display(term.subtrees(1), priority, Assoc.Right)}"
    }
  }
  
  class AppOperator(literal: String, priority: Int, assoc: Assoc=Assoc.None) extends InfixOperator(literal, priority, assoc) {
    override def format(term: AstSugar.Term) = {
      /**/ assume(term.subtrees.length == 2) /**/
      val List(fun, arg) = term.subtrees
      if (fun =~ ("+", 0))
        s"${display(arg, if (isOp(arg, "+")) priority else 0, Assoc.Left)} +"
      else {
        val lst = splitOp(term, "cons")
        if (lst.length > 1 && lst.last =~ ("nil", 0))
          s"⟨${lst dropRight 1 map display mkString ", "}⟩"
        else
          s"${display(fun, priority, Assoc.Left)} ${display(arg, priority, Assoc.Right)}"
      }
    }
    
    def isOp(term: Term, op: String) = (term =~ ("@", 2)) && (term.subtrees(0) =~ ("@", 2)) && (term.subtrees(0).subtrees(0) =~ (op, 0))
    
    def splitOp(term: Term, op: String): List[Term] =
      if (isOp(term, op)) 
        splitOp(term.subtrees(0).subtrees(1), op) ++ splitOp(term.subtrees(1), op)
      else List(term)
  }
  
  def O(literal: String, priority: Int, assoc: Assoc=Assoc.None) = 
    new InfixOperator(literal, priority, assoc)
  
  def M(ops: InfixOperator*) = ops map (x => (x.literal, x)) toMap
  
  val INFIX = M(O("->", 1, Assoc.Right), O("<->", 1), O("&", 1), O("|", 1), O("<", 1), O("=", 1), O("↦", 1, Assoc.Right),
      O(":", 1), O("::", 1), O("/", 1), O("|_", 1), O("|!", 1), O("∩", 1), O("x", 1)) ++ 
      Map("@" -> new AppOperator("", 1, Assoc.Left))
  val QUANTIFIERS = Set("forall", "∀", "exists", "∃")
  
  def display(symbol: Identifier): String = 
    symbol.literal.toString
  
  def display(term: AstSugar.Term): String =
    if (QUANTIFIERS contains term.root.toString)
      displayQuantifier(term.unfold)
    else
    (if (term.subtrees.length == 2) Formula.INFIX get term.root.toString else None)
    match {
      case Some(op) => 
        op.format(term)
      case None => 
        if (term.isLeaf) term.root.toString
        else s"${term.root}(${term.subtrees map display mkString ", "})"
    }
  
  def display(term: AstSugar.Term, pri: Int, side: Assoc): String = {
    if (term.subtrees.length != 2) display(term)
    else {
      val d = display(term)
      INFIX get term.root.toString match {
        case Some(op) =>
          if (op.priority < pri || op.priority == pri && side == op.assoc) d else s"($d)"
        case _ => d
      }
    }
  }

  def displayQuantifier(term: AstSugar.Term) =
    s"${term.root}${term.subtrees dropRight 1 map display mkString " "} (${display(term.subtrees.last)})"
  
}


object Piping {
  
  implicit class Piper[X](private val x: X) extends AnyVal {
    def |>[Y](f: X => Y) = f(x)
  }
  
  implicit class PiedPiper[X,Y](private val f: X => Y) extends AnyVal {
    def |>:(x: X) = f(x)
  }
 
}


object Strip {
  val numeral: PartialFunction[Int, String] = { case x: Int => "$"+x }
  val greek = "αβγδεζηθικλμνξοπρστυφχψω".toList orElse numeral
  val boxedAbc = List("🄰","🄱","🄲","🄳","🄴","🄵","🄶","🄷","🄸","🄹","🄺","🄻","🄼","🄽","🄾","🄿","🅀","🅁","🅂","🅃","🅄","🅅","🅆","🅇","🅈","🅉") orElse numeral
}