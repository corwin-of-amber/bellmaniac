
package syntax

import report.data.TapeString
import scala.collection.generic.CanBuildFrom


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
    def toPretty: String = Formula.display(term) toString
    def toPrettyTape: TapeString = Formula.display(term)
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
    def ↦:(args: Term*) = TI("↦")((args :+ term):_*)>>
    def &(that: Term) = TI("&")(term, that)
    def |(that: Term) = TI("|")(term, that)
    def <->(that: Term) = TI("<->")(term, that)
    def unary_~ = TI("~")(term)
    def x(that: Term) = TI("x")(term, that)
    def ∩(that: Term) = TI("∩")(term, that)
    def +(that: Term) = TI("+"):@(term, that)
    def -(that: Term) = TI("-"):@(term, that)
    def =:=(that: Term) = TI("=")(term, that)
    
    def :@(that: Term*) = @:(term)(that:_*).foldLeft
    def :@(these: List[Term]) = @:(term)(these:_*).foldLeft
    
    def ~>[A](that: A) = term.leaf -> that
    
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

    def >> : Term =
      if (term.subtrees.length == 1 && term.subtrees(0) == `...`) term
      else term.foldRight
  }
  
  def &&(conjuncts: Term*): Term = &&(conjuncts.toList)
  def &&(conjuncts: List[Term]) = TI("&")(conjuncts)<<

  def /::(parts: Term*): Term = /::(parts.toList)
  def /::(parts: List[Term]) = TI("/")(parts)>>
  
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
  import TapeString.{fromAny,TapeFormat}
    
  object Assoc extends Enumeration {
    type Assoc = Value
    val Left, Right, None = Value
  }
  import Assoc.Assoc
  
  class InfixOperator(val literal: String, val priority: Int, val assoc: Assoc=Assoc.None) {
    def format(term: AstSugar.Term) = {
      /**/ assume(term.subtrees.length == 2) /**/
      val op = if (literal == null) display(term.root) else literal
      tape"${display(term.subtrees(0), priority, Assoc.Left)} $op ${display(term.subtrees(1), priority, Assoc.Right)}"
    }
  }
  
  class AppOperator(literal: String, priority: Int, assoc: Assoc=Assoc.None) extends InfixOperator(literal, priority, assoc) {
    override def format(term: AstSugar.Term) = {
      /**/ assume(term.subtrees.length == 2) /**/
      val List(fun, arg) = term.subtrees
      if (fun =~ ("+", 0))
        tape"${display(arg, if (isOp(arg, "+")) priority else 0, Assoc.Left)} +"
      else if (fun =~ ("-", 0))
        tape"${display(arg, if (isOp(arg, "-")) priority else 0, Assoc.Left)} -"
      else {
        val lst = splitOp(term, "cons")
        if (lst.length > 1 && lst.last =~ ("nil", 0))
          tape"⟨${lst dropRight 1 map display mkString ", "}⟩"
        else
          tape"${display(fun, priority, Assoc.Left)} ${display(arg, priority, Assoc.Right)}"
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
  
  def display(symbol: Identifier): TapeString = 
    symbol.literal.toString || symbol
  
  def display(term: AstSugar.Term): TapeString =
    if (QUANTIFIERS contains term.root.toString)
      displayQuantifier(term.unfold)
    else if (term =~ (":", 2) && term.subtrees(0) =~ ("let", 0))// && term.subtrees(1) =~ ("@", 2) && term.subtrees(1).subtrees(0) =~ ("↦", 2))
       tape"let ${display(term.subtrees(1).subtrees(0).subtrees(0))} := ${display(term.subtrees(1).subtrees(1))} in ${display(term.subtrees(1).subtrees(0).subtrees(1))}"
    else
      (if (term.subtrees.length == 2) INFIX get term.root.toString else None)
      match {
        case Some(op) => 
          op.format(term)
        case None => 
          if (term.isLeaf) display(term.root)
          else tape"${display(term.root)}(${term.subtrees map display mkTapeString ", "})"
      }
  
  def display(term: AstSugar.Term, pri: Int, side: Assoc): TapeString = {
    if (term.subtrees.length != 2) display(term)
    else {
      val d = display(term)
      INFIX get term.root.toString match {
        case Some(op) =>
          if (op.priority < pri || op.priority == pri && side == op.assoc) d else tape"($d)"
        case _ => d
      }
    }
  }

  def displayQuantifier(term: AstSugar.Term) =
    tape"${display(term.root)}${term.subtrees dropRight 1 map display mkTapeString " "} (${display(term.subtrees.last)})"
  
}


object Piping {
  
  implicit class Piper[X](private val x: X) extends AnyVal {
    def |>[Y](f: X => Y) = f(x)
    def |--[Y](tee: X => Y) = { tee(x) ; x }
  }
  
  implicit class PiedPiper[X,Y](private val f: X => Y) extends AnyVal {
    def |>:(x: X) = f(x)
    def |>>:(xs: Iterable[X]) = xs map f
  }

  implicit class IterablePiper[X](private val x: Iterable[X]) extends AnyVal {
    def |>>[Y](f: X => Y) = x map f
  }
  
}


object Strip {
  val numeral: PartialFunction[Int, String] = { case x: Int => "$"+x }
  val greek = "αβγδεζηθικλμνξοπρστυφχψω".toList orElse numeral
  val boxedAbcList = List("🄰","🄱","🄲","🄳","🄴","🄵","🄶","🄷","🄸","🄹","🄺","🄻","🄼","🄽","🄾","🄿","🅀","🅁","🅂","🅃","🅄","🅅","🅆","🅇","🅈","🅉")
  val boxedAbc = boxedAbcList orElse numeral
  val boxedAbcOverline = (boxedAbcList map (_ + "̅")) orElse numeral
  val boxedAbcUnderbar = (boxedAbcList map (_ + "̱")) orElse numeral
  val boxedAbcThenUnderbar = (boxedAbcList ++ (boxedAbcList map (_ + "̱"))) orElse numeral
}