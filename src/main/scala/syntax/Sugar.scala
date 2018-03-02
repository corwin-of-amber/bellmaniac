
package syntax

import com.mongodb.{BasicDBList, DBObject}
import report.data.{SerializationContainer, TapeString}
import semantics.{TypedTerm, Prelude}


object AstSugar {

  type Term = Tree[Identifier]
  object Term_: {
    def unapply[A](t: Tree[A]) = if (t.root.isInstanceOf[Identifier]) Some(t.asInstanceOf[Term]) else None
  }
  
  def I(a: Any) = new Identifier(a)
  def I(a: Any, k: String) = new Identifier(a, k)
  def S(a: Any) = new Identifier(a, "set")
  def V(a: Any) = new Identifier(a, "variable")
  object T {
    def apply(a: Identifier, b: List[Tree[Identifier]]=List()) = new Tree(a, b)
    def unapply(t: Term) = Some(t.root, t.subtrees)
  }
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
  val ∩ = I("∩", "operator")
  val ↦ = I("↦", "operator")
  val ∧ = I("∧", "connective")
  val ∨ = I("∨", "connective")
  val <-> = I("<->", "connective")
  val ¬ = I("¬", "connective")
  val `=` = I("=", "operator")
  val / = I("/", "operator")

  val `_∀` = I("∀", "quantifier")
  
  def ∀(vars: Term*)(body: Term): Term = ∀(vars.toList)(body)
  def ∀(vars: List[Term])(body: Term) = T(`_∀`)(vars)(body).foldRight

  implicit class DSL(private val term: Term) extends AnyVal {
    def ::(that: Term) = TI("::")(that, term)
    def -:(that: Term) = TI(":")(term, that)
    def :-(that: Term) = TI(":")(term, that)
    def |:(that: Term) = TI("|_")(that, term)
    def |!(that: Term) = TI("|!")(term, that)
    def /:(that: Term) = TI("/")(that, term)
    def ->(that: Term) = TI("->")(term, that)
    def ->:(that: Term) = TI("->")(that, term)
    def ↦(that: Term) = T(AstSugar.↦)(term, that)
    def ↦:(that: Term) = T(AstSugar.↦)(that, term)
    def ↦:(args: Seq[Term]) = T(AstSugar.↦)(args.toList :+ term)>>
    def &(that: Term) = T(∧)(term, that)
    def |(that: Term) = T(∨)(term, that)
    def <->(that: Term) = TI("<->")(term, that)
    def unary_~ = T(¬)(term)
    def x(that: Term) = TI("×")(term, that)
    def ∩(that: Term) = T(AstSugar.∩)(term, that)
    def +(that: Term) = TI("+"):@(term, that)
    def -(that: Term) = TI("-"):@(term, that)
    def *(that: Term) = TI("⋅"):@(term, that)
    def ⨁(that: Term) = TI("⨁"):@(term, that)
    def ⨀(that: Term) = TI("⨀"):@(term, that)
    def =:=(that: Term) = T(`=`)(term, that)
    def <(that: Term) = TI("<"):@(term, that)
    
    def :@(that: Term*) = @:(term)(that:_*).foldLeft
    def :@(these: Seq[Term])(implicit d: DummyImplicit) = @:(term)(these:_*).foldLeft

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
      
    def :-/(label: Any): Term =
      semantics.TypedLambdaCalculus.pullOut(term, term :/ label) get  // @@ syntax->semantics dependency?
      
    def \(whatWith: (Term, Term)): Term =
      new syntax.transform.TreeSubstitution(List(whatWith))(term)
       
    def << : Term =
      if (term.subtrees.length == 1 && term.subtrees(0).root == `...`.root) term
      else term.foldLeft

    def >> : Term =
      if (term.subtrees.length == 1 && term.subtrees(0).root == `...`.root) term
      else term.foldRight

    def conjuncts = term split I("∧")
    def disjuncts = term split I("∨")

    def isLiteral: Boolean = 
      if (term =~ ("¬", 1)) term.subtrees(0).isLiteral
      else term.root.kind != "connective"
    
    def |!!(that: List[Term]) = if (that.isEmpty) term else this |! &&(that)
  }
  
  def &&(conjuncts: Term*): Term = &&(conjuncts.toList)
  def &&(conjuncts: List[Term]) = if (conjuncts.isEmpty) Prelude.TRUE else T(∧)(conjuncts)<<

  def ||(disjuncts: Term*): Term = ||(disjuncts.toList)
  def ||(disjuncts: List[Term]) = if (disjuncts.isEmpty) Prelude.FALSE else T(∨)(disjuncts)<<

  def /::(parts: Term*): Term = /::(parts.toList)
  def /::(parts: List[Term]) = TI("/")(parts)>>
  
  val `...` = TI("...")

  // - unique identifiers

  class Uid {}
  def $_ = new Identifier("_", "placeholder", new Uid)
  def $v = new Identifier("?", "variable", new Uid)
  def $v(name: Any) = new Identifier(name, "variable", new Uid)
  def $I(name: Any, kind: String="?") = new Identifier(name, kind, new Uid)
 
  def $TV = T($v)
  def $TV(name: String) = T($v(name))
  def $TI(name: String) = T($I(name))
  def $TI(name: String, kind: String) = T($I(name, kind))

  // - pattern matching for terms

  object -> extends Tree(new Identifier("->", "connective")) {
    def unapply(t: Term) = t match { case T(->.root, List(x,y)) => Some(x,y) case _ => None }
  }

}


object Piping {

  implicit class Piper[X](private val x: X) extends AnyVal {
    def |>[Y](f: X => Y) = f(x)
    def |--[Y](tee: X => Y) = { tee(x) ; x }
  }

  implicit class PiedPiper[X,Y](private val f: X => Y) extends AnyVal {
    def |>:(x: X) = f(x)
    def |>>:(xs: Iterable[X]) = xs map f
    def +|[Z](g: X => Z) = (x: X) => { f(x); g(x) }
  }

  implicit class IterablePiper[X](private val x: Iterable[X]) extends AnyVal {
    def |>>[Y](f: X => Y) = x map f
  }

  def noop(x: Any) = {}  /* sometimes useful as "/dev/null" */
}


object Nullable {
  implicit class OrElse[A](val o: A) extends AnyVal {
    def orElse(ow: => A) = if (o == null) ow else o
    def andThen[B](op: A => B, ow: => B): B = if (o == null) ow else op(o)
    def andThen_[X,B](op: X => B, ow: => B): B = if (o == null) ow else op(o.asInstanceOf[X])
    def opt = andThen(Some(_), None)
    def opt_[X] = andThen_[X,Option[X]](Some(_), None)
  }
}


object Strip {
  val numeral: PartialFunction[Int, String] = { case x: Int => "$"+x }
  val lower = "abcdefghijklmnopqrstuvwxyz".toList orElse numeral
  val greek = "αβγδεζηθικλμνξοπρστυφχψω".toList orElse numeral
  val boxedAbcList = List("🄰","🄱","🄲","🄳","🄴","🄵","🄶","🄷","🄸","🄹","🄺","🄻","🄼","🄽","🄾","🄿","🅀","🅁","🅂","🅃","🅄","🅅","🅆","🅇","🅈","🅉")
  val boxedAbc = boxedAbcList orElse numeral
  val boxedAbcOverline = (boxedAbcList map (_ + "̅")) orElse numeral
  val boxedAbcUnderbar = (boxedAbcList map (_ + "̱")) orElse numeral
  val boxedAbcThenUnderbar = (boxedAbcList ++ (boxedAbcList map (_ + "̲"))) orElse numeral
  val subscript0_9 = "₀₁₂₃₄₅₆₇₈₉".toList orElse numeral
  def subscriptDecimal(num: Int) = num.toString map (c => subscript0_9(c - '0')) mkString
  def subscriptIndexed(symbol: String): PartialFunction[Int, String] = { case x: Int => symbol + subscriptDecimal(x) }
}
