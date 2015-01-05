
package syntax


object AstSugar {

  type Term = Tree[Identifier]
  
  def I(a: Any) = new Identifier(a)
  def S(a: Any) = new Identifier(a, "set")
  def V(a: Any) = new Identifier(a, "variable")
  def T(a: Identifier, b: List[Tree[Identifier]]=List()) = new Tree(a, b)
  def TI(a: Any, b: List[Tree[Identifier]]=List()) = T(I(a), b)
  def TV(a: Any, b: List[Tree[Identifier]]=List()) = T(V(a), b)
  
  implicit class TreeBuild[A](private val t: Tree[A]) extends AnyVal {
    def apply(subtrees: Tree[A]*) = new Tree(t.root, t.subtrees ++ subtrees)
  }
  
  implicit class FormulaDisplay(private val term: Term) extends AnyVal {
    def toPretty: String = Formula.display(term)
  }
}


object Formula {
  val INFIX = Map("->" -> 1, "<->" -> 1, "&" -> 1, "<" -> 1)
  val QUANTIFIERS = Set("forall", "∀", "exists", "∃")
  
  def display(term: AstSugar.Term): String =
    if (QUANTIFIERS contains term.root.toString)
      displayQuantifier(term.unfold)
    else
    (if (term.subtrees.length == 2) Formula.INFIX get term.root.toString else None)
    match {
      case Some(pri) => 
        s"${display(term.subtrees(0), pri)} ${term.root} ${display(term.subtrees(1), pri)}"
      case None => 
        if (term.isLeaf) term.root.toString
        else s"${term.root}(${term.subtrees map display mkString ", "})"
    }
  
  def display(term: AstSugar.Term, pri: Int): String = {
    val subpri = (INFIX get term.root.toString) getOrElse 0
    if (subpri < pri) display(term) else s"(${display(term)})"
  }

  def displayQuantifier(term: AstSugar.Term) =
    s"${term.root}${term.subtrees dropRight 1 map display mkString " "} (${display(term.subtrees.last)})"
  
}