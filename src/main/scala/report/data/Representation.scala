package report.data

import syntax.Tree
import syntax.AstSugar._
import syntax.transform.ExtrudedTerms
import semantics.TypedTerm


object Rich {

  import report.{ObjectTree,ObjectVBox,BulletDecorator}

  def display(xterm: Tree[Term]): AsJson =
    display(List(xterm))

  def display(xterm: Tree[Term], bullet: String): AsJson =
    display(List(xterm), bullet)

  def display(forest: List[Tree[Term]], bullet: String = "•") = {
    new ObjectVBox(forest map (t =>
      new ObjectTree(t map annotate)
        with BulletDecorator { override val ● = bullet }))
  }

  def display(ex: ExtrudedTerms): AsJson = display(ex.terms, "•")

  def display(ex: ExtrudedTerms, bullet: String): AsJson = display(ex.terms, bullet)
  
  def annotate(term: Term) = TypedTerm.typeOf(term) match {
    case Some(typ) => term.toPrettyTape + s"\t〔 ${typ toPretty} 〕"
    case None => term.toPrettyTape
  }
}


