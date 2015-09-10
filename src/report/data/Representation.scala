package report.data

import syntax.Tree
import syntax.AstSugar._



object Rich {

  import report.{ObjectTree,ObjectVBox,BulletDecorator}

  def displayRich(xterm: Tree[Term]): AsJson =
    displayRich(List(xterm))

  def displayRich(xterm: Tree[Term], bullet: String): AsJson =
    displayRich(List(xterm), bullet)

  def displayRich(forest: List[Tree[Term]], bullet: String = "•") = {
    new ObjectVBox(forest map (t =>
      new ObjectTree(t map (_.toPrettyTape))
        with BulletDecorator { override val ● = bullet }))
  }
  
}


