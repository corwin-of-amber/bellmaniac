package report.data

import syntax.Tree
import syntax.AstSugar._



class Rich { 
  
  def displayRich(forest: List[Tree[Term]], bullet: String = "•") = {
    import report.{ObjectTree,ObjectVBox,BulletDecorator}
    new ObjectVBox(forest map (t => 
      new ObjectTree(t map (_.toPrettyTape))
        with BulletDecorator { override val ● = bullet }))
  }
  
}