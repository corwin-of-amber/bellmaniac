package report.console

import syntax.Tree



class NestedListTextFormat[A](val ● : String = "•", val indent: String = "  ")(fmt: A => String = ((a:A) => a.toString)) {
    
  def layOut(tree: Tree[A], level: String = "") {
    println(s"$level${●} ${fmt(tree.root)}")
    for (s <- tree.subtrees)
      layOut(s, level + indent)
  }
  
  

  def layOutAndAnnotate(t: Tree[A], annot: (Tree[A] => Option[Any]), 
      fallback: (Tree[A] => String) = ((x:Tree[A]) => x.toString), level: String = "") {
    print(s"$level${●} ")
    if (t.nodes forall (annot(_) == None))
      println(fallback(t))
    else {
      print(fmt(t.root))
      annot(t) match { case Some(a) => println(s"      〔 $a 〕") case _ => println }
      for (s <- t.subtrees)
        layOutAndAnnotate(s, annot, fallback, level + indent)
    }
  }
    
}