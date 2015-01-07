package syntax


trait Scheme {
  type Term = Tree[Identifier]
  
  def apply(args: Term*): Term
  def apply(args: List[Term]): Term = apply(args:_*)
}


object Scheme {
  
  type Term = Tree[Identifier]
    
  implicit class SchemeFun(val f: (Term*) => Term) extends Scheme {
    def apply(args: Term*) = f(args:_*)
  }
  
  implicit class SchemeFun1(val f: Term => Term) extends Scheme {
    def apply(args: Term*) = args.toList match {
      case List(a) => f(a)
      case _ =>
        throw new Exception(s"invalid number of args for scheme; expected 1, got ${args.length}")
    }
  }
  
  implicit class SimplePredicateSymbol(val P: Term) extends Scheme {
    // note: using P(args:_*) would cause infinite recursion
    def apply(args: Term*) = AstSugar.TreeBuild(P)(args:_*)
  }

}
      