package syntax

import AstSugar.Term
import syntax.transform.TreeSubstitution



trait Scheme extends Subroutine[Term, Term]


object Scheme {
      
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
    // note: using P(args:_*) here would cause infinite recursion
    def apply(args: Term*) = AstSugar.TreeBuild(P)(args:_*)
  }

  class Template(val vars: List[Identifier], val template: Term) extends Scheme {
    import AstSugar._
    
    def apply(args: Term*): Term = {
      val subst = new TreeSubstitution(vars map (T(_)) zip args)
      subst(template)
    }
  }

}



trait Subroutine[A,X] {
  def apply(args: A*): X
  def apply(args: List[A]): X = apply(args:_*)
}

object Subroutine {
  trait Arity { val arity: Int }
  
  def apply[A,B](f: A => B) = new Subroutine[A,B] with Arity { def apply(l:A*) = l match { case Seq(x) => f(x) } ; val arity = 1 }
  def apply[A,B](f: (A,A) => B) = new Subroutine[A,B] with Arity { def apply(l:A*) = l match { case Seq(x,y) => f(x,y) } ; val arity = 2 }
  def apply[A,B](f: (A,A,A) => B) = new Subroutine[A,B] with Arity { def apply(l:A*) = l match { case Seq(x,y,z) => f(x,y,z) } ; val arity = 3 }
}
