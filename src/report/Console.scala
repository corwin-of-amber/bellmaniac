package report.console

import java.io.ByteArrayOutputStream

import semantics.TypedTerm
import semantics.TypedTerm._
import syntax.AstSugar._
import syntax.Tree
import syntax.transform.ExtrudedTerms


class NestedListTextFormat[A](val ● : String = "•", val indent: String = "  ")(fmt: A => String = ((a:A) => a.toString)) {

  def layOut(tree: Tree[A], level: String = "") {
    println(s"$level${●} ${fmt(tree.root)}")
    for (s <- tree.subtrees)
      layOut(s, level + indent)
  }


  def layOutAndAnnotate(t: Tree[A], annot: (Tree[A] => Option[Any]),
                        fallback: (Tree[A] => String) = ((x: Tree[A]) => x.toString), level: String = "") {
    print(s"$level${●} ")
    if (t.nodes forall (annot(_) == None))
      println(fallback(t))
    else {
      print(fmt(t.root))
      annot(t) match {
        case Some(a) => println(s"      〔 $a 〕")
        case _ => println
      }
      for (s <- t.subtrees)
        layOutAndAnnotate(s, annot, fallback, level + indent)
    }
  }
}


object Console {

  def display(xterm: Tree[Term]) {
    val format = new NestedListTextFormat[String]()()
    format.layOut(xterm map { x => TypedTerm.typeOf(x) match {
      case Some(typ) => s"${annotateWithTypes(x) toPretty}      〔 ${typ toPretty} 〕"
      case _ => annotateWithTypes(x) toPretty
    }})
  }

  def annotateWithTypes(term: Term, top: Boolean=true): Term = {
    if (term =~ ("↦", 2)) {
      val List(arg, body) = term.subtrees
      val targ = if (top) arg else typeOf(arg) match { case Some(typ) => arg :: typ case _ => arg }
      T(term.root, List(targ, body) map (annotateWithTypes(_, top)))
    }
    else if (term =~ ("@", 2) && term.subtrees(0) =~ ("↦", 2))
      T(term.root, List(annotateWithTypes(term.subtrees(0), false),
        annotateWithTypes(term.subtrees(1), true)))
    else {
      val ttop =
        if (term =~ (":", 2)) top else false
      T(term.root, term.subtrees map (annotateWithTypes(_, ttop)))
    }
  }

  def display(xterm: ExtrudedTerms) { display(xterm.terms) }

  def andOut[X](op: => X) = {
    val ss = new ByteArrayOutputStream
    val ret = scala.Console.withOut(ss)(op)
    (ret, new String(ss.toByteArray(), "utf-8"))
  }

  def asString(op: => Unit) = andOut(op)._2

  def sdisplay(xterm: ExtrudedTerms) = asString { display(xterm) }

}