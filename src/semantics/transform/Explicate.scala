package semantics.transform

import syntax.AstSugar._
import semantics._



class Explicate(implicit scope: Scope) {

  import TypedTerm.{preserve, typeOf_!}
  import LambdaCalculus.{isApp, isAbs}

  val @: = I("@")

  def apply(t: Term) = explicate0(t)(collate(t)(List()))

  def explicate0(t: Term)(implicit map: Map[Id[Term], List[Term]]): Term = map get t match {
    case None => preserve(t, T(t.root, t.subtrees map explicate0))
    case Some(Nil) => preserve(t, T(t.root, t.subtrees map explicate0))
    case Some(guard) => preserve(t, preserve(t, T(t.root, t.subtrees map explicate0)) |! &&(guard))
  }

  def collate(t: Term)(implicit assumptions: List[Term]): Map[Id[Term], List[Term]] = isApp(t) match {
    case Some((f, args)) =>
      val precond = nontriv(TypeTranslation.checks(scope, typeOf_!(f), args))
      accumulate(args flatMap collate toMap, t, precond)
    case _ => isAbs(t) match {
      case Some((vars, body)) =>
        val precond = vars filter isScalar flatMap (v => TypeTranslation.checks(scope, v.typedLeaf, List()))
        accumulate(collate(body)(assumptions ++ precond), body, precond)
      case _ =>
        t.subtrees flatMap collate toMap
    }
  }

  def accumulate[A, B](map: Map[A, List[B]], key: A, values: List[B]) = map get key match {
    case None => map + (key -> values)
    case Some(existing) => map + (key -> (existing ++ values))
  }

  def isScalar(t: Term) = typeOf_!(t).root != "->"

  def nontriv(asserts: List[Term])(implicit assumptions: List[Term]) =
    asserts filterNot assumptions.contains
}

object Explicate {
  def explicate(t: Term)(implicit scope: Scope) = new Explicate apply t
}
