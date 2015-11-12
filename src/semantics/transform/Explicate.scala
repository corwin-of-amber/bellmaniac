package semantics.transform

import syntax.AstSugar._
import semantics._


/**
 * Makes guard conditions explicit (hence the name) by creating guard expressions 'a |! b'
 * when appropriate, according to types of sub-terms.
 *
 * @param includePreconditions
 * @param scope
 */
class Explicate(includePreconditions: Boolean=true)(implicit scope: Scope) {

  import TypedTerm.{preserve, typeOf_!}
  import LambdaCalculus.{isApp, isAbs}

  val @: = I("@")
  val :- = I(":")
  val |! = I("|!")

  def apply(t: Term) = explicate0(t)(collate(t)(List()))

  def explicate0(t: Term)(implicit map: Map[Id[Term], List[Term]]): Term = map get t match {
    case None => preserve(t, T(t.root, t.subtrees map explicate0))
    case Some(Nil) => preserve(t, T(t.root, t.subtrees map explicate0))
    case Some(guard) => preserve(t, preserve(t, T(t.root, t.subtrees map explicate0)) |! &&(guard))
  }

  def collate(t: Term)(implicit assumptions: List[Term]): Map[Id[Term], List[Term]] = isApp(t) match {
    case Some((f, args)) =>
      val precond = nontriv(TypeTranslation.checks(scope, typeOf_!(f), args))
      accumulate((f +: args) flatMap (x => collate(x)(assumptions ++ precond)) toMap, t, precond)
    case _ => isAbs(t) match {
      case Some((vars, body)) =>
        val precond = nontriv(TypeTranslation.checks(scope, typeOf_!(t), vars))
        val postcond = {
          assert(scope.sorts.isMaster(TypePrimitives.ret(typeOf_!(t)).leaf), "unimplemenetd; postcondition required")
          List()
        }
        accumulate(collate(body)(assumptions ++ precond ++ postcond), body,
                   if (includePreconditions) precond else List())
      case _ => t match {
        case T(`|!`, List(expr, cond)) => collate(expr)
        case _ =>
          t.subtrees flatMap collate toMap
      }
    }
  }

  def accumulate[A, B](map: Map[A, List[B]], key: A, values: List[B]) = map get key match {
    case None => map + (key -> values)
    case Some(existing) => map + (key -> (existing ++ values))
  }

  def hoist(t: Term): Term = t match {
    case T(`@:`, sub) =>
      val guarded = sub map hoist map {
        case T(`|!`, List(expr, cond)) => (expr, Some(cond))
        case expr => (expr, None)
      }
      preserve(t, preserve(t, T(@:, guarded map (_._1))) |!! (guarded flatMap (_._2)))
    case T(`:-`, List(lbl, expr)) => hoist(expr) match {
      case T(`|!`, List(expr, cond)) =>
        preserve(t, preserve(t, lbl :- expr) |! cond)
      case expr => preserve(t, lbl :- expr)
    }
    case T(`|!`, List(expr, cond1)) => hoist(expr) match {
      case T(`|!`, List(expr, cond2)) => preserve(t, expr |! (cond1 & cond2))
      case expr => preserve(t, expr |! cond1)
    }
    case T(r, s) => preserve(t, T(r, s map hoist))
  }

  def isScalar(t: Term) = typeOf_!(t).root != "->"

  def nontriv(asserts: List[Term])(implicit assumptions: List[Term]) =
    asserts filterNot assumptions.contains
}

object Explicate {
  def explicate(t: Term, includePreconditions: Boolean=false)(implicit scope: Scope) =
    new Explicate(includePreconditions) apply t
  def explicateHoist(t: Term, includePreconditions: Boolean=false)(implicit scope: Scope) = {
    val e = new Explicate(includePreconditions)
    e.hoist(e(t))
  }
}
