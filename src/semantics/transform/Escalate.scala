package semantics.transform

import syntax.AstSugar._
import semantics.{LambdaCalculus, TypePrimitives, TypedTerm, Scope}
import semantics.TypeTranslation.TypingSugar



/**
 * Turns all slash expressions "f / g" to simple scalar conditionals by introducing
 * appropriate eta-expansions, "x ↦ (f x) / (g x)".
 *
 * @param scope
 */
class Escalate(implicit scope: Scope) {

  import TypedTerm.{preserve, typeOf, typeOf_!}
  import TypePrimitives.{args=>targs,ret=>tret,shape}
  import TypingSugar.qvars

  private val / = I("/")

  def apply(t: Term): Term = (t, typeOf(t)) match {
    case (T(/, s), Some(typ)) if !typ.isLeaf =>
      val (args, bodies) = distribAbs(targs(typ), t.split)
      preserve(t, TI("↦")(args)(typed_/::(bodies, tret(typ)))>>)
    case _ =>
      preserve(t, T(t.root, t.subtrees map apply))
  }

  def typed_/::(elems: Iterable[Term], typ: Term) =
    elems reduce ((x,y) => TypedTerm(x /: y, typ))

  def distribAbs(argtypes: List[Term], parts: List[Term]) = {
    val arglists = parts map (x => LambdaCalculus.uncurry(x)._1)
    val sentinel = qvars(argtypes)
    val nargs = argtypes.length
    val args = transpose(nargs, arglists :+ sentinel) map (_ find (_.root != "?") get) map TypedTerm.raw toList ;
    (args, parts map (t => TypedTerm(t :@ args, tret(typeOf_!(t)))))
  }

  def transpose[A](n: Int, xss: List[List[A]]) =
    0 until n map (i => xss collect { case l if i<l.length => l(i) })
}