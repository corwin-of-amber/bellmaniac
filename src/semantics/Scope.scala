
package semantics

import syntax.AstSugar.Term
import syntax.{Tree, Identifier, AstSugar}
import syntax.transform.TreeSubstitution
import semantics.TypeTranslation.Declaration



object Domains {
  val TOP = new Identifier("⊤", "set")
  val BOT = new Identifier("⊥", "set")
  
  val ⊤ = TOP
  val ⊥ = BOT
  
  class Extends(val sub: Identifier, val sup: Identifier) {}
  
  implicit class SubsortAssoc(private val sup: Identifier) extends AnyVal {
    def :<: (sub: Identifier) = new Extends(sub, sup)
    def :<: (sub: Tree[Identifier]) = new Extends(sub.leaf, sup)
  }

  implicit class SubsortAssocT(private val sup: Tree[Identifier]) extends AnyVal {
    def :<: (sub: Identifier) = new Extends(sub, sup.leaf)
    def :<: (sub: Tree[Identifier]) = new Extends(sub.leaf, sup.leaf)
  }
}



class Domains {

  import Domains._
  import AstSugar.{T,TreeBuild}
  import Scope.TypingException

  var hierarchy = new Tree(⊤, List(new Tree(⊥)))

  def findSortHie(sort: Identifier) = hierarchy.nodes find (_.root == sort)
  
  private def hei_⊥ = findSortHie(⊥) getOrElse {assert(false, "⊥ is missing!") ; null}
  
  def declare(ext: Extends) {
    findSortHie(ext.sup) match {
      case Some(hie) =>
        /**/ assert(ext.sub.kind == "set") /**/
        val hie0 = if (hie.subtrees exists (_.root == ⊥)) T(hie.root)(T(ext.sub)(hei_⊥))
          else hie(T(ext.sub)(hei_⊥))
        hierarchy = new TreeSubstitution[Identifier](List(hie -> hie0))(hierarchy)
      case None =>
        throw new TypingException(s"undefined supertype '${ext.sup}'")
    }
  }

  def declare(id: Identifier) { declare(id :<: ⊤) }
  
  def declare(id: Term) { declare(id.leaf) }

  /**
   * Adds an artificial "⊥" sub-sort as the lowest descendant of every master.
   * These makes a sub-lattice below each master, which is used by the type-checker.
   */
  def cork() = {
    val floor = List(T(⊥))
    val corks = masters flatMap { master =>
        val ley = master.nodes filter (_.subtrees == floor)
        val newbot = new Identifier(s"⊥.${master.root}", "set", ⊥)
        ley map (t => (t, T(t.root, List(T(newbot, t.subtrees)))))
      }
    hierarchy = hierarchy.replaceDescendants(corks)
  }

  def contains(sort: Identifier) = findSortHie(sort).isDefined
  
  def masters = hierarchy.subtrees
  
  def getMastersOf(sort: Identifier) =
    if (sort == ⊤) List(⊤)
    else
      for (s <- hierarchy.subtrees if s.nodes exists (_.root == sort)) yield s.root

  def getMasterOf(sort: Identifier) = getMastersOf(sort) match {
      case List() => throw new TypingException(s"undefined sort '$sort'")
      case List(x) => x
      case multi => throw new TypingException(s"ambiguous top-level sort for '$sort': $multi")
    }

  def isMaster(sort: Identifier) = masters exists (_.root == sort)

  def supers(sort: Identifier) = {
    def f(t: Tree[Identifier]): List[Identifier] = 
      if (t.root == sort) List(t.root)
      else t.subtrees flatMap f match {
        case Nil => Nil
        case l => t.root :: l
      }
    f(hierarchy)
  }
  
  def subs(sort: Identifier) = findSortHie(sort) match {
    case Some(hie) => hie.bfs map (_.root) toList
    case None => throw new TypingException(s"undefined sort '$sort'")
  }
  
  def <=(sort1: Identifier, sort2: Identifier) = subs(sort2) contains sort1
  def >=(sort1: Identifier, sort2: Identifier) = <=(sort2, sort1)
  
  def max(sorts: Iterable[Identifier]) = sorts.find (x => sorts.forall (<=(_, x)))
  def min(sorts: Iterable[Identifier]) = sorts.find (x => sorts.forall (>=(_, x)))
  
  def join(sort1: Identifier, sort2: Identifier) = {
    val (supers1, supers2) = (supers(sort1), supers(sort2))
    min(supers1 intersect supers2) getOrElse
      { assert(false, s"$sort1 and $sort2 do not have a minimal supertype!") ; null }
  }

  def meet(sort1: Identifier, sort2: Identifier) = {
    val (subs1, subs2) = (subs(sort1), subs(sort2))
    max(subs1 intersect subs2) getOrElse
      { assert(false, s"$sort1 and $sort2 do not have a maximal subtype!") ; null }
  }
  
}

/**
 * A cheating techniques to reason about second-order functions.
 * The function type is represented by a first-order sort that reflects it.
 */
class FunctionType(val args: List[Identifier], val ret: Identifier) {
  import AstSugar._

  val faux = new Identifier((args :+ ret) mkString "→", "set", this)
  val app = new Declaration(
      List(TypedIdentifier( new Identifier("@", "function", this), 
                            TI("->")(faux +: args :+ ret map (T(_))).foldRight ),
           TypedIdentifier( new Identifier("|@|", "predicate", this),
                            TI("->")(faux +: args :+ S("") map (T(_))).foldRight )), List() )
                                 
  def abs(f: Declaration) = {
    import TypeTranslation.{In,Out}
    import TypeTranslation.TypingSugar._
    val f_abs = TypedIdentifier( new Identifier(s"${f.head.untype}#", "function", new Uid), T(faux) )
    val f_abs_supp = TypedIdentifier( new Identifier(s"|${f.head.untype}#|", "predicate", new Uid), T(S("")) )
    val micro = (args map ((x) => In(T(x)))) :+ Out(T(ret))
    val (varids, _, _) = TypeTranslation.contract(f_abs, micro)
    val vars = varids map (T(_))
    val assumptions = List(
        T(f_abs_supp) ,
        ∀(vars)( (T(app.head)(T(f_abs) :: vars) =:= T(f.head)(vars)) &
                 (T(app.support)(T(f_abs) :: vars) <-> T(f.support)(vars))  )
      )
    new Declaration(List(f_abs, f_abs_supp), assumptions)
  }
  
  def abs(f: Identifier) =
    TypedIdentifier( new Identifier(s"${f.literal}#", "function", new Uid), T(faux) )

}

class Scope {

  val sorts = new Domains
  val functypes = collection.mutable.Map[Term, FunctionType]()

  def this(base: Term*)(sub: Domains.Extends*) = {
    this()
    base map sorts.declare
    sub map sorts.declare
    sorts.cork()
  }

  def declFunctionType(rawType: Term): FunctionType = {
    def arg(e: Term) = if (e.isLeaf) e.root else declFunctionType(e).faux
    functypes get rawType match {
      case Some(functype) => functype
      case _ =>
        val functype = new FunctionType(TypePrimitives.args(rawType) map arg, arg(TypePrimitives.ret(rawType)))
        functypes += ((rawType, functype))
        functype
    }
  }
}

object Scope {

  import syntax.AstSugar._
  import Domains.SubsortAssoc

  class TypingException(msg: String) extends TraceableException(msg)

  import com.mongodb.{DBObject, BasicDBList}
  import report.data.SerializationContainer
  import scala.collection.JavaConversions._

  def fromJson(json: DBObject)(implicit container: SerializationContainer) = json match {
    case list: BasicDBList =>
      val ids = list collect { 
        case l: BasicDBList => l.toList match {
          case List(subsort: DBObject, supersort: DBObject) => Identifier.fromJson(subsort) :<: Identifier.fromJson(supersort)
        }
        case x: DBObject => Identifier.fromJson(x)
      }
      val scope = new Scope
      ids foreach { case id: Identifier => scope.sorts.declare(id) case ext: Domains.Extends => scope.sorts.declare(ext) }
      scope.sorts.cork()
      scope
  }
}

