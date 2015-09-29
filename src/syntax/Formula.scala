package syntax

import com.mongodb.{BasicDBList, DBObject, BasicDBObject}
import report.data._
import semantics.TypedTerm


/**
 * Identifiers are the basic blocks of formula ASTs; a term is defined as Tree[Identifier], so an Identifier is
 * present at every node.
 * Each Identifier is either a connective, a quantifier, a variable, etc.
 *
 * @param literal a textual representation of the identifier (typically a string or a number)
 * @param kind "connective", "quantifier", "variable", "function", "predicate", "set"; use "?" for unknown (wildcard)
 * @param ns namespace. Can be any object. Identifiers with the same literal (and matching kinds) but different ns
 *           are considered unequal. This helps avoid name clashes.
 */
class Identifier (val literal: Any, val kind: String = "?", val ns: AnyRef = null) extends AsJson {
  override def toString() = literal.toString

  override def equals(other: Any) = other match {
    case other: Identifier =>
      literal == other.literal &&
        (kind == "?" || other.kind == "?" || kind == other.kind) &&
        ns == other.ns

    case x => literal == x
  }

  override def hashCode = (literal, ns).hashCode  // 'kind' cannot be part of the hashCode, because "?" is a wildcard

  override def asJson(container: SerializationContainer): BasicDBObject = {
    val j = new BasicDBObject("$", "Identifier").append("literal", container.any(literal)).append("kind", kind)
    if (ns != null)
      container match {
        case numerator: Numerator => j.append("ns", numerator --> ns)
        case _ => j
      }
    else j
  }
}


/**
 * Helper functions for formatting formulas as text and for serialization.
 */
object Formula {

  import AstSugar.{Term,DSL}
  import TapeString.{fromAny,TapeFormat}

  object Assoc extends Enumeration {
    type Assoc = Value
    val Left, Right, None = Value
  }
  import Assoc.Assoc

  class InfixOperator(val literal: String, val priority: Int, val assoc: Assoc=Assoc.None) {
    def format(term: AstSugar.Term) = {
      /**/ assume(term.subtrees.length == 2) /**/
      val op = if (literal == null) display(term.root) else literal
      tape"${display(term.subtrees(0), priority, Assoc.Left)} $op ${display(term.subtrees(1), priority, Assoc.Right)}"
    }
  }

  class AppOperator(literal: String, priority: Int, assoc: Assoc=Assoc.None) extends InfixOperator(literal, priority, assoc) {
    override def format(term: AstSugar.Term) = {
      /**/ assume(term.subtrees.length == 2) /**/
      val List(fun, arg) = term.subtrees
      if (fun =~ ("+", 0) || fun =~ ("-", 0))
        tape"${display(arg, if (isOp(arg, fun.leaf)) priority else 0, Assoc.Left)} ${fun.leaf}"
      else {
        val lst = splitOp(term, "cons")
        if (lst.length > 1 && lst.last =~ ("nil", 0))
          tape"⟨${lst dropRight 1 map display mkTapeString ", "}⟩"
        else
          tape"${display(fun, priority, Assoc.Left)} ${display(arg, priority, Assoc.Right)}"
      }
    }

    def isOp(term: Term, op: Any) = (term =~ ("@", 2)) && (term.subtrees(0) =~ ("@", 2)) && (term.subtrees(0).subtrees(0) =~ (op, 0))

    def splitOp(term: Term, op: Any): List[Term] =
      if (isOp(term, op))
        splitOp(term.subtrees(0).subtrees(1), op) ++ splitOp(term.subtrees(1), op)
      else List(term)
  }

  def O(literal: String, priority: Int, assoc: Assoc=Assoc.None) =
    new InfixOperator(literal, priority, assoc)

  def M(ops: InfixOperator*) = ops map (x => (x.literal, x)) toMap

  val INFIX = M(O("->", 1, Assoc.Right), O("<->", 1), O("&", 1), O("|", 1), O("<", 1), O("=", 1), O("↦", 1, Assoc.Right),
    O(":", 1), O("::", 1), O("/", 1), O("|_", 1), O("|!", 1), O("∩", 1), O("x", 1)) ++
    Map("@" -> new AppOperator("", 1, Assoc.Left))
  val QUANTIFIERS = Set("forall", "∀", "exists", "∃")

  class TermTag(val term: Term) extends AnyVal

  def display(symbol: Identifier): TapeString =
    symbol.literal.toString //|-| symbol

  def display(term: AstSugar.Term): TapeString =
    if (QUANTIFIERS contains term.root.toString)
      displayQuantifier(term.unfold)
    else if (term =~ (":", 2) && term.subtrees(0) =~ ("let", 0))// && term.subtrees(1) =~ ("@", 2) && term.subtrees(1).subtrees(0) =~ ("↦", 2))
      tape"let ${display(term.subtrees(1).subtrees(0).subtrees(0))} := ${display(term.subtrees(1).subtrees(1))} in ${display(term.subtrees(1).subtrees(0).subtrees(1))}"
    else
      (if (term.subtrees.length == 2) INFIX get term.root.toString else None)
      match {
        case Some(op) =>
          op.format(term)
        case None =>
          if (term.isLeaf) display(term.root) |-| new TermTag(term)
          else tape"${display(term.root)}(${term.subtrees map display mkTapeString ", "})"
      }

  def display(term: AstSugar.Term, pri: Int, side: Assoc): TapeString = {
    if (term.subtrees.length != 2) display(term)
    else {
      val d = display(term)
      INFIX get term.root.toString match {
        case Some(op) =>
          if (op.priority < pri || op.priority == pri && side == op.assoc) d else tape"($d)"
        case _ => d
      }
    }
  }

  def displayQuantifier(term: AstSugar.Term) =
    tape"${display(term.root)}${term.subtrees dropRight 1 map display mkTapeString " "} (${display(term.subtrees.last)})"

  implicit class OrElse[A](val o: A) extends AnyVal {
    def orElse(ow: => A) = if (o == null) ow else o
    def andThen[B](op: A => B, ow: => B): B = if (o == null) ow else op(o)
    def opt = andThen(Some(_), None)
  }

  // Perhaps this should not be here
  def fromJson(json: DBObject)(implicit container: SerializationContainer): Term = {
    def id(json: DBObject) = {
      // TODO typed identifier, ns
      new Identifier(
        literal = json.get("literal") orElse { throw new SerializationError("'literal' missing", json); },
        kind = json.get("kind") andThen (_.toString, "?")
      )
    }
    def term(any: AnyRef) = fromJson(any.asInstanceOf[DBObject])
    import scala.collection.JavaConversions._
    val root = id(json.get("root") andThen (_.asInstanceOf[DBObject], { throw new SerializationError("'root' missing", json) }))
    val subs = json.get("subtrees") andThen (_.asInstanceOf[BasicDBList].toList map term, List())
    val tree = new Term(root, subs)
    json.get("type") andThen (typ => TypedTerm(tree, term(typ)), tree)
  }
}

