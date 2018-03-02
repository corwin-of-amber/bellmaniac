package syntax

import com.mongodb.{BasicDBList, DBObject, BasicDBObject}
import report.data._
import Nullable._
import semantics.TypedTerm
import syntax.AstSugar.Uid
import semantics.LambdaCalculus


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

  def unapply = Some((literal, kind, ns))
  
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

object Identifier {
  def unapply(id: Identifier) = id.unapply
  def fromJson(json: DBObject)(implicit container: SerializationContainer): Identifier = {
    // TODO typed identifier
    new Identifier(
      literal = json.get("literal") orElse { throw new SerializationError("'literal' missing", json); },
      kind = json.get("kind") andThen (_.toString, "?"),
      ns = json.get("ns") andThen (ns => if (ns == "*") new Uid else container match {
        case numerator: Numerator => (numerator <-- ns.asInstanceOf[Int]).asInstanceOf[AnyRef]
        case _ => null
      }, null)
    )
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
    val Left, Right, Both, None = Value
  }
  import Assoc.Assoc

  trait Notation {
    def format(term: AstSugar.Term): TapeString
    val precedence : Int
    val assoc : Assoc = Assoc.None
    val arity : Int = 2
  }

  class InfixOperator(val literal: String, val precedence: Int, override val assoc: Assoc=Assoc.None) extends Notation {
    def format(term: AstSugar.Term) = {
      /**/ assume(term.subtrees.length == 2) /**/
      val op = if (literal == null) display(term.root) else literal
      tape"${display(term.subtrees(0), precedence, Assoc.Left)} ${op |-| new TermTag(term)} ${display(term.subtrees(1), precedence, Assoc.Right)}"
    }
  }

  class AppOperator(literal: String, precedence: Int, assoc: Assoc=Assoc.Left) extends InfixOperator(literal, precedence, assoc) {
    override def format(term: AstSugar.Term) = {
      /**/ assume(term.subtrees.length == 2) /**/
      val (fun, args) = LambdaCalculus.isApp(term) getOrElse { assert(false, "term has to be an application"); throw new RuntimeException }
      // TODO move this functionality to getNotation and use it here
      (if (fun.isLeaf) INFIX get fun.root else None) match {
        case Some(op) if args.length == op.arity =>  /* special form for (fully applied) infix operators and other notations */
          INFIX(fun.root) format (new Tree(fun.leaf, args))
          //tape"${display(arg, if (isOp(arg, fun.leaf)) precedence else 0, Assoc.Left)} ${fun.leaf}"
        case _ =>          
          /* Special form for list notation */
          val lst = splitOp(term, "cons")
          if (lst.length > 1 && lst.last =~ ("nil", 0))
            tape"⟨${lst dropRight 1 map display mkTapeString ", "}⟩"
          else
            tape"${display(fun, precedence, Assoc.Left)} ${args map (display(_, precedence, Assoc.Right)) mkString " "}"
      }
    }

    def isOp(term: Term, op: Any) = (term =~ ("@", 2)) && (term.subtrees(0) =~ ("@", 2)) && (term.subtrees(0).subtrees(0) =~ (op, 0))

    def splitOp(term: Term, op: Any): List[Term] =
      if (isOp(term, op))
        splitOp(term.subtrees(0).subtrees(1), op) ++ splitOp(term.subtrees(1), op)
      else List(term)
  }
  
  class AbsOperator(literal: String, precedence: Int, assoc: Assoc=Assoc.Right) extends InfixOperator(literal, precedence, assoc) {
    override def format(term: AstSugar.Term) = {
      /**/ assume(term.subtrees.length == 2, s"term does not have exactly 2 subtrees: '${term}'") /**/
      val List(va, body) = term.subtrees
      if (body.root == literal)  // display i ↦ j ↦ __ as i j ↦ __
        tape"${display(va, precedence, Assoc.Left)} ${display(body, precedence, Assoc.Right)}"
      else
        super.format(term)
    }
  }
  
  class GuardOperator(literal: String, precedence: Int, assoc: Assoc=Assoc.None) extends InfixOperator(literal, precedence, assoc) {
    override def format(term: AstSugar.Term) = {
      /**/ assume(term.subtrees.length == 2) /**/
      val op = if (literal == null) display(term.root) else literal
      tape"${display(term.subtrees(0), precedence, Assoc.Left)} ${op |-| new TermTag(term)}{${display(term.subtrees(1))}}"
    }
  }
  
  def O(literal: String, precedence: Int, assoc: Assoc=Assoc.None) =
    new InfixOperator(literal, precedence, assoc)

  import collection.mutable
  
  class OperatorMap[B] extends mutable.HashMap[Any, B] {
    def get(id: Identifier) = super.get(id) match {
      case None => super.get(id.literal)
      case some => some
    }
    
    def apply(id: Identifier) = get(id) getOrElse default(id)
    def contains(id: Identifier) = get(id).isDefined
  }
  
  object OperatorMap {
    def empty[B] = new OperatorMap[B]
  }
  
  def M(ops: InfixOperator*) = OperatorMap.empty[Notation] ++= (ops map (x => (x.literal, x)))

  val INFIX = M(O("->", 5, Assoc.Right), O("<->", 5), O("∧", 5, Assoc.Left), O("∨", 5, Assoc.Left), O("<", 5), O("=", 5),
    O(":", 5, Assoc.Right), O("::", 5), O("/", 7, Assoc.Both), O("|_", 5), O("∩", 5), O("×", 5),
    O("+", 5, Assoc.Left), O("-", 5, Assoc.Left), O("⨁", 5), O("⨀", 5)) ++=
    Map("@" -> new AppOperator("", 2, Assoc.Left),
        AstSugar.↦ -> new AbsOperator("↦", 10, Assoc.Right),
        "|!" -> new GuardOperator("|_", 5))
  val QUANTIFIERS = Set("forall", "∀", "exists", "∃")

  class TermTag(val term: Term) extends AnyVal

  def display(symbol: Identifier): TapeString =
    symbol.literal.toString //|-| symbol

  def display(term: AstSugar.Term): TapeString =
    if ((QUANTIFIERS contains term.root.toString) && !term.isLeaf)
      displayQuantifier(term.unfold)
    else if (term =~ (":", 2) && term.subtrees(0) =~ ("let", 0) && term.subtrees(1) =~ ("@", 2) && term.subtrees(1).subtrees(0) =~ ("↦", 2))
      tape"let ${display(term.subtrees(1).subtrees(0).subtrees(0))} := ${display(term.subtrees(1).subtrees(1))} in ${display(term.subtrees(1).subtrees(0).subtrees(1))}"
    else if (term =~ (":", 2) && term.subtrees(0) =~ ("...", 0))
      display(term.subtrees(0))  // hidden term
    else
      (if (term.subtrees.length == 2) INFIX get term.root else None)
      match {
        case Some(op) =>
          op.format(term)
        case None =>
          if (term.isLeaf) display(term.root) |-| new TermTag(term)
          else tape"${display(term.root)}(${term.subtrees map display mkTapeString ", "})"
      }

  def display(term: AstSugar.Term, pre: Int, side: Assoc): TapeString = {
    val d = display(term)
    getNotation(term) match {
      case Some(op) =>
        if (op.precedence < pre || op.precedence == pre && (side == op.assoc || op.assoc == Assoc.Both)) d else tape"($d)"
      case _ => d
    }
  }

  def displayQuantifier(term: AstSugar.Term) =
    tape"${display(term.root)}${term.subtrees dropRight 1 map display mkTapeString " "} (${display(term.subtrees.last)})"

  def getNotation(term: AstSugar.Term) = {
    LambdaCalculus.isApp(term) match {
      case Some((f, _)) if f.isLeaf => 
        (Seq(f.root, term.root) flatMap (INFIX get _)).headOption
      case _ => INFIX get term.root
    }
  }
  
  // Perhaps this should not be here
  def fromJson(json: DBObject)(implicit container: SerializationContainer): Term = {
    def term(any: AnyRef) = fromJson(any.asInstanceOf[DBObject])
    import scala.collection.JavaConversions._
    val root = Identifier.fromJson(json.get("root") andThen (_.asInstanceOf[DBObject], { throw new SerializationError("'root' missing", json) }))
    val subs = json.get("subtrees") andThen (_.asInstanceOf[BasicDBList].toList map term, List())
    val tree = new Term(root, subs)
    json.get("type") andThen (typ => TypedTerm(tree, term(typ)), tree)
  }
}

