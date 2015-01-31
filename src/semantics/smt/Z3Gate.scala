
package semantics.smt

import scala.collection.mutable.HashMap
import com.microsoft.z3.Expr
import com.microsoft.z3.Sort
import syntax.Identifier
import syntax.AstSugar
import com.microsoft.z3.FuncDecl
import semantics.TypeTranslation.TypedIdentifier
import semantics.TypeTranslation.TypedIdentifier
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.Z3Exception



class Z3Gate {
  
  import AstSugar._
  import Z3Sugar._
  
  val declarations = new HashMap[Identifier, FuncDecl]
  val sorts = new HashMap[Identifier, Sort]
  
  val mnemonics = new HashMap[String, Identifier]
  
  /* some built-in declarations */
  sorts += (S("R") -> ctx.getRealSort)
  sorts += (S("") -> ctx.getBoolSort)
  
  // -----------------
  // Declarations part
  // -----------------
  
  def getSort(sort: Identifier) = sorts getOrElse (sort, {
    val newSort = ctx mkUninterpretedSort sort.toString
    sorts += (sort -> newSort)
    newSort
  })
  
  def getSorts(typ: Term): List[Sort] =
    if (typ.isLeaf) List(getSort(typ.root))
    else if (typ.root == "->") {
      val sorts = typ.unfold.subtrees
      if (sorts forall (_.isLeaf)) sorts map (x => getSort(x.root))
      else throw new SmtNotFirstOrder(s"not first-order: type '${typ.toPretty}'")
    }
    else throw new SmtException(s"cannot handle type '${typ.toPretty}'")
  
  def declare(symbol: TypedIdentifier): FuncDecl = declare(symbol.untype, symbol.typ)
  
  def declare(symbol: Identifier, typ: Term) = declarations get symbol match {
    case Some(decl) => 
      val existingType = typeOf(decl)
      if (existingType == typ) decl
      else
        throw new SmtException(s"multiply declared symbol '$symbol' " +
          s"(conflicting types: ${existingType.toPretty}  ~  ${typ.toPretty})")
    case _ => 
      val decl = func (mne(symbol) :-> (getSorts(typ):_*))
      declarations += symbol -> decl
      decl
  }
  
  def typeOf(f: FuncDecl): Term =
    TI("->", f.getDomain.toList map typeOf)(typeOf(f.getRange)).foldRight
  
  
  def typeOf(sort: Sort): Term = sorts find (_._2 == sort) match {
    case Some((k,_)) => T(k)
    case _ => T(S(sort.toString))
  }
  
  /**
   * Gets a string mnemonic for this identifier; makes sure distinct
   * identifiers get distinct mnemonics (even if they have the same
   * literal).
   */
  def mne(id: Identifier) = mnemonics find (_._2 == id) match {
    case Some(x) => x._1
    case _ =>
      val lit = id.literal.toString
      val newMne = (lit #:: (nat map (lit + _))) find (! mnemonics.contains(_))
      mnemonics += newMne.get -> id
      newMne.get
  }

  /**
   * just the stream of naturals (taken from Scala docs)
   */
  def nat = { 
    def loop(v: Int): Stream[Int] = v #:: loop(v + 1)
    loop(0)
  }

  // ---------------
  // Assertions part
  // ---------------

  def expression(expr: Term): Expr = {
    val r = expr.root
    val arity = expr.subtrees.length
    def recurse = expr.subtrees map expression
    if (r == "forall" || r == "∀") {
      val (vas :+ body) = expr.unfoldRight.subtrees
      fork {
        val vas_decl = vas map quantifiedVar 
        forall(vas_decl:_*)(expression(body))
      }
    }
    else if ((r == "->" || r == "→") && arity == 2) {
      val List(l, r) = recurse
      l -> r
    }
    else if (r == "&" || r == "∧") 
      conjunction(recurse:_*) 
    else if (r == "|" || r == "∨") 
      disjunction(recurse:_*)
    else if ((r == "<->" || r == "↔︎") && arity == 2) {
      val List(l, r) = recurse
      l <-> r
    }
    else if ((r == "~" || r == "¬") && arity == 1)
      ~(recurse(0))
    else if ((r == "=") && arity == 2) {
      val List(l, r) = recurse
      l =:= r
    }
    else {
      declarations get r match {
        case Some(decl) => decl(recurse:_*)
        case _ => r match {
          case rt: TypedIdentifier => declare(rt)(recurse:_*)
          case _=> throw new SmtException(s"undeclared '$r' ($arity-ary)")
        }
      }
    }
  }
  
  def formula(term: Term) = try !! ( expression(term) )
    catch { 
      case x: SmtException => throw x.at(term)
      case z: Z3Exception => throw new SmtException(z.toString()).at(term)
    }
  
  def quantifiedVar(va: Term) = {
      if (va.isLeaf)
        declare(va.root.asInstanceOf[TypedIdentifier])() 
      else throw new SmtException(s"not a valid variable: '${va.toPretty}'")
  }
  
  def fork[R](op: => R) = {
    val checkpoint = (declarations.clone, mnemonics.clone)
    def rollback = { declarations.clear ; declarations ++= checkpoint._1
                     mnemonics.clear ; mnemonics ++= checkpoint._2 }
    try op
    finally rollback
  }
  
  def solveAndPrint(assumptions: List[BoolExpr], goals: List[BoolExpr]) =
    Z3Sugar.solveAndPrint(assumptions, goals)
  
  def solve(assumptions: List[BoolExpr], goals: List[BoolExpr], verbose: Boolean=false) =
    if (verbose)
      Z3Sugar.solveAndPrint(assumptions, goals)
    else      
      Z3Sugar.solve(assumptions, goals)
}


class SmtException(msg: String) extends Exception(msg) { 
  import syntax.AstSugar._
  
  var formula: Term = null;
  def at(formula: Term): SmtException = {
    this.formula = formula; this
  }
  
  override def getMessage = if (formula == null) super.getMessage 
    else s"$msg\n\tin: ${formula.toPretty}"
}
class SmtNotFirstOrder(msg: String) extends SmtException(msg) {}
