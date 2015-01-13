package semantics

import org.deri.iris.compiler.Parser
import org.deri.iris.KnowledgeBaseFactory
import scala.collection.JavaConversions._
import syntax.Tree
import syntax.Identifier
import org.deri.iris.factory.Factory
import org.deri.iris.storage.IRelation
import scala.collection.immutable.HashMap
import syntax.Unify
import syntax.Resolve
import syntax.Unify.CannotUnify
import semantics.Scope.TypingException
import report.console.NestedListTextFormat


class Namespace[Name](cmp: (Name,Name) => Boolean = null) {
  private var _nextFresh = 0;
  private var _nameToIndex = new scala.collection.mutable.HashMap[Name, Int];
  private var _indexToName = new scala.collection.mutable.HashMap[Int, Name];
  
  def get(index : Int) = _indexToName get index
  def lookup(name : Name) = _nameToIndex get name
  
  def declare(name : Name) = {
    lookup(name) match {
      case Some(index) => index
      case None =>
        val gen = fresh
        _nameToIndex(name) = gen
        _indexToName(gen) = name
        gen
    }
    
  }
  
  def fresh() = {
    _nextFresh += 1
    _nextFresh
  }
  
  def foreach(op: ((Int, Name)) => Unit) =
    _indexToName foreach op
   
  def filter(pred: ((Int, Name)) => Boolean) =
    _indexToName filter pred
  
  override def toString = _indexToName.toString 
}


trait ResolveLattice {
  val join: Resolve = Resolve.NULL;
  val meet: Resolve = Resolve.NULL;
}

object TypeInference {

  import syntax.AstSugar._


  val TREE_PRED = new Identifier("T")
  
  def tree2Tuples(t : Tree[Identifier], ns : Namespace[Identifier]) : (Identifier, List[List[Identifier]]) = {
    if (t.subtrees.isEmpty) (t.root, List())
      //(new Identifier(ns declare t.root, "index"), List())
    else {
      val rootId = new Identifier(ns fresh, "index")
      val children = t.subtrees map (x => tree2Tuples(x, ns))
      val subTuples = (children map (_._2)).flatten
      val subIds = children map (_._1)
      val rootTuple = rootId :: t.root :: subIds
      (rootId, rootTuple +: subTuples)
    }
  }
  
  def tree2Facts(t : Tree[Identifier], ns : Namespace[Identifier]) = {
    val (_, tuples) = tree2Tuples (t, ns)
    tuples map (tup => new Tree(TREE_PRED, tup map (x => new Tree(x))))
  }
  
  def tuples2Tree(tuples: IRelation, rootIndex: Int) = {
    val sz = tuples.size
    for (i <- 0 until sz) {
      
    }
  }
  
  def asDatalog(i : Identifier) = i.literal match {
    case index: Int => i.toString
    case _ => s"'$i'"
  }
    
  
  def asDatalog(t : Tree[Identifier]): String = {
    if (t.subtrees isEmpty) asDatalog(t.root)
    else {
      val children = t.subtrees map asDatalog mkString ", " 
      s"${t.root}($children)"
    }
  }
  
  /**
   * Provides a conservative type assignment to be used as a starting
   * point.
   */  
  class CoarseGrained(resolve: ResolveLattice) {
    
    val ns = new Namespace[Id[Tree[Identifier]]]
    
    def infer(expr: Tree[Identifier]): (Identifier, Map[Identifier, Tree[Identifier]]) = {
      val freshvar = new Identifier(ns.declare(expr), "variable")
      if (expr.isLeaf) {
        (freshvar, Map(expr.root -> new Tree(freshvar)))
      }
      else if (expr.root == "program") {
        val children = for (s <- expr.subtrees) yield infer(s)._2
        implicit val join = resolve.join;
        for (c <- children) println(" ; " + c)
        val mgu = children reduce ((x, y) => Unify.mgu(x,y))
        (freshvar, mgu)
      }
      else if (expr.root == "@") {
        val children = for (s <- expr.subtrees) yield infer(s)
        /**/ assume(children.length == 2) /**/
        val (f, a) = (children get 0, children get 1)
        val t1 = a._1; val t2 = freshvar
        val beta = Map(f._1 -> TI("->")(T(t1), T(t2)))
        implicit val meet = resolve.meet;
        val mgu = List(beta) ++ (children map (_._2)) reduce ((x, y) => Unify.mgu(x,y))
        (t2, mgu)
      }
      else if (expr.root == "↦") {
        val children = for (s <- expr.subtrees) yield infer(s)
        /**/ assume(children.length == 2) /**/
        val List(v, e) = children
        val t1 = v._1; val t2 = e._1
        val abs = Map(freshvar -> TI("->")(T(t1), T(t2)))
        implicit val meet = resolve.meet;
        val mgu = List(abs) ++ (children map (_._2)) reduce ((x, y) => Unify.mgu(x,y))
        (freshvar, mgu)
      }
      else if (expr.root == "::") {
        /**/ assume(expr.subtrees.length == 2) /**/
        val (va, tpe) = (infer(expr.subtrees(0)), expr.subtrees(1))
        implicit val meet = resolve.meet;
        (freshvar, Unify.mgu(va._2, Map(freshvar -> T(va._1), va._1 -> tpe) + (freshvar -> tpe)))
      }
      else if (expr.root == ":") {
        /**/ assume(expr.subtrees.length == 2) /**/
        val (lbl, va) = (expr.subtrees(0), infer(expr.subtrees(1)))
        if (!lbl.isLeaf) throw new Exception(s"invalid label '$lbl'")
        implicit val meet = resolve.meet;
        (va._1, Unify.mgu(va._2, Map(freshvar -> T(va._1), lbl.root -> T(va._1))))
      }
      else if (expr.root == "min") {
        /**/ assume(expr.subtrees.length == 1) /**/
        val vec = infer(expr.subtrees(0))
        val domainvar = new Identifier(ns.fresh, "variable")
        implicit val meet = resolve.meet;
        (freshvar, Unify.mgu(vec._2, Map(vec._1 -> TI("->")(T(domainvar), T(freshvar)))))
      }
      else
        throw new Exception(s"don't quite know what to do with '${expr.root}'  (in $expr)")
    }
  
  }
  
  /**
   * Improves a coarse assignment of types to tree nodes by detecting slack
   * and removing it.
   */
  class FineGrained(val ns: Namespace[Id[Term]], var assign: Map[Identifier,Term])(resolve: ResolveLattice) {

    def improve(t: Term) = {
      whileMutate (() => assign) {
        for (n <- t.nodes)
          improve0(n)
      }
      assign
    }
    
    private def improve0(n: Term) {
      if (n =~ ("::", 2)) {
        List(n, n.subtrees(0)) map nodeType match {
          case List(Some(tpe), Some(va)) =>
            if (tpe != va) {
              val force = step0(n, tpe, va)
              for ((k,v) <- List(n, n.subtrees(0)) zip force)
                retype(k, v)
            }
        }
      }
      else if (n =~ ("↦", 2)) {
        List(n) ++ n.subtrees map nodeType match {
          case List(Some(f), Some(x), Some(y)) =>
            val xy = TI("->")(x, y)
            if (f != xy) {
              val force = step0(n, f, xy)
              val moreForce = (force dropRight 1) ++ force.last.subtrees
              for ((k,v) <- List(n) ++ n.subtrees zip moreForce)
                retype(k, v)
            }
        }
        val arg = n.subtrees(0)
        (nodeType(arg), getVariable(arg)) match {
          case (Some(declType), Some(id)) => assign get id match {
            case Some(varType) =>
              if (declType != varType) {
                val force = step0(arg, declType, varType)
                retype(arg, force(0))
                retype(id, force(1))
              }
            case _ => 
          }
          case _ =>
        }
      }
      else if (n.isLeaf) {
        (nodeType(n), assign get n.root) match { 
          case (Some(refType), Some(varType)) =>
            if (refType != varType) {
              val force = step0(n, refType, varType)
              retype(n, force(0))
              retype(n.root, force(1))
            }
          case _ =>
        }
      }
    }

    def nodeType(t: Term) = ns lookup t match {
      case Some(index) => assign get V(index)
      case None => None
    }
    
    def retype(t: Term, newType: Term) {
      retype(V(ns declare t), newType)
    }
    
    def retype(id: Identifier, newType: Term) {
      if ((assign get id) != Some(newType)) {
        println(s"  SET! $id -> $newType")
        assign += (id -> newType)
      }
    }
    
    def getVariable(t: Term): Option[Identifier] = {
      if (t.isLeaf) Some(t.root)
      else if (t =~ ("::", 2)) getVariable(t.subtrees(0))
      else None
    }
    
    /**
     * Unifies the proposed type terms with "meet" in order to
     * try to force lower (more restrictive) types.
     */
    def useForce(types: List[Term]) = {
      val root = $v
      val abstypes = types map { t =>
        val a = t map (id => if (id.kind == "set") $v else id)
        (a, Unify.mgu(t, a)(Resolve.NULL) + (root -> a)) 
      }
      val u = new Unify()(resolve.meet)
      abstypes foreach (u digest _._2)
      println(u.canonicalize)
      abstypes map (u canonicalize _._1)
    }
    
    /**
     * Calls useForce and prints the results nicely
     */
    private def step0(node: Term, terms: Term*) = {
      /**/ assume(!terms.isEmpty) /**/
      val force = useForce(terms.toList)
      /**/ assert(force.length == terms.length) /**/
      _printNicely(node, terms, force)
      force
    }
    
    def _printNicely(node: Term, terms: Seq[Term], force: Seq[Term]) {
      println(s"|- $node")
      println(s"   :: ${terms(0).toPretty}") 
      for (t <- terms drop 1)
        println(s"      ${t.toPretty}")
      if (force forall (_==force(0)))
        println(s"      => ${force(0).toPretty}")
      else
        println(s"      => ${force map (_.toPretty)}")
    }
    
    // -------------
    // Mutation part
    // -------------
    
    def whileMutate(getter: () => AnyRef)(op: => Unit) {
      while (checkMutate(getter)(op)) {}
    }
    
    def checkMutate(getter: () => AnyRef)(op:  => Unit) = {
      val pre = getter()
      op
      pre ne getter()
    }
    
  }
  
  

  class ResolveBase extends Resolve {
    
    override def alternatives(term: Tree[Identifier]) = {
      if (term.root == "->" && term.subtrees.length == 2 && term.subtrees(0).root == "∩") {
        val args = term.subtrees(0).subtrees
        val cross = args filter (isTupleType _)
        val approx = for (c <- cross) yield TI("->", List(c, term.subtrees(1)))
        approx ++ (approx flatMap (alternatives _))
      }
      else if (term.root == "->" && term.subtrees.length == 2 && term.subtrees(0).root == "x") {
        val args = term.subtrees(0).subtrees
        var curry = TI("->", List(args(0), TI("->", List(args(1), term.subtrees(1)))))
        List(curry) ++ alternatives(curry)
      }
      else List()
    }
    
    override def isUnitary(term: Tree[Identifier]) = !isTupleType(term)
    
    def isTupleType(term: Tree[Identifier]): Boolean =
      term.root == "x" || (term.root == "∩" && (term.subtrees exists (isTupleType _)))
  }
  
 
  class DualResolve(val scope: Scope) extends ResolveLattice {
    
    def this() = this(new Scope)
    
    override val join = new ResolveBase {
      override def conflict(x:Tree[Identifier], y:Tree[Identifier], key: Identifier): Option[Map[Identifier, Tree[Identifier]]] = {
        if (x.isLeaf && y.isLeaf) (scope.findSortHie(x.root), scope.findSortHie(y.root)) match {
          case (Some(xh), Some(yh)) =>
            if (xh.subtrees exists (_.root == y.root)) {
              if (key == null) Some(Map()) else Some(Map(key -> x))          
            }
            else if (yh.subtrees exists (_.root == x.root)) {
              if (key == null) Some(Map()) else Some(Map(key -> y))
            }
            else None
          case _ => None
        }
        else None
      }
    }
      
    override val meet = new ResolveBase {
      override def conflict(x:Tree[Identifier], y:Tree[Identifier], key: Identifier): Option[Map[Identifier, Tree[Identifier]]] = {
        if (x.isLeaf && y.isLeaf) (scope.findSortHie(x.root), scope.findSortHie(y.root)) match {
          case (Some(xh), Some(yh)) =>
            if (xh.subtrees exists (_.root == y.root)) {
              if (key == null) Some(Map()) else Some(Map(key -> y))          
            }
            else if (yh.subtrees exists (_.root == x.root)) {
              if (key == null) Some(Map()) else Some(Map(key -> x))
            }
            else None
          case _ => None
        }
        else None
      }
    }
    
  }
  
  
  class ConservativeResolve(scope: Scope) extends DualResolve(scope: Scope) {
    def this() = this(new Scope)
    override val meet = join
  }
  
      
  def infer(term: Term)(implicit resolve: ResolveLattice) =
    new CoarseGrained(resolve).infer(term)
  
  def main(args: Array[String]): Unit = {

    import examples.Paren
      
    //val ns = new Namespace[Id[Tree[Identifier]]]
    val conservative = new ConservativeResolve(Paren.scope)
    val dual = new DualResolve(Paren.scope)
    
    val coarse = new CoarseGrained(conservative)

    val (rootvar, assign) = coarse.infer(Paren.tree)
    
    //println(assign)
    //println(ns)
    
    println("-" * 80)

    val scope = Paren.scope
    
    println(scope.sorts)
    
    for ((k,v) <- assign)
      (k.kind, k.literal) match {
      case ("variable", x:String) =>
        println(s"$k :: $v" +
          s"     <: ${TypeTranslation.decl(scope, k, v).toPretty}")
      case _ =>
    }
    
    val fine = new FineGrained(coarse.ns, assign)(dual)
    val reassign = fine.improve(Paren.tree)

    println("-" * 80)
    
    for ((k,v) <- reassign)
      (k.kind, k.literal) match {
      case ("variable", x:String) =>
        println(s"$k :: $v")
      case _ =>
    }
    
    val format = new NestedListTextFormat[Identifier]
    format.layOutAndAnnotate(Paren.tree, 
        ((x) => fine.nodeType(x) map (_.toPretty)), (_.toPretty))
  }
    
    
  /*
      
    val facts = tree2Facts(tree, ns) map asDatalog
    
    val parser = new Parser
    val program = (facts map (_+".") mkString "\n") + """

      ur('J'). ur('R').

      in(?i, ?t) :- T(?t0, '::', ?i, ?t).

      in(?i, ?X)  :- T(?t1, '->', ?X, ?Y), in(?f, ?t1), T(?t2, '@', ?f, ?i), arg_type(?X).
      in(?t2, ?Y) :- T(?t1, '->', ?X, ?Y), in(?f, ?t1), T(?t2, '@', ?f, ?i), arg_type(?X).

      arg_type(?X) :- ur(?X).
      arg_type(?X) :- T(?X, '->', ?Y, ?Z).

      T(?u, '->', ?X, ?YZ) :- T(?u, '->', ?XY, ?Z), T(?XY, 'x', ?X, ?Y), T(?YZ, '->', ?Y, ?Z).
    """
    parser.parse(program)
    
    println("Rules")
    for (rule <- parser.getRules) {
      println(" * " + rule)
    }
    
    println("Facts")
    for (fact <- parser.getFacts) {
      println(" * " + fact)
    }
    
    val config = KnowledgeBaseFactory.getDefaultConfiguration;
    
    val kb = KnowledgeBaseFactory.createKnowledgeBase(parser.getFacts, parser.getRules, config)
    
    val queries = "?-in(?i, ?Z)."

    val queryParser = new Parser
    queryParser parse queries
        
    for (query <- queryParser getQueries)
      println (kb.execute(query))
  * */
  
  
}