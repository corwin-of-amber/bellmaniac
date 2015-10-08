package semantics

import scala.collection.JavaConversions._
import syntax.Tree
import syntax.Identifier
import scala.collection.immutable.HashMap
import syntax.Unify
import syntax.Resolve
import syntax.Unify.CannotUnify
import semantics.Scope.TypingException
import report.console.NestedListTextFormat
import java.util.logging.Logger
import java.util.logging.Level


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
  import TypedTerm.typeOf

  
  /**
   * Demotes type variables to regular variables and variables to predicates
   * (for use inside a type term when unifying)
   */
  def mark(tpe: Term) =
    tpe map (id => id.kind match {
      case "type variable" => new Identifier(id.literal, "variable", id.ns)
      case "variable" => new Identifier(id.literal, "predicate", id.ns)
      case _ => id
    })
  
  /**
   * Reverses the effect of "mark".
   */
  def unmark(tpe: Term) =
    tpe map (id => id.kind match {
      case "variable" => new Identifier(id.literal, "type variable", id.ns)
      case "predicate" => new Identifier(id.literal, "variable", id.ns)
      case _ => id
    })

  class AbsTypeUid extends Uid
  var c = 0;
  def $v = new Identifier("'" + { c += 1 ; c }, "variable", new AbsTypeUid)

  def abstype(tpe: Term) = {
      val a = tpe map (id => if (id.kind == "set") $v else id)
      (a, Unify.mgu(tpe, a)(Resolve.NULL))
  }
    
  def abstypes(types: Map[Identifier, Term]) = {
    val abstypes = types map { case (k,v) => (k, abstype(v)) }
    (abstypes map { case (k,v) => (k, v._1) }) ++ (abstypes.values flatMap (_._2)) toMap
  }

  /**
   * Unifies the proposed type terms with "meet" in order to
   * try to force lower (more restrictive) types on the components.
   */
  def reinforce(types: List[Term])(meet: Resolve) = {
    val root = $v
    val abstypes = types map abstype map { case (a, m) => (a, m + (root -> a)) }
    val u = new Unify()(meet)
    abstypes foreach (u digest _._2)
    abstypes map (u canonicalize _._1)
  }

  object LatticeOps {
    def ⊓(types: Term*)(implicit scope: Scope) = {
      val dual = new TypeInference.DualResolve(scope)
      TypeInference.reinforce(types toList)(dual.meet)(0)
      // - ⊓ is not symmetric?!
    }
  }
    
  val POLYMORPHIC = {
    import Prelude.{min,cons,nil,N,B}
    def ? = T($v)
    def __[A](gen: => A) = (() => gen)
    Map(min ~>  __ { val b = ?; (? -> b) -> b },                    // min :: ('a -> 'b) -> 'b
        cons ~> __ { val b = ?; b -> ((N -> b) -> (N -> b)) },      // cons :: 'b -> (N -> 'b) -> N -> 'b
        nil ~>  __ { ? -> ? },                                      // nil :: 'a -> 'b
        V("=") -> __ { val a = ?; a -> (a -> B) },                  // = :: 'a -> 'a ->
        V("+") -> __ { val a = ?; a ->: a ->: a },                  // + :: 'a -> 'a -> 'a
        V("-") -> __ { val a = ?; a ->: a ->: a },                  // - :: 'a -> 'a -> 'a
        I(0) -> __ { ? },
        I(1) -> __ { ? }
     )
  }
  
  /**
   * Provides a conservative type assignment to be used as a starting
   * point.
   */  
  class CoarseGrained(resolve: ResolveLattice) {
    
    val ns = new Namespace[Id[Tree[Identifier]]]
    val scope = resolve.asInstanceOf[DualResolve].scope   // @@@ TODO oh terrible!!
    def raw(x: Term) = TypePrimitives.rawtype(scope, x)
    
    def infer(expr: Tree[Identifier], vassign: Map[Identifier, Tree[Identifier]]=Map()) = {
      val (rootvar, assign) = infer0(expr)
      implicit val join = resolve.join
      // - unify all the information you have (@@@ this is so messy)
      val u = new Unify
      u digest (vassign map { case (k,v) => (k, mark(raw(v))) })
      u digest (expr.nodes collect { n => typeOf(n) match { case Some(typ) => (NV(n) -> mark(raw(typ))) }} toMap)
      u digest assign
      // - canonicalize result
      (rootvar, u.canonicalize filter (_._1.ns match { case _:AbsTypeUid=>false case _=>true }))
    }
    
    import Prelude.B

    def infer0(expr: Tree[Identifier]): (Identifier, Map[Identifier, Tree[Identifier]]) = {
      val freshvar = new Identifier(ns.declare(expr), "variable", ns)
      implicit val resolve = Resolve.NULL;
      if (expr.isLeaf) {
        (freshvar, Map(
          POLYMORPHIC get expr.root match {
            case Some(gen) => freshvar -> gen()
            case _ => expr.root -> new Tree(freshvar)
          }))
      }
      else if (expr.root == "program") {
        val children = for (s <- expr.subtrees) yield infer0(s)._2
        //implicit val join = resolve.join;
        if (log.isLoggable(Level.INFO))
          for (c <- children) println(" ; " + c)
        val mgu = children reduce ((x, y) => Unify.mgu0(x,y))
        (freshvar, mgu)
      }
      else if (expr.root == "@") {
        val children = expr.subtrees map infer0
        /**/ assume(children.length == 2) /**/
        val (f, a) = (children get 0, children get 1)
        val t1 = a._1; val t2 = freshvar
        val beta = Map(f._1 -> TI("->")(T(t1), T(t2)))
        //implicit val meet = resolve.meet;
        val mgu = List(beta) ++ (children map (_._2)) reduce ((x, y) => Unify.mgu0(x,y))
        (t2, mgu)
      }
      else if (expr.root == "↦") {
        val children = expr.subtrees map infer0
        /**/ assume(children.length == 2) /**/
        val List(v, e) = children
        val t1 = v._1; val t2 = e._1
        val abs = Map(freshvar -> TI("->")(T(t1), T(t2)))
        //implicit val meet = resolve.meet;
        val mgu = List(abs) ++ (children map (_._2)) reduce ((x, y) => Unify.mgu0(x,y))
        (freshvar, mgu)
      }
      else if (expr.root == "::") {
        /**/ assume(expr.subtrees.length == 2) /**/
        val (va, tpe) = (infer0(expr.subtrees(0)), mark(TypePrimitives.shape(expr.subtrees(1))(scope)))
        //implicit val meet = resolve.meet;
        (freshvar, Unify.mgu0(Map(freshvar -> T(va._1), va._1 -> tpe), va._2))
        // TODO perhaps abstype() is no longer needed here?
        /*
        val (atpe, acomponents) = abstype(tpe)
        val (btpe, bcomponents) = abstype(tpe) // allow a gap for fine-grained later to fill
        implicit val meet = resolve.meet;
        (freshvar, Unify.mgu0(va._2, Map(va._1 -> atpe, freshvar -> btpe) ++ acomponents ++ bcomponents))
        */
      }
      else if (expr.root == ":") {
        /**/ assume(expr.subtrees.length == 2) /**/
        val (lbl, va) = (expr.subtrees(0), infer0(expr.subtrees(1)))
        if (!lbl.isLeaf) throw new Exception(s"invalid label '$lbl'")
        //implicit val meet = resolve.meet;
        (va._1, Unify.mgu0(va._2, Map(freshvar -> T(va._1), lbl.root -> T(va._1))))
      }
      else if (expr.root == "/") {
        /**/ assume(expr.subtrees.length == 2) /**/
        val (br1, br2) = (infer0(expr.subtrees(0)), infer0(expr.subtrees(1)))
        //implicit val join = resolve.join;
        (freshvar, Unify.mgu0(br1._2 + (freshvar -> T(br1._1)), br2._2 + (freshvar -> T(br2._1))))        
      }
      else if (expr.root == "|!") {
        /**/ assume(expr.subtrees.length == 2) /**/
        val va = infer0(expr.subtrees(0))  /* ignore condition for now */
        (freshvar, va._2 + (freshvar -> T(va._1)))
      }
      else if (expr.root == "fix") {
        /**/ assume(expr.subtrees.length == 1) /**/
        val f = infer0(expr.subtrees(0))
        //implicit val join = resolve.join;
        (freshvar, Unify.mgu0(f._2, Map(f._1 -> TI("->")(T(freshvar), T(freshvar)))))
      }
      else if (expr.root == "ω") {
        /**/ assume(expr.subtrees.length == 1) /**/
        val f = infer0(expr.subtrees(0))
        val domainvar = new Identifier(ns.fresh, "variable", ns)
        //implicit val join = resolve.join;
        (freshvar, Unify.mgu0(f._2, Map(freshvar -> T(f._1), f._1 -> TI("->")(T(domainvar), T(domainvar)))))
      }
      else if (expr.root == "=") {
        val tp = $v
        val children = expr.subtrees map infer0 map { case (x,y) => y + (tp -> T(x)) }
        //implicit val join = resolve.join;
        val mgu = (Map(freshvar -> B) +: children) reduce ((x, y) => Unify.mgu0(x,y))
        (freshvar, mgu)
      }
      else if (expr.root == "∀") {
        val children = expr.subtrees map infer0
        /**/ assume(expr.subtrees.length >= 1) /**/
        //implicit val join = resolve.join
        val mgu = (Map(freshvar -> B, children.last._1 -> B) +: (children map (_._2))) reduce ((x, y) => Unify.mgu0(x,y))
        (freshvar, mgu)
      }
      else if (expr.root == "<->" || expr.root == "~" || expr.root == "|" || expr.root == "&" || expr.root == "->") {
        val children = expr.subtrees map infer0 map { case (x,y) => y + (x -> B) }
        //implicit val join = resolve.join
        val mgu = (Map(freshvar -> B) +: children) reduce ((x, y) => Unify.mgu0(x,y))
        (freshvar, mgu)
      }
      else if (expr.root == "↓") {
        val children = expr.subtrees map infer0 map (_._2)
        //implicit val join = resolve.join
        val mgu = (Map(freshvar -> B) +: children) reduce ((x, y) => Unify.mgu0(x,y))
        (freshvar, mgu)
      }
      else if (expr.root.kind == "set") {
        /**/ assume(expr.subtrees.length == 1) /**/
        (freshvar, Map(freshvar -> B) ++ infer0(expr.subtrees(0))._2)
      }
      else if (expr.root == "<" && !expr.isLeaf)  { /* mighty hack */ (freshvar, Map(freshvar ->B)) }
      else
        throw new Exception(s"don't quite know what to do with '${expr.root}'  (in $expr)")
    }
    
    def NV(index: Int) = new Identifier(index, "variable", ns)
    def NV(term: Term): Identifier = NV(ns.declare(term))
  }
  
  /**
   * Improves a coarse assignment of types to tree nodes by detecting slack
   * and removing it.
   */
  class FineGrained(val ns: Namespace[Id[Term]], var assign: Map[Identifier,Term])(scope: Scope, resolve: ResolveLattice) {

    def improve(t: Term) = {
      whileMutate (() => assign) {
        for (n <- t.nodes)
          improve0(n)
      }
      assign
    }
    
    def canonicalize(typ: Term) = {
      val u = new Unify()(Resolve.NULL)
      u.digest(assign)
      unmark( u canonicalize mark(typ) )
    }
    
    private def improve0(n: Term) {
      if (n.root == "program") {
        for (stmt <- n.subtrees)
          if (stmt =~ ("::", 2)) improveDecl(stmt)
      }
      else if (n =~ ("::", 2)) {
        List(n, n.subtrees(0)) map nodeType match {
          case List(Some(tpe), Some(va)) =>
            val spec = canonicalize(n.subtrees(1))
            if (tpe != va || tpe != spec) {
              val force = step1(n, tpe, va, spec)
              for (k <- List(n, n.subtrees(0)))
                retype(k, force)
            }
          case _ =>
        }
      }
      else if (n =~ (":", 2)) {
        List(n, n.subtrees(1)) map nodeType match {
          case List(Some(parent), Some(child)) =>
            if (parent != child) {
              val force = step1(n, parent, child)
              for (k <- List(n, n.subtrees(1)))
                retype(k, force)
            }
        }
      }
      else if (n =~ ("@", 2)) {
        List(n) ++ n.subtrees map nodeType match {
          case List(Some(y), Some(f), Some(x)) =>
            if (f != (x -> y)) {
              val (farg, fret) = TypePrimitives.curry(f)(scope)
              val arg = TypePrimitives.intersection(scope, List(x, farg))
              val ret = TypePrimitives.intersection(scope, List(y, fret))
              val xy = TypePrimitives.intersection(scope, List(f, x -> y))
              if (log.isLoggable(Level.INFO)) {
                println(s"|- $n")
                println(s"   :: ${y toPretty}  ∩  ${fret toPretty}  =>  ${ret toPretty}")
                println(s"   ${n.subtrees(0)} :: ${f toPretty}  ∩  ${(x -> y) toPretty}  =>  ${xy toPretty}")
                println(s"   ${n.subtrees(1)} :: ${x toPretty}  ∩  ${farg toPretty}  =>  ${arg toPretty}")
              }
              retype(n, ret)
              retype(n.subtrees(0), xy)
              retype(n.subtrees(1), arg)
            }
          case _ =>
        }
      }
      else if (n =~ ("↦", 2)) {
        List(n) ++ n.subtrees map nodeType match {
          case List(Some(f), Some(x), Some(y)) =>
            if (f != (x -> y)) {
              val (farg, fret) = TypePrimitives.curry(f)(scope)
              val arg = TypePrimitives.intersection(scope, List(x, farg))
              val ret = TypePrimitives.intersection(scope, List(y, fret))
              val xy = TypePrimitives.intersection(scope, List(f, x -> y))
              if (log.isLoggable(Level.INFO)) {
                println(s"|- $n")
                println(s"   :: ${f toPretty}  ∩  ${(x -> y) toPretty}  =>  ${xy toPretty}")
                println(s"   ${n.subtrees(0)} :: ${x toPretty}  ∩  ${farg toPretty}  =>  ${arg toPretty}")
                println(s"   ${n.subtrees(1)} :: ${y toPretty}  ∩  ${fret toPretty}  =>  ${ret toPretty}")
              }
              retype(n.subtrees(0), arg)
              retype(n.subtrees(1), ret)
              retype(n, xy)
            }
          case _ =>
        }
        val arg = n.subtrees(0)
        improveDecl(arg)
      }
      else if (n =~ ("/", 2)) {
        n +: n.subtrees map nodeType match {
          case List(Some(tpe), Some(ltpe), Some(rtpe)) =>
            if (tpe != ltpe || tpe != rtpe) {
              val join = TypePrimitives.union(scope, List(ltpe, rtpe))
              if (join != tpe) {
                retype(n, step1(n, tpe, join))
                retype(n.subtrees(0), step1(n.subtrees(0), ltpe, tpe))
                retype(n.subtrees(1), step1(n.subtrees(1), rtpe, tpe))
              }
            }
          case _ =>
        }
      }
      else if (n =~ ("ω", 1)) {
        n +: n.subtrees map nodeType match {
          case List(Some(ωtyp), Some(ftyp)) =>
            //val (ωarg, ωret) = TypePrimitives.curry(ωtyp)(scope)
            //val (farg, fret) = TypePrimitives.curry(ftyp)(scope)
            if (ωtyp != ftyp) {
              val force = step1(n, ωtyp, ftyp)
              retype(n, force); // but not n.subtrees(0)
            }
          case _ =>
        }
      }
      else if (n.isLeaf) {
        (nodeType(n), assign get n.root) match { 
          case (Some(refType), Some(varType)) =>
            if (refType != varType) {
              val force = step1(n, refType, varType)
              retype(n, force)
            }
          case _ =>
        }
      }
    }
    
    def improveDecl(decl: Term) {
      (nodeType(decl), TypedLambdaCalculus.getDeclaredVariable(decl)) match {
        case (Some(declType), Some(id)) => assign get id match {
          case Some(varType) =>
            if (declType != varType) {
              val typ = step1(decl, declType, varType)
              retype(decl, typ)
              retype(id, typ)
            }
          case _ => 
        }
        case _ =>
      }
    }

    def NV(index: Int) = new Identifier(index, "variable", ns)
    
    def nodeType(t: Term) = ns lookup t match {
      case Some(index) => assign get NV(index)
      case None => None
    }
    
    def retype(t: Term, newType: Term) {
      retype(NV(ns declare t), newType)
    }
    
    def retype(id: Identifier, newType: Term) {
      if ((assign get id) != Some(newType))
        assign += (id -> newType)
    }
    
    /**
     * Calls reinforce with "meet" and prints the results nicely
     */
    private def step0(node: Term, terms: Term*) = {
      /**/ assume(!terms.isEmpty) /**/
      val force = reinforce(terms.toList)(resolve.meet)
      /**/ assert(force.length == terms.length) /**/
      if (log.isLoggable(Level.INFO)) _printNicely(node, terms, force)
      force
    }
    
    private def step1(node: Term, types: Term*) = {
      /**/ assume(!types.isEmpty) /**/
      try {
        val least = TypePrimitives.intersection(scope, types toList)
        if (log.isLoggable(Level.INFO)) _printNicely(node, types, List(least))
        least
        }
      catch { 
        case x: Scope.TypingException => throw x.at(node)
      }
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
      if (term.root == "∩")
        List(term.subtrees(0))
      else if (term.root == "->" && term.subtrees.length == 2 && term.subtrees(0).root == "∩") {
        val args = term.subtrees(0).subtrees
        val cross = args filter (isTupleType _)
        val approx = for (c <- cross) yield TI("->", List(c, term.subtrees(1)))
        approx ++ (approx flatMap (alternatives _))
      }
      else if (term.root == "->" && term.subtrees.length == 2 && term.subtrees(0).root == "×") {
        val args = term.subtrees(0).subtrees
        var curry = TI("->", List(args(0), TI("->", List(args(1), term.subtrees(1)))))
        List(curry) ++ alternatives(curry)
      }
      else List()
    }
    
    override def isUnitary(term: Tree[Identifier]) = !isTupleType(term)
    
    def isTupleType(term: Tree[Identifier]): Boolean =
      term.root == "×" || (term.root == "∩" && (term.subtrees exists (isTupleType _)))
  }
  
 
  class DualResolve(val scope: Scope) extends ResolveLattice {
    
    def this() = this(new Scope)
    
    override val join = new ResolveBase {
      override def conflict(x:Tree[Identifier], y:Tree[Identifier], keys: List[Identifier]): Option[Map[Identifier, Tree[Identifier]]] = {
        if (x.isLeaf && y.isLeaf && (scope.sorts contains x.root) && (scope.sorts contains y.root)) {
          val join = scope.sorts.join(x.root, y.root)
          if (join == Domains.⊤) None
          else Some(keys map (_ -> T(join)) toMap)
        }
        else None
      }
    }
      
    override val meet = new ResolveBase {
      override def conflict(x:Tree[Identifier], y:Tree[Identifier], keys: List[Identifier]): Option[Map[Identifier, Tree[Identifier]]] = {
        if (x.isLeaf && y.isLeaf && (scope.sorts contains x.root) && (scope.sorts contains y.root)) {
          val meet = scope.sorts.meet(x.root, y.root)
          Some(keys map (_ -> T(meet)) toMap)
        }
        else None
      }
    }
    
  }
  
  
  class ConservativeResolve(scope: Scope) extends DualResolve(scope: Scope) {
    def this() = this(new Scope)
    override val meet = join
  }
  
  /**
   * Combines coarse-grained and fine-grained type inference.
   * @deprecated
   */
  def infer(scope: Scope, term: Term, vassign: Map[Identifier, Tree[Identifier]]) = {
    val conservative = new ConservativeResolve(scope)
    val dual = new DualResolve(scope)
    log.info("-- coarse --")
    val coarse = new CoarseGrained(conservative)
    val (rootvar, assign) = coarse.infer(term, vassign)
    // val tassign = { for ((k,v) <- coarse.ns; tpe <- assign get coarse.NV(k)) yield (v, tpe) } .toMap
    // synth.tactics.Rewrite.display(annotate(term, tassign))(new TypeTranslation.Environment(scope, Map()))
    val tassign0 = (term.nodes collect { n => typeOf(n) match { case Some(typ) => (coarse.NV(n) -> typ) }} toMap)
    log.info("-- fine --")
    val fine = new FineGrained(coarse.ns, assign ++ tassign0 ++ vassign)(scope, dual)
    val reassign = fine.improve(term)
    (reassign filter ((kv) => kv._1.ns ne coarse.ns), 
        { for ((k,v) <- coarse.ns; tpe <- reassign get fine.NV(k)) yield (v, tpe) } .toMap
    )
  }
  
  /**
   * Combines coarse-grained and fine-grained type inference.
   */
  def infer(term: Term, preassign: Map[Identifier, Tree[Identifier]]=Map())(implicit scope: Scope): (Map[Identifier, Term], Term) = {
    val (vassign, tassign) = infer(scope, term, preassign)
    val typed = annotate(term, tassign)
    if (log.isLoggable(Level.INFO))
      synth.tactics.Rewrite.display(typed)(new TypeTranslation.Environment(scope, Map()))
    (vassign, typed)
  }
  
  def annotate(term: Term, tassign: Map[Id[Term], Term]): Term = {
    if (term =~ ("::", 2))
      annotate(term.subtrees(0), tassign)
    else {
      val clon = T(term.root, term.subtrees map (annotate(_, tassign)))
      tassign get term match {
        case Some(typ) => TypedTerm(clon, typ)
        case _ => term match {
          case typed: TypedTerm => TypedTerm(clon, typed.typ)
          case _ => clon
        }
      }
    }
  }
  
  val log = Logger.getLogger("TypeInference")
  log.setLevel(Level.OFF)
    
  
  def main(args: Array[String]): Unit = {

    import examples.Paren
      
    import Binding.{prebind,inline}
    
    val program = inline(prebind(Paren.tree))
    
    val conservative = new ConservativeResolve(Paren.scope)
    val dual = new DualResolve(Paren.scope)
    
    val coarse = new CoarseGrained(conservative)

    val (rootvar, assign) = coarse.infer(program)
    
    //println(assign)
    //println(ns)
    
    println("-" * 80)

    val scope = Paren.scope
    
    println(scope.sorts.hierarchy)
    
    for ((k,v) <- assign)
      (k.kind, k.literal) match {
      case ("variable", x:String) =>
        println(s"$k :: $v")// +
          //s"     <: ${TypeTranslation.decl(scope, k, v).toPretty}")
      case _ =>
    }
    
    val fine = new FineGrained(coarse.ns, assign)(scope, dual)
    val reassign = fine.improve(program)

    println("-" * 80)
    
    for ((k,v) <- reassign)
      (k.kind, k.literal) match {
      case ("variable", x:String) =>
        println(s"$k :: $v")
      case _ =>
    }
    
    val format = new NestedListTextFormat[Identifier]()()
    format.layOutAndAnnotate(program, 
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