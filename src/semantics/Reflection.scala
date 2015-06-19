package semantics

import syntax.AstSugar
import syntax.Identifier
import TypeTranslation.TypedIdentifier
import TypeTranslation.Environment
import TypeTranslation.Declaration
import Scope.TypingException
import AstSugar._
import java.util.logging.Logger
import java.util.logging.Level
import report.console.NestedListTextFormat
import synth.tactics.Rewrite
import com.sun.org.apache.xalan.internal.xsltc.runtime.output.StringOutputBuffer
import java.io.StringWriter
import java.io.ByteArrayOutputStream



object Reflection {
  
  case class Consolidated(term: Term) extends Term(term.root, term.subtrees)
  def isConsolidated(term: Term) = term match {
    case Consolidated(_) | TypedTerm(_, Consolidated(_)) => true
    case _ => false
  }

  def isFuncType(typ: Term) = typ.root == "->"
  def isFunc(v: TypedIdentifier) = isFuncType(v.typ)    
  
  
  val log = Logger.getLogger("semantics.Reflection")
  log.setLevel(Level.OFF)
  
  {  /* I'm not sure this is advised */
    val handler = new java.util.logging.ConsoleHandler
    handler.setLevel(Level.FINER);
    Reflection.log.addHandler(handler);
  }
}



class Reflection(val env: Environment, val typedecl: Map[Identifier, Term]) {

  import TypeTranslation.Declaration
  import TypeTranslation.TypingSugar._
  import Reflection._
  import Prelude.B
  import syntax.Strip.greek
  import TypedTerm.preserve
  
  //-----------------
  // Abstraction Part
  //-----------------
  
  import TypePrimitives.rawtype
  
  def abstype(typ: Term): Term = {
    if (isFuncType(typ)) T(env.scope.declFunctionType(rawtype(env.scope, typ)).faux)
    else typ
  }

  def preserveAbs(term: Term, newterm: Term) = term match {
    case typed: TypedTerm => TypedTerm(newterm, abstype(typed.typ))
    case _ => newterm
  }
  
  def pushTypeDown(term: Term) = if (term.isLeaf) {
    val typ = env.typeOf_!(term)
    TypedTerm(T(TypedIdentifier(term.root, typ)), typ)
  } else term
  
  def isFuncTypeExt(typ: Term) = {
    isFuncType(typ) || (typ.isLeaf && (env.scope.functypes.values exists (_.faux == typ.root)))
  }
    
  def equality(typ: Term) = ∀:(typ, (x,y) => (x =:= y) -> Consolidated(x =:= y))

  def equality: List[Term] = env.scope.functypes.keys map equality toList 

  def equality(used: Set[Identifier]): List[Term] = {
    val usedTypes = used flatMap (env.typeOf(_) map TypePrimitives.ret map (_.leaf))//collect { case x if x.isLeaf => x.root })
    (env.scope.functypes filter { case (k,v) => usedTypes contains v.faux }).keys map equality toList
  }
  
  //---------------
  // Type Info Part
  //---------------
  
  def typeinfo(symbol: TypedIdentifier) =
    T(symbol.untype) =:= T(symbol)
  
  def typeinfo(typedecl: Map[Identifier, Term]) = typedecl map { 
      case (k,v) => TypedTerm(T(k), rawtype(env.scope, v)) =:= T(TypedIdentifier(k, v))
    }
  
  def typeinfo: List[Term] = typeinfo(typedecl) toList
  
  //-------------------
  // Consolidation Part
  //-------------------
  
  object Role extends Enumeration {
    val Definition, Proposition = Value
  }
  
  def consolidate(term: Term)(implicit role: Role.Value) = consolidate1(term)
  
  def consolidate1(term: Term)(implicit role: Role.Value): Term = {
    if (isConsolidated(term)) term
    else preserve(term, consolidate0(term))
  }
  
  def consolidate0(term: Term)(implicit role: Role.Value): Term = {
    def sub = term.subtrees map consolidate1
    if (term =~ ("@", 2)) {
      val List(fun, arg) = sub
      if (currying contains fun.root) pushTypeDown(fun)(arg)
      else if (fun.root == "/") {    /* distribute '@' over '/' */
        consolidate1(T(fun.root, fun.subtrees map (_ :@ arg)))
      }
      else if (fun =~ ("↦", 2)) {    /* beta reduction */
        consolidate1(TypedLambdaCalculus.beta(fun, arg))
      }
      else throw new Exception(s"application term cannot be consolidated: '${fun toPretty} @ ${arg toPretty}'")
    }
    else if (term =~ ("=", 2)) {
      val List(lhs, rhs) = sub
      val typ = env.typeOf_!(lhs)
      if (typ =~ ("->", 2)) {
        val va = T(TypedIdentifier(new Identifier(greek(lhs.subtrees.length), "variable", new Uid), typ.subtrees(0)))
        val ret = TypePrimitives.curry(env.typeOf_!(rhs))(env.scope)._2
        bind(va)
        ∀(va)(consolidate1(TypedTerm(lhs :@ va, typ.subtrees(1)) =:= TypedTerm(rhs :@ va, ret)))
      }
      else if (rhs =~ ("/", 2)) {
        val List(trueB, falseB) = rhs.subtrees
        val cond = ↓?(trueB)
        && (List(cond -> (lhs =:= trueB), (~cond) -> (lhs =:= falseB)) map consolidate1)
      }
      else if (rhs =~ ("|!", 2)) {
        val cond = rhs.subtrees(1)
        import Prelude.↓
        && (List(cond -> consolidate1(lhs =:= rhs.subtrees(0)), (~cond) -> (~(↓(lhs)))))
      }
      else {
        role match {
          case Role.Definition => (↓?(lhs) <-> ↓?(rhs)) & (lhs =:= rhs)
          case _               => (↓?(lhs) <-> ↓?(rhs)) & (↓?(lhs) -> (lhs =:= rhs))
        }
      }
    }
    else if (term =~ ("<->", 2)) {
      val List(lhs, rhs) = sub
      val typ = env.typeOf_!(lhs)
      if (typ =~ ("->", 2)) {
        val va = T(TypedIdentifier(new Identifier(greek(lhs.subtrees.length), "variable", new Uid), typ.subtrees(0)))
        val ret = TypePrimitives.curry(env.typeOf_!(rhs))(env.scope)._2
        bind(va)
        ∀(va)(consolidate1(TypedTerm(lhs :@ va, typ.subtrees(1)) <-> TypedTerm(rhs :@ va, ret)))
      }
      else (lhs <-> rhs)
    }
    else if (term =~ ("↦", 2)) {
      bind(term.subtrees(0))
      term  /* postpone until beta reduction occurs */
    }
    else if (term =~ ("∀", 2) || term =~ ("↦", 2)) {
      bind(term.subtrees(0))
      T(term.root, sub)
    }
    else if (term =~ ("↓",1)) {
      ↓?(sub(0))
    }
    else T(term.root, sub)
  }
  
  def bind(va: Term) {
    /**/ assert(va.isLeaf) /**/
    if (isFuncType(env.typeOf_!(va)))
      currying += (va.root -> (overload(va.root) take 1))  /* bound var: has only one version */
    alwaysDefined += va.root
  }
  
  import Prelude.TRUE
  
  def ↓? (term: Term): Term = {
    if (env.typeOf(term) exists isFuncTypeExt) TRUE
    else
      &&( TI("↓")(term) :: (term.subtrees map ↓? filter (_ != TRUE)) )
  }
  
  //--------------
  // Currying Part
  //--------------
  
  import TypeTranslation.{MicroCode,In,Out,Check}
  import TypePrimitives.arity
  import syntax.Scheme
        
  val currying = collection.mutable.Map[Identifier, List[TypedIdentifier]]()
  
  def uncurry(term: Term): Term = {
    if (term =~ ("↓",1)) {
      val atom = term.subtrees(0)
      val checks = if (isConsolidated(atom)) List()
        else atom.root match {
          case a if a == "@" => atom.subtrees(0).root match {
            case tid: TypedIdentifier => TypeTranslation.checks(env.scope, tid, atom.subtrees drop 1)
            case _ => List()
          }
          case tid: TypedIdentifier => TypeTranslation.checks(env.scope, tid, atom.subtrees)
          case _ => List()
        }
      &&(T(term.root)(uncurry(atom)) :: (checks map uncurry))
    }
    else if (term.root == "@") {
      uncurry1(term.subtrees(0), term.subtrees drop 1)
    }
    else preserveAbs(term, uncurry0(term))
  }
    
  def uncurry0(term: Term): Term = currying get term.root match {
    case Some(oset) => oset find (x => arity(x.typ) == term.subtrees.length) match {
      case Some(variant) => T(variant, term.subtrees map uncurry _)
      case _ => uncurry1(T(term.root), term.subtrees)
    }
    case _ => T(term.root, term.subtrees map uncurry _)
  }
    
  def uncurry1(fun: Term, args: List[Term]) = {
    val ucfun = uncurry(fun)
    val typ = env.typeOf_!(ucfun)
    env.scope.functypes.values find (_.faux == typ.root) match {
      case Some(functype) => TypedTerm(T(functype.app.head, ucfun :: (args map uncurry)), T(functype.ret))
      case _ => throw new Scope.TypingException(s"unrecognized reflection type '$typ' for '${ucfun toPretty}'")
    }
  }
  
  def overload(typ: Term): List[Term] = overload(rawtype(TypeTranslation.emit(env.scope, typ))) map (TypeTranslation.canonical(env.scope, _))
  
  def overload(symbol: Identifier): List[TypedIdentifier] = {
    val ns = new Uid
    val typ = env.typeOf_!(symbol)
    for (otyp <- overload(typ)) yield {
      if (otyp == typ) TypedIdentifier(symbol, otyp)
      else
      TypedIdentifier(new Identifier(s"${symbol.literal}[${arity(otyp)}]", "function", ns), otyp)
    }
  }
    
  def overload(micro: List[MicroCode]): List[List[MicroCode]] = List(Out(abstype(TypeTranslation.canonical(env.scope, micro)))) ::
    (micro match {
      case In(typ) :: tail => 
        val arg = abstype(typ)
        (overload(tail) map (In(arg) :: _))
      case _ => Nil
    })

  def curryAxioms(variant: TypedIdentifier, master: TypedIdentifier) = {
    val args = TypePrimitives.args(variant.typ)
    val ret = TypePrimitives.ret(variant.typ)
    val arity = args.length
    /**/ assume(ret.isLeaf) /**/
    env.scope.functypes.values find (x => x.faux == ret.root) match {
      case Some(functype) =>
        val qv = qvars(args ::: (functype.args map (T(_))))
        val fret = T(functype.ret)
        Some(∀(qv)
          (TypedTerm(T(functype.app.head)(TypedTerm(T(variant)(qv take arity), ret))(qv drop arity), Consolidated(fret)) =:= TypedTerm(T(master)(qv), Consolidated(fret))))
      case _ => None
    }
  }
    
  def curryAxioms(variants: List[TypedIdentifier], used: Set[Identifier]): List[Term] = {
    val master = variants.last
    variants dropRight 1 filter (used.contains) flatMap (curryAxioms(_, master))
  }
  
  def curryAxioms(used: Set[Identifier]): List[Term] = currying.values flatMap (curryAxioms(_,used)) toList
 
  //-------------
  // Support Part
  //-------------
  
  val supports = collection.mutable.Map[Identifier, TypedIdentifier]()
  val alwaysDefined = collection.mutable.Set[Identifier]()
  
  def supportType(typ: Term): Term =
    if (typ.root == "->") T(typ.root, (typ.subtrees dropRight 1) :+ supportType(typ.subtrees.last))
    else B
  
  def support(symbol: Identifier) = supports get symbol match {
    case Some(supp) => supp
    case _ =>
      val supp = TypedIdentifier(new Identifier(s"|${symbol.literal}|", "predicate", new Uid),
                                 supportType(env.typeOf_!(symbol)))
      supports += symbol -> supp
      supp
  }
  
  def support(term: Term): Term =
    if (term =~ ("↓",1)) {
      val atom = term.subtrees(0)
      if (alwaysDefined contains atom.root) TRUE 
      else if (atom.root == "+") TRUE  /* @@ TODO add alwaysTotal? */
      else T(support(atom.root), atom.subtrees map support)
    }
    else
      T(term.root, term.subtrees map support)
  
  //------------
  // Solver Part
  //------------
  def solve(assumptions: List[Term], goals: List[Term]): Trench[Term] = solve(List(), assumptions, goals)
    
    
  def solve(definitions: List[Term], assumptions: List[Term], goals: List[Term]) = {
    import semantics.smt.Z3Sugar
    import syntax.Piping._
    
    def reflect(phi: Term)(implicit role: Role.Value=Role.Proposition) = {
      log.fine(phi.untype toPretty)
      val phi_c = consolidate(phi)
      log.fine(s"  ${phi_c toPretty}")
      val phi_u = uncurry(phi_c)
      log.fine(s"  ${phi_u toPretty}")
      val phi_s = support(phi_u)
      log.fine(s"  ${phi_s toPretty}")
      FolSimplify.simplify(phi_s)
    }
    def e(l: List[Term]) = new Trench[Term](l)
    val fo_assumptions = (e(definitions) map_/ (reflect(_)(Role.Definition))) ++ 
                         (e(assumptions) map_/ reflect)
    
    val fo_goals = e(goals) map_/ reflect flatMap (_.split(new Identifier("&", "connective")))

    val fo_symbols = (fo_assumptions.toList ++ fo_goals.toList) flatMap (_.nodes map (_.root)) toSet
    
    val prelude = typeinfo ++ curryAxioms(fo_symbols) ++ equality(fo_symbols)
    val fo_prelude = e(prelude) map_/ reflect filter (_ != TRUE)
    
    log.fine("-" * 60)
  
    Trench.display(fo_assumptions)
    report.NotebookLog.out += Trench.displayRich(fo_assumptions)
    Trench.display(fo_prelude)
    Trench.display(fo_goals, "◦")
    
    val (z3g, fo_base) = TypeTranslation toSmt List(env)

    val status =
      z3g.solve(fo_base ++ (
        for (atn <- fo_assumptions.toList ++ fo_prelude.toList if atn != TRUE) yield {
          z3g.formula(atn)
        }),
        fo_goals.toList map z3g.formula)
        
    val statusMap = (fo_goals.toList map (new Id(_))) zip status toMap
    val results = fo_goals map_/ (s => TI(statusMap(s).toPretty))
    
    Trench.display(results, "◦")
    report.NotebookLog.out += Trench.displayRich(results, "◦")

    results
  }
  
}


object `@Reflection` {
  
  import semantics.Domains._
  import semantics.Prelude._
    

  /**
   * Demonstrates use of reflection to prove a simple property
   * of functions.
   */
  def main(args: Array[String]): Unit = {
    import examples.Paren._
    implicit val scope = new Scope
    
    scope.sorts.declare(J.root)
    scope.sorts.declare(R.root)
    scope.sorts.declare(J0.root :<: J.root)
    scope.sorts.declare(J1.root :<: J.root)
    
    val f = TV("f")
    val c = TV("c")
    val x = TV("x")
    val i = TV("i")
  
    val prenv = (TypeTranslation.subsorts(scope) where (compl(J)(J0, J1)))
    val typedecl = Map(
        f ~> ((J -> R) -> (J -> R)),
        c ~> ((J0 -> R) -> (J1 -> R)),
        x ~> (J -> R),
        i ~> J )
    
    val env = prenv ++ TypeTranslation.decl(scope, typedecl)
  
    val JR = new FunctionType(List(J.root), R.root)
    val JRJR = new FunctionType(List(JR.faux, J.root), R.root)
    scope.functypes += (((J -> R), JR))
    scope.functypes += (((J -> R) -> (J -> R), JRJR))
  
    // f := c / I := \x i. c x i / x i
    
    // need to prove
    // c x = c (f x)
    val Ijr = T(TypedIdentifier(I("I"), (J->R) -> (J->R)))
    val xj0 = T(TypedIdentifier(I("x|J0"), (J -> R)))
    val cx = T(TypedIdentifier(I("cx"), J -> R))
    val fx = T(TypedIdentifier(I("fx"), J -> R))
    val fxj0 = T(TypedIdentifier(I("fx|J0"), J -> R))
    val cfx = T(TypedIdentifier(I("cfx"), J -> R))
    
    
    val assumptions = List(
        Ijr =:= { val x = $v ; T(x) ↦ T(x) },
        f =:= TypedTerm(c /: Ijr, (J->R) -> (J->R)),
        xj0 =:= T(TypedIdentifier(x.root, J0 -> R)),
        cx =:= TypedTerm(c :@ xj0, J -> R),
        fx =:= TypedTerm(f :@ x, J -> R),
        fxj0 =:= T(TypedIdentifier(fx.root, J0 -> R)),
        cfx =:= TypedTerm(c :@ fxj0, J -> R)
      )
      
    
    val goals = List(cx =:= cfx)
        
    val symbols = List(Ijr, c, f, x, xj0, cx, fx, fxj0, cfx)
    
    val reflect = new Reflection(env, typedecl)
    
    reflect.currying ++= symbols map (symbol => (symbol.root, reflect.overload(symbol.root))) toMap
  
    for (symbol <- symbols) {
      println(s"${symbol.untype} :: ${env.typeOf(symbol.root).get toPretty}")
      /*
      val variants = reflect.currying(symbol.root)
      for (variant <- variants)
        println(s"   ${variant toPretty}")
      for (axiom <- reflect.curryAxioms(variants))
        println(s"   ***  ${axiom toPretty}")
      */
    }
    
    println("· " * 25)
  
    reflect.solve(assumptions, goals)
    
    /*
    val expr1 = (x :: (J0 -> R))
    val expr2 = @:(f, x) :: (J0 -> R)
    val expr3 = @:(@:(c, x), i) /: @:(x, i)
    
    val (expr1_id, expr1_env) = TermTranslation.term(env, expr1, Map())
    val (expr2_id, expr2_env) = TermTranslation.term(env, expr2, Map())
    val (expr3_id, expr3_env) = TermTranslation.term(env, expr3, Map())
    println(JR.abs(expr2_env.decl(expr2_id)).toPretty)*/
      
    /*
    import semantics.smt.Z3Sugar._
    
    {
      val F = ctx mkUninterpretedSort "J->R"
      val J = ctx mkUninterpretedSort "J"
      val R = ctx getRealSort
      val B = ctx getBoolSort
      
      val J0 = func ("J₀" :-> (J, B))
      val J1 = func ("J₁" :-> (J, B))
      
      val c = func ("c" :-> (F, J, R))
      val c_def = func ("|c|" :-> (F, J, B))
      val f = func ("f" :-> (F, J, R))
      val f_def = func ("|f|" :-> (F, J, B))
      
      val F_app = func ("@" :-> (F, J, R))
      val F_app_def = func ("|@|" :-> (F, J, B))
      
      val i = const ("i" -> J)
      val j = const ("j" -> J)
      val k = const ("k" -> J)
      val θ_abs = const ("θ#" -> F)
      val ζ_abs = const ("ζ#" -> F)
  
      val fθ_abs = const ("fθ#" -> F)
      
      val θ_J0R_abs = const ("θ|J0#" -> F)
      val fθ_J0R_abs = const ("fθ|J0" -> F)
      
      val assumptions = List(
          ∀(i)(J0(i) <-> ~J1(i)),
          // c :: (J0 -> R) -> (J1 -> R)
          ∀(θ_abs, i)(c_def(θ_abs, i) -> J1(i)),
          // f := c / I
          ∀(θ_abs, i)(
              ( c_def(θ_abs, i) -> (f_def(θ_abs, i) & (f(θ_abs, i) =:= c(θ_abs, i))) ) &
              ( ~c_def(θ_abs, i) -> ((f(θ_abs, i) =:= F_app(θ_abs, i)) & (f_def(θ_abs, i) <-> F_app_def(θ_abs, i))) )
            ),
          // f θ
          ∀(i)( (F_app(fθ_abs, i) =:= f(θ_abs,i)) & (F_app_def(fθ_abs, i) <-> f_def(θ_abs,i)) ),
          // θ|J0
          ∀(i)( (F_app(θ_J0R_abs, i) =:= F_app(θ_abs, i)) &
              (F_app_def(θ_J0R_abs, i) <-> (F_app_def(θ_abs, i) & J0(i))) ),
          // (f θ)|J0
          ∀(i)( (F_app(fθ_J0R_abs, i) =:= F_app(fθ_abs, i)) &
              (F_app_def(fθ_J0R_abs, i) <-> (F_app_def(fθ_abs, i) & J0(i))) ),
          // F equality
          ∀(θ_abs, ζ_abs)(
            ∀(i)( (F_app_def(θ_abs, i) <-> F_app_def(ζ_abs, i)) &
                  (F_app_def(θ_abs, i) -> (F_app(θ_abs, i) =:= F_app(ζ_abs, i))) ) -> (θ_abs =:= ζ_abs)
          )
        )
          
      val goals = List(
          //F_app_def(θ_J0R_abs, i) <-> F_app_def(fθ_J0R_abs, i),
          //F_app_def(θ_J0R_abs, i) -> (F_app(θ_J0R_abs, i) =:= F_app(fθ_J0R_abs, i))
          c(θ_J0R_abs, i) =:= c(fθ_J0R_abs, i)
        )
      
      solveAndPrint(assumptions, goals)
    } */
  }
  
}
