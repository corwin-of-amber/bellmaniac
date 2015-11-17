package synth.proof

import syntax.AstSugar._
import syntax.Identifier
import semantics.UntypedTerm
import semantics.pattern.Expansion
import semantics.TermTranslation.TermBreak
import semantics.Binding
import semantics.TypeInference
import semantics.TypeTranslation.Environment
import semantics.pattern.MacroMap
import semantics.Reflection
import semantics.TypeTranslation
import semantics.TypePrimitives
import semantics.TypedTerm
import semantics.Scope
import semantics.TypedLambdaCalculus
import semantics.TypeTranslation.Declaration
import semantics.FormulaTranslation
import semantics.Prelude
import synth.pods.Pod
import semantics.TypedIdentifier
import semantics.TypedSubstitution
import semantics.Reflection.Compound
import semantics.Trench


/**
 * Carries out automatic proofs employing macro expansion, term translation,
 * and reflection.
 */
class Prover(val pods: List[Pod], val verbose: Prover.Verbosity=Prover.Verbosity.All)(implicit val env: Environment) {

  import TypeTranslation.TypingSugar._
  import TypedTerm.typeOf_!
  import TypePrimitives.{shape, args}
  import Prelude.B
  
  implicit val scope = env.scope
  val typedecl = env.typedecl
  val expand = new Expansion(pods map (_.macros) reduceOption (_ ++ _) getOrElse MacroMap.empty)
    
  def intros(goal: Term): (List[Term], Term) = {
    if (goal =~ ("=", 2)) {
      val List(lhs, rhs) = goal.subtrees
      val ftype = shape(env.typeOf_!(lhs))
      if (ftype != shape(env.typeOf_!(rhs)))
        throw new Scope.TypingException(s"incompatible types in equality, '${typeOf_!(lhs) toPretty}'  =  '${typeOf_!(rhs) toPretty}")
      val vars = qvars(args(ftype))
      (vars, TypedLambdaCalculus.simplify((lhs:@(vars:_*)) =:= (rhs:@(vars:_*))))
    }
    else if (goal.root == "∀") {
      val vars = goal.subtrees.dropRight(1)
      val (more_vars, g) = intros(goal.subtrees.last)
      (vars ++ more_vars, g)
    }
    else if (goal =~ ("->", 2)) {
      val (vars, g) = intros(goal.subtrees(1))
      (vars, TypedTerm(goal.subtrees(0) -> g, B))
    }
    else (List(), goal)
  }
    
  
  def e(term: Term) = {
    val (vassign, typed) = TypeInference.infer(Binding.prebind(term), typedecl)
    (TypeTranslation.decl(env.scope, vassign), expand(typed))
  }

  import Prover.Verbosity

  class Transaction(verbose: Verbosity=verbose) {
    val termb = new TermBreak(env)
    val formulat = new FormulaTranslation(termb)
    val termlings = collection.mutable.ListBuffer[(Environment, List[Term])]()
    val locals = collection.mutable.Set[Identifier]()
    
    def typedecls(symbols: Iterable[Identifier]) = symbols collect {
      case tid: TypedIdentifier => tid.untype -> tid.typ
    } toMap
    
    def let(term: Term) = {
      val (v_env, (v, v_t)) = be(term)
      termlings += ((v_env, v_t))
      v
    }
    
    def prop(formula: Term) = {
      val (env1, typed) = e(formula)
      val (v, v_t) = formulat(typed)
      termlings += ((env1, v_t))
      v
    }
    
    def goal(formula: Term) = {
      val (env1, typed) = e(formula)
      val (v, v_t) = formulat(typed)
      termlings += ((env1, List()))
      Compound(v_t, v)
    }
    
    def intros(goal: Term) = {
      val (vars, g) = Prover.this.intros(goal)
      locals ++= vars map (_.leaf)
      g
    }
    
    def commonSwitch(c: CommonSubexpressionElimination) = 
      new TypedSubstitution(
        c.cabinet filter (_.length > 1) flatMap { l =>
          val se = l.head.compact
          def prefix(s: String) = if (s == "") "" else s"[$s ↦] "
          println(s"${l.length}  x  ${prefix(se.enclosure map (_ toPretty) mkString " ")}${se.term toPretty}");
          val uf = let(se.capsule):@(se.enclosure)
          l map (_.term) map ((_, uf))
        } toList)
    
    def commit(assumptions: Iterable[Term], goals: Iterable[Term])(implicit d: DummyImplicit): Trench[Term] = {
      commit(assumptions, goals map (Compound(_)))
    }
    
    def commit(assumptions: Iterable[Term], goals: Iterable[Compound]) = if (goals.isEmpty) Trench.empty[Term] else {
      val (lassumptions, lgoals) = (assumptions.toList, goals.toList) // prevent laziness
      val symbols = typedecl.keys ++ (pods flatMap (_.decl.symbols)) ++ termb.intermediates ++ locals
      val env1 = (env /: termlings) { case (env, (env1, _)) => env ++ env1 }
      val env2 = (env1 /: (pods map (_.decl.shallow))) { case (e, d) => e + d }
      val terms1 = termlings map (_._2)
      
      val reflect = new Reflection(env2, typedecl ++ typedecls(locals))(verbose)
      reflect.currying ++= symbols filter (x => env1.typeOf(x) exists Reflection.isFuncType) map
                                          (symbol => (symbol, reflect.overload(symbol))) toMap
  
      for (variants <- reflect.currying.values)
        reflect.alwaysDefined ++= (variants dropRight 1)
                                      
      if (verbose == Verbosity.All) println("· " * 25)
  
      reflect.solve(terms1.toList flatten, lassumptions ++ (pods flatMap (_.decl.precondition)), lgoals)
    }
    
    def be(term: Term) = {
      val (env1, typed) = e(term)
      (env1, termb(typed))
    }
    
  }
  
  
  import semantics.pattern.{SimplePattern,ExactMatch}
  import collection.mutable.ListBuffer
  
  case class Subexpression(term: Term, enclosure: List[Term]) {
    def compact = Subexpression(term, enclosure filter (term.leaves.contains))
    def capsule = (enclosure :\ term)(_ ↦ _)
  }
  
  class CommonSubexpressionElimination {
    
    def this(formulas: Iterable[Term], pattern: SimplePattern) = {
      this; scan(formulas, pattern)
    }
    
    val cabinet = ListBuffer[ListBuffer[Subexpression]]()
    
    def scan(formulas: Iterable[Term], pattern: SimplePattern) {
      for (a <- formulas) {
        pattern.find(a) foreach (mo => { 
          def subexpr = Subexpression(mo.subterm, TypedLambdaCalculus.enclosure(a, mo.subterm) get)
          cabinet.find { l => new ExactMatch(l.head.term) matchInclTypes (mo.subterm) } match {
            case Some(l) => l += subexpr
            case None => cabinet += ListBuffer(subexpr)
          }
        })
      }    
    }
        
  }
  
}


object Prover {
  val Verbosity = Reflection.Verbosity
  type Verbosity = Reflection.Verbosity
}