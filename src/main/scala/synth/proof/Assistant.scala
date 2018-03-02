package synth.proof


import syntax.{Identifier,Tree}
import syntax.AstSugar._
import semantics.Scope
import semantics.FunctionType
import semantics.TypedTerm
import semantics.TypeTranslation
import semantics.TypeTranslation.Environment
import semantics.TypeTranslation.TypingSugar._
import semantics.TypePrimitives.{shape,args}
import semantics.TypedLambdaCalculus.{pullOut, enclosure}
import semantics.ProgressiveTypedSubstitution
import semantics.TypeInference
import semantics.Binding
import semantics.Prelude
import semantics.TypedLambdaCalculus
import semantics.LambdaCalculus
import semantics.pattern.SimplePattern
import semantics.Trench
import report.DevNull
import report.AppendLog
import report.data.Rich
import syntax.transform.Extrude
import syntax.transform.EqByRef
import semantics.Domains
import semantics.Prelude.{R,N}
import synth.pods.PartitionPod
import synth.pods.TotalOrderPod
import synth.pods.IndexArithPod
import semantics.smt.SmtGuidelines
import semantics.pattern.Pattern



class Assistant(implicit env: Environment) {
  implicit val scope = env.scope
  val typedecl = env.typedecl
  
  def precompile(term: Term) = {
    Binding.prebind(term)
  }
  
  def compile(term: Term) = {
    TypeInference.infer(Binding.prebind(term), typedecl)._2
  }
  
  import Prelude.{↓,B}
  
  def encapsulate(goal: Term, item: Term, item_uf: Term) = {
    val capsule = pullOut(goal, item) get
    val args = enclosure(goal, item) get
    val subst = new ProgressiveTypedSubstitution(List((item, item_uf :@ (args)))) with EqByRef[Term]
    (capsule, subst(goal))
  }
  
  def instantiate(goal: Term, concretes: List[Term]): Term = {
    if (concretes.isEmpty) goal
    else if (goal.root == "∀") {
      val vars = goal.subtrees.dropRight(1)
      val subst = new ProgressiveTypedSubstitution(vars zip concretes)
      instantiate(subst(goal.subtrees.last), concretes drop vars.length)
    }
    else if (goal =~ ("->", 2)) {
      val g = instantiate(goal.subtrees(1), concretes)
      TypedTerm(goal.subtrees(0) -> g, B)
    }
    else throw new Scope.TypingException(s"cannot instantiate '${goal toPretty}' (with '${concretes map (_.toPretty) mkString "', '"}')")
  }

  // Copied over from Prover
  def intros(goal: Term) = {
    val (vars, igoal) = intros0(goal);
    &&(vars map (↓(_))) -> igoal
  }

  def intros0(goal: Term): (List[Term], Term) = {
    if (goal =~ ("=", 2)) {
      val List(lhs, rhs) = goal.subtrees
      val ftype = shape(env.typeOf_!(lhs))
      if (ftype != shape(env.typeOf_!(rhs)))
        throw new Scope.TypingException(s"incompatible types in equality, '${env.typeOf_!(lhs) toPretty}'  =  '${env.typeOf_!(rhs) toPretty}")
      val vars = qvars(args(ftype))
      (vars, simplify((lhs:@(vars:_*)) =:= (rhs:@(vars:_*))))
    }
    else if (goal.root == "∀") {
      val vars = goal.subtrees.dropRight(1)
      val (more_vars, g) = intros0(goal.subtrees.last)
      (vars ++ more_vars, g)
    }
    else if (goal =~ ("->", 2)) {
      val (vars, g) = intros0(goal.subtrees(1))
      (vars, TypedTerm(goal.subtrees(0) -> g, B))
    }
    else (List(), goal)
  }
  
  /**
   * @param term: a term to process and simplify.
   * @param argpat: when to apply a beta reduction to an expression of the form (v ↦ t₀) t₁.
   *   Term is reduced when argpat(t₁) is true (default is always).
   */
  def simplify(term: Term)(implicit argpat: Term=>Boolean=_=>true): Term = {
    val sub = term.subtrees map simplify
    if (term =~ ("@", 2) && sub(0) =~ ("↦", 2) && argpat(sub(1)))
      simplify(TypedLambdaCalculus.beta(typeGuard(sub(0)), sub(1)))
    else if (term =~ ("@", 2) && sub(0).root == "/") TypedTerm.preserve(term, TI("/")(sub(0).subtrees map (x => 
      simplify(TypedTerm.preserve( term, TypedTerm.preserveBoth(sub(0), x) :@ sub(1) )))))
    else if (term =~ ("|!", 2)) {
      val cond = unguard(term.subtrees(1))
      if (cond == Prelude.TRUE)
        TypedTerm.preserveBoth(term, sub(0))
      else if (sub(0) =~ ("|!", 2)) {
        val mcond = mergeConds(sub(0).subtrees(1), cond)
        if (mcond == sub(0).subtrees(1)) sub(0)
        else TypedTerm.preserveBoth(term, TypedTerm.preserve(sub(0), sub(0).subtrees(0) |! mcond))
      }
      else TypedTerm.preserve(term, sub(0) |! cond)
    }
    else if (term =~ (":", 2)) sub(1) // TODO only throw away labels when necessary?
    else TypedTerm.preserveBoth(term, T(term.root, sub))
  }
  
  def unguard(cond: Term): Term = {
    val inner = cond.nodes filter (_ =~ ("|!", 2)) toList
    def hoist = &&(inner map (_.subtrees(1)))
    if (inner.isEmpty) cond
    else 
      TypedTerm.replaceDescendants(cond, inner map (n => (n, n.subtrees(0)))) & hoist
  }
  
  def typeGuard(fun: Term)(implicit scope: Scope) = {
    val (args, body) = LambdaCalculus.uncurry(fun)
    val checks = TypeTranslation.checks(scope, env.typeOf_!(fun), args)
    if (checks.isEmpty) fun
    else TypedTerm.replaceDescendant(fun, (body, TypedTerm.preserve(body, body |! &&(checks))))
  }
  
  def mergeConds(condA: Term, condB: Term) = {
    val a = condA.split(I("∧"))
    && (a ++ (condB.split(I("∧")) filterNot a.contains))
  }
  
  def scopeFacts(designated: Map[DesignatedRole, Term]=Map.empty) = {
    def is_⊥(t: Tree[Identifier]) = t.root == Domains.⊥ || t.root.ns == Domains.⊥
    val < = TV("<")
    val masterIndex =
      scope.sorts.masters map (T(_)) filterNot List(N,R).contains flatMap { J =>
        val toJ = designated get DesignatedRole(<, J) match { 
          case Some(lt) => TotalOrderPod(J, lt) 
          case _ =>        TotalOrderPod(J) 
        }
        val idxJ = IndexArithPod(J, toJ.<)
        List(toJ, idxJ)
      }
    val partitions =
      scope.sorts.hierarchy.nodes collect {
        case t if !is_⊥(t) && !t.subtrees.exists(is_⊥) && t.subtrees.length == 2 =>
          val J = T(scope.sorts.getMasterOf(t.root))
          val < = masterIndex collectFirst { case toJ: TotalOrderPod if toJ.D == J => toJ.< } get ;
          PartitionPod(T(t.root), <, T(t.subtrees(0).root), T(t.subtrees(1).root))
      }
    masterIndex ++ partitions
  }
  
  /**
   * Use common idioms for passing a proof obligation to the prover.
   */
  def invokeProver(assumptions: List[Term], goals: List[Term], subexprPattern: Pattern, verbose: Prover.Verbosity=null, 
                   oneByOne: Boolean=true, exitOnFail: Boolean=true)
      (implicit prover: Prover, smtGuidelines: SmtGuidelines=SmtGuidelines.default, 
                logf: AppendLog=DevNull, extrude: Extrude=new Extrude(Set.empty)) = {
    import syntax.Piping._

    println("· " * 25)

    if (ui.Config.config.log() contains "Prover") {
      for (goal <- goals) logf += Map("term" -> goal,
        "display" -> Rich.display(extrude(goal) |-- report.console.Console.display))
    }

    val commits =
      for (goals <- if (oneByOne) goals map (List(_)) else List(goals)) yield {
        val igoals = goals map intros
        val t = if (verbose == null) new prover.Transaction else new prover.Transaction(verbose)
        val switch = t.commonSwitch(new prover.CommonSubexpressionElimination(igoals, subexprPattern))

        t.commit(assumptions map simplify map t.prop, igoals map (switch(_)) map simplify map t.goal)
      }

    val results = commits reduce (_ ++ _)

    if (exitOnFail && !(results.toList forall (_.root == "valid"))) System.exit(1)

    println("=" * 80)  // QED!
    
    results
  }

}

case class DesignatedRole(symbol: Term, domain: Term)
