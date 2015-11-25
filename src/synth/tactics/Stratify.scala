package synth.tactics

import syntax.Identifier
import syntax.AstSugar._
import semantics.Scope
import semantics.FunctionType
import semantics.TypedTerm
import semantics.TypeTranslation
import semantics.TypeTranslation.Environment
import semantics.TypedIdentifier
import semantics.Reflection
import semantics.TypePrimitives
import semantics.TypeTranslation.TypingSugar._
import semantics.TypedLambdaCalculus
import semantics.TypeInference
import syntax.Strip
import semantics.TypeTranslation.Declaration
import synth.proof.Prover
import synth.pods.TotalOrderPod
import synth.pods.Pod
import semantics.TypedSubstitution
import semantics.Prelude
import synth.pods.NilPod
import synth.pods.ConsPod
import synth.pods.MinPod
import synth.pods.NatPod
import semantics.pattern.MacroMap
import semantics.ProgressiveTypedSubstitution
import semantics.Reflection.Consolidated
import semantics.Binding
import syntax.transform.EqByRef


object Stratify {

  import semantics.Domains._
  import semantics.Prelude._

  class PodBuilder(program: Term, symbols: List[Term])(implicit env: Environment) {
    val (vassign, body) = TypeInference.infer(Binding.prebind(program))(env.scope)
    
    def decl = mkDecl(symbols, body.split(Prelude.program.root))
    def macros = mkMacros(symbols, body.split(Prelude.program.root))
    
    def mkTid(id: Identifier) = TypedIdentifier(id, vassign(id))
    def mkTid(t: Term): TypedIdentifier = mkTid(t.leaf)
    def mkDecl(symbols: List[Term], axioms: List[Term]) = {
      val boundvars = (axioms map Binding.PREBIND_SET.boundvars flatten) map (T(_))
      val subst = new TypedSubstitution((symbols ++ boundvars) map (x => (x, T(mkTid(x)))))
      new Declaration((symbols map mkTid), axioms map (subst(_)))
    }
    
    def mkMacro(defn: Term): MacroMap = {
      if (defn.root == "∀") mkMacro(defn.subtrees.last)
      else if (defn =~ ("=", 2) || defn =~ ("<->", 2)) {
        val List(head, body) = defn.subtrees
        val headSymbol :: args = head.splitLeft(@:.root)
        MacroMap(headSymbol.leaf -> { x => 
          val _ :: given = x.splitLeft(@:.root)
          if (given.length == args.length)
            Some(new ProgressiveTypedSubstitution(args zip given)(env.scope)(body))
          else
            None
        })
      }
      else throw new Error("not a definition: ${defn toPretty}")
    }
    def mkMacros(symbols: List[Term], axioms: List[Term]) = {
      val subst = new TypedSubstitution(symbols map (x => (x, T(mkTid(x)))))
      axioms map (subst(_)) map mkMacro reduce (_ ++ _)
    }
  }
  
  class MonoPod(val F: Term, val < : Term)(implicit env: Environment) extends Pod {
    val ⊑ = $TyTV("⊑", F ->: F ->: B)
    val ≼ = $TyTV("≼", F ->: F ->: B)
    val (θ, ζ) = ($TV("θ"), $TV("ζ"))
    val vars = qvars(TypePrimitives.args(F))
    
    override val decl = new PodBuilder(program(
        ∀(θ,ζ)(
            ⊑ :@ (θ,ζ) <-> 
              ∀(vars)(↓(θ:@(vars)) -> ( ↓(ζ:@(vars)) & ~(< :@(θ:@(vars), ζ:@(vars)))) )
        ),
        ∀(θ,ζ)(
            ≼ :@ (θ,ζ) <-> 
              ∀(vars)(↓(θ:@(vars)) -> ↓(ζ:@(vars)) )
        )
      )
      , List(⊑, ≼)/*, θ, ζ) ++ vars*/).decl
/*
    override val macros = new PodBuilder(
        ∀(θ,ζ)(
            ⊑ :@ (θ,ζ) <-> 
              ∀(vars)(↓(θ:@(vars)) -> ( ↓(ζ:@(vars)) & ~(< :@(θ:@(vars), ζ:@(vars)))) )
        )
      , List(⊑, θ, ζ) ++ vars).macros
  */    
  }
  
  
  class AntiSymmetryPod(val ⊑ : Term)(implicit env: Environment) extends Pod {
    val (x, y) = ($TV("x"), $TV("y"))
    
    override val decl = new PodBuilder(
        ∀(x,y)( (⊑ :@(x,y)) ->: (⊑ :@(y,x)) ->: (x =:= y) ),
        List(/*x,y*/)).decl
  }
  
  class DecreasingPod(val f : Term, val ⊑ : Term, val ≼ : Term)(implicit env: Environment) extends Pod {
    val (x, y) = ($TV("x"), $TV("y"))
    
    override val decl = new PodBuilder(program(
//        ∀(x)( ⊑ :@ (x, f :@ x) ),
        ∀(x, y)( (⊑ :@ (x, y)) -> (≼ :@ (f :@ x, f :@ y)) )
      ), List(/*x, y*/)).decl
  }
  
  import TypePrimitives.{shape,args}
  import TypedLambdaCalculus.{pullOut, enclosure}
  
  class Assistant(implicit env: Environment) {
    implicit val scope = env.scope
    
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
    def intros(goal: Term): (List[Term], Term) = {
      if (goal =~ ("=", 2)) {
        val List(lhs, rhs) = goal.subtrees
        val ftype = shape(env.typeOf_!(lhs))
        if (ftype != shape(env.typeOf_!(rhs)))
          throw new Scope.TypingException(s"incompatible types in equality, '${env.typeOf_!(lhs) toPretty}'  =  '${env.typeOf_!(rhs) toPretty}")
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
  }
  
  
  def main(args: Array[String]): Unit = {

    import examples.Paren
    import examples.Paren._
    import Shrink.{InputPod,APod}
    import semantics.Binding.{inline,prebind}
            
    val prenv = Paren.env
    implicit val scope = prenv.scope
    
    val A = new APod(Paren.J, Paren.J0)
    
    val (vassign, program) = TypeInference.infer( inline( prebind(InputPod.program(A.program).unfoldRight) ) )
    
    implicit val env = prenv ++ TypeTranslation.decl(scope, vassign)
    
    println("-" * 80)
    
    import java.util.logging.Level
    //Reflection.log.setLevel(Level.FINER)
        
    val toR = TotalOrderPod(R)
    val nilNR = NilPod(N, R)
    val consR = ConsPod(R)
    val minJR = MinPod(J, R, toR.<)
    val minNR = MinPod(N, R, toR.<)
    import toR.<
    val plustot = ∀:(R, (a,b) => ↓(a + b) & (TypedTerm(a + b, R) =:= TypedTerm(b + a, R)))
    val plusmono = ∀:(R, (a,b,c,d) => ~(< :@(a, c)) ->: ~(< :@(b, d)) ->: ~(< :@(a + b, c + d)))
    
    val monoJJR = new MonoPod(J ->: J ->: R, toR.<)
    val monoJJJR = new MonoPod(J ->: J ->: J ->: R, toR.<)
    
    import TypedLambdaCalculus.{pullOut,enclosure,simplify}
    
    val f = program :/ "f"
    val item = f :/ "item"
    
    val a = new Assistant
    val item_uf = $TyTV("『item』", (((J x J) ∩ Paren.<) ->: R) ->: J ->: J ->: J ->: env.typeOf_!(item))
    val (item_capsule, f_enc) = a.encapsulate(f, item, item_uf)
    
    val (y, z, u) = ($TyTV("y", J ->: J ->: R), $TyTV("z", J ->: J ->: R), $TyTV("u", R))
    val fact = monoJJR.⊑ :@ (y, z)

    val asym = new AntiSymmetryPod(monoJJR.⊑)
    val dec = new DecreasingPod(f, monoJJR.⊑, monoJJR.⊑)
    
    val instances = List(
        a.instantiate(monoJJR.decl.precondition.head, List(y, z)).subtrees(1),
        //f =:= (y ↦ (i ↦ (j ↦ (min:@(item_capsule:@(y,i,j)))))),
        a.instantiate(monoJJR.decl.precondition.head, List( (i ↦ (j ↦ (min:@(item_capsule:@(y,i,j))))), 
            (i ↦ (j ↦ (min:@(item_capsule:@(z,i,j))))) ))
        //a.instantiate(monoJJJR.decl.precondition.head, List(item_uf :@ y, item_uf :@ z)).subtrees(1),
        //a.instantiate(monoJJR.decl.precondition.head, List(f :@ y, f :@ z)).subtrees(1)//,
        //a.instantiate(monoJJR.decl.precondition.head, List(f_enc :@ y, f_enc :@ z)).subtrees(1),
        //a.instantiate(dec.decl.precondition.head, List(y, z)),
        //a.instantiate(dec1.decl.precondition.head, List(y, z))
        )
    
    //val instances = List(/*monoJJR.decl.precondition.head, */dec.decl.precondition.head)
    
    instances map (x => println(x toPretty))
    
    val p = new Prover(List(NatPod, toR, minJR, minNR, consR, nilNR, monoJJR))
    val t = new p.Transaction
    
    t.commit(List(plustot, plusmono) ++ (instances dropRight 1 map simplify map t.prop), List(instances.last) map simplify map t.prop)

    /*
    val item_capsule = pullOut(f, item) get
    //val fenc = new TypedSubstitution(List((item, nilNR.nil :@ NatPod._0)))(f, (_ eq _))
    
    val asymm = new AntiSymmetryPod(monoJJR.⊑)
    import toR.<
    val plustot = ∀:(R, (a,b) => ↓(a + b) & (TypedTerm(a + b, R) =:= TypedTerm(b + a, R)))
    val plusmono = ∀:(R, (a,b,c,d) => ~(< :@(a, c)) ->: ~(< :@(b, d)) ->: ~(< :@(a + b, c + d)))
    
    val p = new Prover(List(NatPod, toR, nilNR, consR, minJR, minNR, monoJJR, monoJJJR))
    val t = new p.Transaction
    //t.commit(List(), asymm.decl.precondition map t.intros)

    val item_uf = $TyTV("@item", (((J x J) ∩ Paren.<) ->: R) ->: ((J x J) /*∩ Paren.<*/) ->: J ->: R)//t.let(item_capsule)
    val f_args = enclosure(f, item) get
    val fenc = new ProgressiveTypedSubstitution(List((item, item_uf :@ (f_args))))(env.scope)(f, (_ eq _))
    val dec0 = new DecreasingPod(item_uf, monoJJR.⊑, monoJJJR.⊑)
    val dec1 = new DecreasingPod(fenc, monoJJR.⊑, monoJJR.⊑)

    
    
    val hardLabor = dec1.decl.precondition map Binding.prebind map p.e map (_._2) map t.intros //map TypedLambdaCalculus.simplify
    Rewrite.display(hardLabor.head)
    t.locals += item_uf.root
    
    val triangleEq = ∀:(J ->: J ->: R, (x, y) => 
      ∀:(J, (i, j) => (Paren.< :@ (i, j)) -> (TypedTerm(x :@ (i,j), R) =:= TypedTerm(y :@ (i,j), R))) ->
      //(TypedTerm(T(TypedIdentifier(x.root, ((J x J) ∩ Paren.<) -> R)), J ->: J ->: R) =:= 
      // TypedTerm(T(TypedIdentifier(y.root, ((J x J) ∩ Paren.<) -> R)), J ->: J ->: R)) -> 
          Consolidated(TypedTerm(item_uf(x), J ->: J ->: J ->: R) =:= TypedTerm(item_uf(y), J ->: J ->: J ->: R)))
    
    val x = T(t.locals.find(_ == "x") get)
    
    //t.commit(List(triangleEq) ++ dec0.decl.precondition, hardLabor ++
    //     List(Consolidated(t.let(item_uf :@ x) =:= TypedTerm(item_uf(x), J ->: J ->: J ->: R))))
    
    t.commit(List(plustot, plusmono, triangleEq) ++ dec0.decl.precondition, hardLabor map t.prop)
    
    //t.commit(List(), 
    //    dec.decl.precondition map t.intros map TypedLambdaCalculus.simplify map t.prop)*/
  }
  
/*  
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
    val Ijr = TV("Ijr")

    val prenv = (TypeTranslation.subsorts(scope) where (compl(J)(J0, J1)))
    val typedecl = Map(
        //< ~> ((J x J) -> B),
        Ijr ~> (((J x J)->R) -> ((J x J)->R)),
        f ~> (((J x J) -> R) -> (((J x J) /*∩ <*/) -> R)),
        c ~> (((J0 x J0) -> R) -> ((J1 x J1) -> R)),
        x ~> ((J x J) -> R) )
    
    implicit val env = prenv ++ TypeTranslation.decl(scope, typedecl)

    // f := c / I    ( := \x i. c x i / x i )
    
    // need to prove
    // c x = c (f x)
    
    val termb = new TermBreak(env)

    val (_, cxcfx) = 
      TypeInference.infer( c =:= (x ↦ (c :@ (f :@ x))), typedecl )
      
    Rewrite.display(cxcfx)
    
    val assumptions = List(
        Ijr =:= { val x = T($v("α")) ; TypedTerm(x ↦ x, (J->(J->R))->(J->(J->R))) },
        f =:= TypedTerm(c /: Ijr, (J->(J->R)) -> (J->(J->R)))
      )
    
    val p = new Prover(List())
    
    val t = new p.Transaction
    
    t.commit(assumptions, List(t.let( p.intros(cxcfx) )))
    
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
 */
}