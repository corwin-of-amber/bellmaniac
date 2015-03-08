package synth.tactics

import syntax.Tree
import syntax.AstSugar._
import semantics.TypeTranslation.TypedTerm
import semantics.Scope
import semantics.TypeTranslation
import semantics.TypeInference
import semantics.Id
import report.console.NestedListTextFormat
import syntax.Identifier
import semantics.TypeTranslation.Environment
import semantics.Binding
import semantics.Prelude
import semantics.TypeTranslation.Environment
import semantics.TypedLambdaCalculus
import synth.tactics.Split.TermBreak
import semantics.Reflection



object Rewrite {
  
  object CPod {
    import examples.Paren.{J,w}
    import semantics.Prelude._
    
    def apply(J0: Term, J1: Term, J2: Term) = {
      val C = $TV("C")
      val P = $TV("P")
      val (θ, i, j, k) = ($TV("θ"), $TV("i"), $TV("j"), $TV("k"))
      val (item, compute) = ($TV("item"), $TV("compute"))
      TV("program")(
          P :: ((J x J) -> B),
          w :: ((J x J x J) -> R),
          C :- ((θ ↦ (i ↦ (j ↦ (min :@ (k ↦ ( item :- ((θ :@ i :@ k) + (θ :@ k :@ j) + (w :@ i :@ k :@ j))))))))
           :: ((((J x J) ∩ P) -> R) ->: J0 ->: J2 ->: R))
      )
    }
  }
  
  def display(term: Term)(implicit env: Environment) {
    val format = new NestedListTextFormat[Identifier]
    format.layOutAndAnnotate(term, (env.typeOf(_) map (_.toPretty)), (_.toPretty))
  }
  
  def display(xterm: Tree[Term]) {
    val format = new NestedListTextFormat[String]
    format.layOut(xterm map (_.toPretty))
  }
  
  class ExactMatch(val pattern: Term) {
    def matchInclTypes(symbol1: Identifier, symbol2: Identifier, rebinds: Map[Identifier, Identifier]): Boolean = 
      rebinds.getOrElse(symbol1, symbol1) == symbol2
    
    def matchInclTypes(term1: Term, term2: Term, rebinds: Map[Identifier, Identifier]=Map())(implicit env: Environment): Boolean = {
      if      (term1 =~ (":", 2)) matchInclTypes(term1.subtrees(1), term2, rebinds)
      else if (term2 =~ (":", 2)) matchInclTypes(term1, term2.subtrees(1), rebinds)
      else if (matchInclTypes(term1.root, term2.root, rebinds) && env.typeOf(term1) == env.typeOf(term2) &&
        (term1.subtrees.length == term2.subtrees.length)) {
        val rebinds0 = rebinds ++ (if (term1 =~ ("↦", 2)) Map(term1.subtrees(0).leaf -> term2.subtrees(0).leaf) else Map())
        (term1.subtrees zip term2.subtrees forall { case (x,y) => matchInclTypes(x, y, rebinds0) })
      }
      else false
    }
    
    def find(term: Term)(implicit env: Environment=Environment.Empty) =
      term.nodes filter (matchInclTypes(pattern, _))
  }
  
  class Matched(val subterm: Term, val groups: Map[Identifier, Term]) {
    override def toString = subterm.toString
    def toPretty = 
      if (groups.isEmpty) subterm.toPretty
      else s"${subterm.toPretty} 〔${groups map {case(x,y)=>s"$x=${y.toPretty}"} mkString ", "}〕"
      
    def apply(label: Identifier) = groups get label getOrElse
      { throw new Exception(s"no matched label '$label' (in ${toPretty})") }
    def apply(label: Term): Term = apply(label.leaf)
    def apply(label: Any) = groups find (_._1 == label) map (_._2) getOrElse 
      { throw new Exception(s"no matched label '$label' (in ${toPretty})") }
  }
    
  class SimplePattern(val pattern: Term) {
      
    def find(term: Term) = {
      term.nodes collect { n => simpleMatch(pattern, n, true) match {
        case Some(x) => new Matched(n, x)
      }}
    }
      
    def simpleMatch(pattern: Term, term: Term, top: Boolean=false): Option[Map[Identifier, Term]] = {
      if      (pattern =~ (":", 2)) simpleMatch(pattern.subtrees(1), term, top) map (_ + (key(pattern) -> term))
      else if (term =~ (":", 2) && !top) simpleMatch(pattern, term.subtrees(1))
      else if (term =~ ("::", 2) && !top) simpleMatch(pattern, term.subtrees(0))
      else if (pattern =~ ("?", 0)) Some(Map())
      else if (pattern.root.literal == term.root.literal) {
        if (pattern.subtrees == List(`...`)) 
          Some(Map())
        else if (pattern.subtrees.length == term.subtrees.length) {
          val sub = pattern.subtrees zip term.subtrees map { case (x,y) => simpleMatch(x,y) }
          val init: Option[Map[Identifier, Term]] = Some(Map())
          (init /: sub){
            case (Some(m1), Some(m2)) => Some(m1 ++ m2)
            case _ => None
          }
        }
        else None
      }
      else None
    }
    
    def key(pattern: Term) = {
      /**/ assume(pattern =~ (":", 2)) /**/
      pattern.subtrees(0).leaf
    }
  }
  
  object SimplePattern {
    def apply(pattern: Term) = new SimplePattern(pattern)
  }
  
  class Rewrite(val from: Term, val to: Term) {
    private val ematch = new ExactMatch(from)
    def apply(term: Term)(implicit env: Environment=Environment.Empty) = {
      for (s <- ematch find term) yield TypeInference.infer(TypedLambdaCalculus.replaceDescendant(term, (s, subst)))(env.scope)._2
    }
    def subst = Binding.prebind(to)
  }
  
  object Rewrite {
    def apply(from: Term, to: Term) = new Rewrite(from, to)
    def apply(equation: Term) = {
      if (equation =~ ("=", 2)) new Rewrite(equation.subtrees(0), equation.subtrees(1))
      else throw new Exception(s"expected an equation of the form 'from = to', got '${equation toPretty}")
    }
  }
  
  
  import syntax.transform.Extrude
  import TypedLambdaCalculus.pullOut
  import synth.pods.{MinDistribPod,SlicePod}
  
  
  def proveEquality(lhs: Term, rhs: Term, typedecl: Map[Identifier, Term])(implicit env: Environment) = {
    val termb = new TermBreak(env)
    val (lhs_id, lhs_t) = termb(lhs)
    val (rhs_id, rhs_t) = termb(rhs)
    val assumptions = lhs_t ++ rhs_t
    val goals = List(lhs_id =:= rhs_id)
    val reflect = new Reflection(env, typedecl)
    val symbols = typedecl.keys ++ termb.intermediates
    reflect.currying ++= symbols filter (x => Reflection.isFuncType(env.typeOf_!(x))) map 
                                        (symbol => (symbol, reflect.overload(symbol))) toMap
                                        
    reflect.solve(assumptions, goals)
  }
  
  
  def main(args: Array[String]): Unit = {
    import examples.Paren.{J,K0,K1,K2}
    import semantics.Domains._
    import semantics.Prelude._
    
    val L0 = TS("L₀")
    val L1 = TS("L₁")
    val L2 = TS("L₂")
    val L3 = TS("L₃")
    val L4 = TS("L₄")
    val L5 = TS("L₅")
    
    implicit val scope = new Scope
    scope.sorts.declare(J)
    scope.sorts.declare(K0 :<: J)
    scope.sorts.declare(K1 :<: J)
    scope.sorts.declare(K2 :<: J)
    scope.sorts.declare(L0 :<: K0)
    scope.sorts.declare(L1 :<: K0)
    scope.sorts.declare(L2 :<: K1)
    scope.sorts.declare(L3 :<: K1)
    scope.sorts.declare(L4 :<: K2)
    scope.sorts.declare(L5 :<: K2)
    scope.sorts.declare(R)
    
    implicit val env = new Environment(scope, Map())
    
    def instantiate(term: Term, vassign: Map[Identifier, Term]=Map()) = {
      println("-" * 60)
      println(" <> " + term.toPretty)
      println("-" * 60)
      TypeInference.infer(Binding.prebind(term), vassign)
    }
    
    val (vassign, tC) = instantiate(CPod.apply(K0, K1, K2))
    val C = tC
    
    display(C)
    
    println(s"C  ===  ${C toPretty}")
    
    import examples.Paren.{i,k,j}
    val * = TI("*")
    
    val extrude = Extrude(Set(I("/"), cons.root))
    
    // Slice  ( k ↦ ? )  [L2, L3]
    for (kf <- SimplePattern(k ↦ ?) find C) {
      val (vassign1, slicekf) = instantiate(SlicePod(kf.subterm, List(L2, L3)), vassign)
      for ((k,v) <- vassign1)
        println(s"$k   $v")
      val env1 = TypeTranslation.decl(scope, vassign1)
      //proveEquality(slicekf.subtrees(0), slicekf.subtrees(1), vassign1)(env1)//Map())
      
      for (C <- Rewrite(slicekf)(C)) {
        println(s"C  ===  ${C toPretty}")
        // MinDistrib  ( min  /(...) )
        for (smallkfs <- SimplePattern(min :@ (* :- /::(`...`))) find C) {
          val (_, mindistkfs) = instantiate(MinDistribPod(smallkfs(*).split), vassign)
          for (C <- Rewrite(mindistkfs)(C)) {
            println(s"C  ===  ${C toPretty}")
            // Slice  ( i ↦ ? )  [L0xL4, L0xL5, L1xL4, L1xL5]
            for (if_ <- SimplePattern(i ↦ ?) find C) {
              val (_, sliceif) = instantiate(SlicePod(if_.subterm, List(L0 x L4, L0 x L5, L1 x L4, L1 x L5)), vassign)
              for (C <- Rewrite(sliceif)(C)) {
                println(s"C  ===  ${C toPretty}")
                display(extrude(C))
                for (kf <- SimplePattern(min :@ (k ↦ ?)) find C; x <- pullOut(C, kf.subterm)) {
                  println(s"${x toPretty}")
                  //display(x)
                }
              }
              //display(tC :/ "C")
            }
          }
        }
      }
    }
    
    
  }
  
  
}