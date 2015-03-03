package synth.tactics

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



object Rewrite {
  
  object SlicePod {
    import Prelude.?
    
    def apply(f: TypedTerm, subdomains: List[Term])(implicit scope: Scope) = {
      //val emit = TypeTranslation.emit(scope, f.typ)
      //val slices = subdomains map (subdomain =>
      //  TypeTranslation.canonical(scope, TypeTranslation.emit(scope, subdomain, TypeTranslation.InOut.IN) ++ emit.tail))
      val slices = subdomains map (_ -> ?)
      println(slices)
      f =:= /::(slices map (f :: _) toList)
    }
    
  }
  
  object MinDistribPod {
    import Prelude.{min,cons,nil}
    
    def apply(fs: List[Term])(implicit scope: Scope) = {
      (min :@ (/::(fs))) =:= (min :@ (((fs map (min :@ _)) :\ nil)(cons :@ _ :@ _)))
    }
  }
  
  object CPod {
    import examples.Paren.{J,R}
    import semantics.Prelude._
    
    def apply(J0: Term, J1: Term, J2: Term) = {
      val C = $TV("C")
      val P = $TV("P")
      val (θ, i, j, k) = ($TV("θ"), $TV("i"), $TV("j"), $TV("k"))
      val (item, compute) = ($TV("item"), $TV("compute"))
      TV("program")(
          P :: ((J x J) -> B),
          C :- ((θ ↦ (i ↦ (j ↦ (min :@ (k ↦ ( item :- (θ :@ i :@ k) ))))))
           :: ((((J x J) ∩ P) -> R) ->: J0 ->: J2 ->: R))
      )
    }
  }
  
  def display(term: Term)(implicit env: Environment) {
    val format = new NestedListTextFormat[Identifier]
    format.layOutAndAnnotate(term, (env.typeOf(_) map (_.toPretty)), (_.toPretty))
  }
  
  def matchInclTypes(symbol1: Identifier, symbol2: Identifier, rebinds: Map[Identifier, Identifier]): Boolean = 
    rebinds.getOrElse(symbol1, symbol1) == symbol2
  
  def matchInclTypes(term1: Term, term2: Term, rebinds: Map[Identifier, Identifier]=Map())(implicit env: Environment): Boolean = 
    if      (term1 =~ (":", 2)) matchInclTypes(term1.subtrees(1), term2, rebinds)
    else if (term2 =~ (":", 2)) matchInclTypes(term1, term2.subtrees(1), rebinds)
    else if (matchInclTypes(term1.root, term2.root, rebinds) && env.typeOf(term1) == env.typeOf(term2) &&
      (term1.subtrees.length == term2.subtrees.length)) {
      val rebinds0 = rebinds ++ (if (term1 =~ ("↦", 2)) Map(term1.subtrees(0).leaf -> term2.subtrees(0).leaf) else Map())
      (term1.subtrees zip term2.subtrees forall { case (x,y) => matchInclTypes(x, y, rebinds0) })
    }
    else false

  def main(args: Array[String]): Unit = {
    import examples.Paren.{R,J,K0,K1,K2}
    import semantics.Domains._
    import semantics.Prelude._
    
    val L2 = TS("L₂") //₀₁₂₃₄₅
    val L3 = TS("L₃")
    
    implicit val scope = new Scope
    scope.sorts.declare(J)
    scope.sorts.declare(K0 :<: J)
    scope.sorts.declare(K1 :<: J)
    scope.sorts.declare(K2 :<: J)
    scope.sorts.declare(L2 :<: K1)
    scope.sorts.declare(L3 :<: K1)
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
    
    println(C.toPretty)
    
    val kf = C.nodes find (x => x =~ ("↦", 2) && x.subtrees(0) =~ ("k", 0)) get

    val (_, slicekf) = instantiate(SlicePod(kf.asInstanceOf[TypedTerm], List(L2, L3)), vassign)
    display(C)
    display(slicekf.subtrees(0))
    println(slicekf toPretty)

    val matches = (C.nodes filter (matchInclTypes(_, slicekf.subtrees(0))))
    for (m <- matches; C <- Some(C.replaceDescendant((m, slicekf.subtrees(1))))) {
      println(C.toPretty)
      
      val smallkfs = C.nodes find (x => x =~ ("@", 2) && x.subtrees(0) =~ ("min", 0) && x.subtrees(1).root == "/") get

      val (_, mindistkf) = instantiate(MinDistribPod(smallkfs.subtrees(1).unfold.subtrees), vassign)
      display(mindistkf)
      println(mindistkf toPretty)
    }
    
    
  }
  
  
}