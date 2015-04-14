package synth.tactics

import syntax.Identifier
import syntax.AstSugar._
import semantics.Scope
import semantics.FunctionType
import semantics.TypedTerm
import semantics.TypeTranslation
import semantics.TypeTranslation.Environment
import semantics.TypeTranslation.TypedIdentifier
import semantics.Reflection
import semantics.TypePrimitives
import syntax.transform.TreeSubstitution
import synth.pods.NilPod
import synth.pods.NatPod
import synth.pods.ConsPod
import semantics.TypedLambdaCalculus
import synth.pods.MinPod
import semantics.pattern.MacroMap
import synth.pods.TotalOrderPod



object Split {

  import semantics.Domains._
  import semantics.Prelude._
  import semantics.TermTranslation.TermBreak
  import semantics.UntypedTerm

  
  def main(args: Array[String]): Unit = {
    import examples.Paren._
    implicit val scope = new Scope
    
    val N = T(S("N"))
    
    scope.sorts.declare(N.root)
    scope.sorts.declare(J.root)
    scope.sorts.declare(R.root)
    scope.sorts.declare(J0.root :<: J.root)
    scope.sorts.declare(J1.root :<: J.root)

    val y = TV("y")
    val g = TV("g")
    val h = TV("h")
    
    import NatPod.{_0,_1,z,nz,s,p}
    
    val prenv = (TypeTranslation.subsorts(scope) where (compl(J)(J0, J1)))
    val typedecl = Map(
        i ~> J,
        g ~> (J0 -> R),
        h ~> (J1 -> R),
        x ~> R, y ~> R)
        
    implicit val env = prenv ++ TypeTranslation.decl(scope, typedecl)
    
    val termb = new TermBreak(env)
    
    //val assumptions = cons_t
    //val goals = List()
    
    val nilNR = NilPod(N, R)
    val consR = ConsPod(R)
    val toR = TotalOrderPod(R)
    val minNR = MinPod(N, R, toR.<)
    val minJR = MinPod(J, R, toR.<)
    
    def liftedOrElse[A,B,C](m1: Map[A, B => Option[C]], m2: Map[A, B => Option[C]]) = {
      m1 ++ (m2 map { case(k,v2) =>
          m1 get k match {
            case Some(v1) => (k, { (b: B) => v1(b) orElse { v2(b) } })
            case _ => (k, v2)
          }
        })
    }
    
    val mac = nilNR.macros ++ consR.macros ++ minNR.macros ++ minJR.macros
    def expand(term: Term): Term = {
      val eterm = TypedTerm.preserve(term, T(term.root, term.subtrees map expand))
      def head(term: Term): Identifier = if (term =~ ("@", 2)) head(term.subtrees(0)) else term.root
      mac get head(eterm) flatMap (_(eterm)) match {
       case Some(newTerm) => newTerm
       case _ => eterm
      }
    }
    
    import semantics.Binding
    import semantics.TypeInference
    import syntax.Unify
    
    import java.util.logging.Level
    //TypeInference.log.setLevel(Level.INFO)
    
    def e(term: Term) = expand(TypeInference.infer(Binding.prebind(term), typedecl)._2)
    def be(term: Term) = termb({ val x = e(term); println(x toPretty); x})

    //println(minN :@ (consM(TypedTerm(minJ :@ g, R), consM(TypedTerm(minJ :@ h, R), TypedTerm(nil, N->R)))))
    //println(e( minN :@ (consM(TypedTerm(minJ :@ g, R), consM(TypedTerm(minJ :@ h, R), TypedTerm(nil, N->R)))) ))
    
    import TypeTranslation.TypingSugar._
    
    val (mingh, mingh_t) = be(min :@ (g /: h))
    val (xy, xy_t) = be(min :@ g)
    val (xx, xx_t) = be(min :@ h)
    val (minxy, minxy_t) = 
      be( min :@ (cons :@ (TypedTerm(min :@ g, R), cons :@ (TypedTerm(min :@ h, R), TypedTerm(nil, N->R)))) )
    
    
    val decls = List(NatPod.decl, nilNR.decl, toR.decl, minNR.decl, minJR.decl)
    
    val assumptions = xx_t ++ xy_t ++ mingh_t ++ minxy_t ++ (decls flatMap (_.precondition))
    
    val goals = List(
        //((minxy =:= ming) | (minxy =:= minh)) , //↓(TypedTerm(argmin :@ g, N)),
        //(↓(< :@ ming :@ minh) & (< :@ ming :@ minh)) -> (minxy =:= ming),
        mingh =:= minxy
        )
        
    
    val symbols = typedecl.keys ++ (decls flatMap (_.symbols)) ++ termb.intermediates
    
    val reflect = new Reflection(env, typedecl)
    
    reflect.currying ++= symbols filter (x => Reflection.isFuncType(env.typeOf_!(x))) map 
                                        (symbol => (symbol, reflect.overload(symbol))) toMap

    for (variants <- reflect.currying.values)
      reflect.alwaysDefined ++= (variants dropRight 1)
                                        
    for (symbol <- symbols) {
      println(s"${T(symbol).untype} :: ${env.typeOf(symbol).get toPretty}")
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
    
  }
  
}