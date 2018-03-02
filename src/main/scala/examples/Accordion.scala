package examples

import syntax.AstSugar._
import semantics.{TypeTranslation, Scope, Prelude}
import semantics.Prelude._
import semantics.TypeTranslation.TypingSugar._
import semantics.Domains.SubsortAssocT
import semantics.pattern.SimplePattern
import synth.engine.TacticApplicationEngine
import synth.pods.Pod
import synth.proof.{Prover, Assistant}
import synth.pods.ConsPod.`⟨ ⟩`
import synth.pods.IndexArithPod
import synth.pods.TotalOrderPod
import report.data.Rich
import scala.collection.immutable.ListMap
import syntax.Scheme
import syntax.Scheme.SchemeFun
import syntax.Strip
import semantics.LambdaCalculus
import synth.engine.TacticApplicationEngine.Instantiated
import synth.engine.TacticApplicationEngine.PodOrigin
import synth.engine.CollectStats
import synth.engine.PodFactory
import semantics.TypedIdentifier
import semantics.TypedTerm
import semantics.TypeTranslation.Environment
import syntax.Identifier



object Accordion {

  val J = TS("J")
  val J0 = TS("J₀")
  val J1 = TS("J₁")
  val K0 = TS("K₀")
  val K1 = TS("K₁")
  val K2 = TS("K₂")
  val K3 = TS("K₃")
  val L0 = TS("L₀")
  val L1 = TS("L₁")
  val L2 = TS("L₂")
  val L3 = TS("L₃")
  val L4 = TS("L₄")
  val L5 = TS("L₅")

  val δ = TyTV("δ", J ->: J ->: J ->: R)

  import IndexArithPod._1
  val < = TV("<")

  case class APod(val J: Term) extends Pod {

    val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), $TV("k"))

    override val program = Prelude.program(
        ψ ↦ fix((θ ↦: i ↦: j ↦: (
            max:@ `⟨ ⟩`(
                ψ:@(i,j),
                max:@(k ↦ ((θ:@(j+_1,k)) + (δ:@(i,j,k))))
            )
        )) :: (((J x J) ∩ <) -> R) ->: (((J x J) ∩ <) -> R))
    )
  }

  case class BPod(val J0: Term, val J1: Term) extends Pod {

    val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), $TV("k"))

    override val program = Prelude.program(
        (ψ :: ((? x J1) ∩ <) ->: ?) ↦ /::(
            (i ↦: j ↦: (
              max:@ `⟨ ⟩`(
                  ψ:@(i,j),
                  max:@(k ↦ (((ψ :: (J1 x J1) ->: ?):@(j+_1,k)) + (δ:@(i,j,k))))
              ))) :: ((J0 x J1) ∩ <) ->: R,
            ψ :: ((J1 x J1) ∩ <) ->: R
        )
    )
  }

  case class CPod(val J0: Term, val J1: Term) extends Pod {

    val (ψ, θ, i, j, k) = ($TV("ψ"), $TV("θ"), $TV("i"), $TV("j"), $TV("k"))

    override val program = Prelude.program(
        (ψ :: ((J0 x ?) ∩ <) ->: ?) ↦ /::(
            ψ :: ((J0 x J1) ∩ <) ->: R,
            (i ↦: j ↦: (
              max:@ `⟨ ⟩`(
                  ψ:@(i,j),
                  max:@((k::J1) ↦ ((ψ:@(j+_1,k)) + (δ:@(i,j,k))))
              ))) :: ((J0 x J0) ∩ <) ->: R
        )
    )
  }

  case class DPod(val J0: Term, val J1: Term, val J2: Term) extends Pod {

    val (ψ, i, j, k) = ($TV("ψ"), $TV("i"), $TV("j"), $TV("k"))

    override val program = Prelude.program(
        ψ ↦ /::(
            ψ :: (J1 x J2) ->: R,
            (i ↦: j ↦: (
              max:@ `⟨ ⟩`(
                  ψ:@(i,j),
                  max:@(k ↦ (((ψ::(J1 x J2) ->: ?):@(j+_1,k)) + (δ:@(i,j,k))))
              ))) :: (J0 x J1) ->: R
        )
    )
  }


  import semantics.TypedTerm.typeOf_!

  implicit val scope = new Scope(R, N, J)(J0 :<: J, J1 :<: J,
      K0 :<: J0, K1 :<: J0, K2 :<: J1, K3 :<: J1,
      L0 :<: K0, L1 :<: K0, L2 :<: K1, L3 :<: K1, L4 :<: K2, L5 :<: K2)

  implicit val env = TypeTranslation.subsorts(scope) ++
      TypeTranslation.decl(scope, Map(δ ~> typeOf_!(δ)))



  def main(args: Array[String]): Unit = {
    ui.Config.tae(args)
    new Interpreter().executeFile(ui.Config.config.filename())
  }


  trait InvokeProver extends TacticApplicationEngine {
    override lazy val prover: Prover = prover(List(), Set(max), Set(T(I("∪", "predicate"))))

    def prover(pods: List[Pod], fv: Set[Term], ty: Set[Term], env: Environment=this.env) = {
      import synth.pods._

      def when[A](trig: Term, pods: => List[A]) =
        if (fv contains trig) pods else List()

      def when2[A,B](trig: Term, pods: => Map[A,B]) =
        if (fv contains trig) pods else Map()

      def when3[A](trig: Char, pods: => Iterable[A]) =
        if (ty exists (x => x.root.kind == "predicate" &&
            x.root.literal.toString.contains(trig))) pods else List()

      val gen = new synth.tactics.Synth.ScopeGen(scope)

      val base = List(NatPod, TuplePod)
      val totalOrders = Map(R ~> TotalOrderPod(R)) ++ (gen.masters match {
        case List() => Map()
        case List(j) => Map(j -> TotalOrderPod(T(j), <))   // single master sort
        case l =>                                     // more than one master sort
          l.zipWithIndex map { case (sort, idx) =>  // yeah kind of a hack :\
            sort -> TotalOrderPod(T(sort), TV(Strip.subscriptIndexed("<")(idx+1)))
          }
      })
      val indexAriths = gen.masters map (sort => sort -> IndexArithPod(T(sort), totalOrders(sort).<)) toMap
      val parts = gen.partitions map { case (sup, sub1, sub2) =>
        val m = scope.sorts.getMasterOf(sup)
        PartitionPod(T(sup), totalOrders(m).<, T(sub1), T(sub2))
      } toList
      val maxes = when2(max, (List(N.leaf) ++ gen.masters) map (sort => sort -> MaxPod(T(sort), R, totalOrders(R.leaf).<)) toMap)
      val mins = when2(min, (List(N.leaf) ++ gen.masters) map (sort => sort -> MinPod(T(sort), R, totalOrders(R.leaf).<)) toMap)
      val offsets = when3('∪', gen.sortsByMaster flatMap { case (master, subsorts) =>
        subsorts filterNot (_ == master) map (x => OffsetsPod(T(x), indexAriths(master)))
      })

      val allPods = base ++ totalOrders.values ++ indexAriths.values ++ parts ++ maxes.values ++ mins.values ++ offsets toList

      new Prover(allPods ++ pods, Prover.Verbosity.ResultsOnly)(env)
      /*
      val toR = TotalOrderPod(R)
      val toJ = TotalOrderPod(J, <)
      val idxJ = IndexArithPod(J, toJ.<)
      val partJ = PartitionPod(J, toJ.<, J0, J1)
      val partJ0 = PartitionPod(J0, toJ.<, K0, K1)
      val partJ1 = PartitionPod(J1, toJ.<, K2, K3)
      val partK0 = PartitionPod(K0, toJ.<, L0, L1)
      val partK1 = PartitionPod(K1, toJ.<, L2, L3)
      val partK2 = PartitionPod(K2, toJ.<, L4, L5)
      val maxJR = MaxPod(J, R, toR.<)
      val maxNR = MaxPod(N, R, toR.<)

      new Prover(List(NatPod, TuplePod, toR, toJ, idxJ, partJ, partJ0, partJ1, partK0, partK1, partK2, maxJR, maxNR) ++ pods, Prover.Verbosity.ResultsOnly)
      */
    }

    def mkEnv(fv: Iterable[Term]) = {
      val decls = fv flatMap { v => TypedTerm.typeOf(v) map (v ~> _) } toMap;
      val declKeys = List(V("δ"), V("succ"))  // @@@
      TypeTranslation.decl(scope, declKeys flatMap (δ => decls.get(δ) map (δ -> _)) toMap)
    }

    def collectTypes(term: Term) =
      term.nodes flatMap { v => TypedTerm.typeOf(v).toSeq flatMap (_.leaves) } toSet

    override def prover(program: Term) = {
      val fv = LambdaCalculus.freevars(program)
      val ty = collectTypes(program)
      implicit val env = this.env ++ mkEnv(fv)
      prover(List(), fv, ty, env)
    }

    def invokeProver(assumptions: List[Term], goals: List[Term], pods: List[Pod]=List()) {
      val fv = goals flatMap LambdaCalculus.freevars toSet
      val ty = goals flatMap collectTypes toSet
      implicit val env = this.env ++ mkEnv(fv)
      (new Assistant()).invokeProver(assumptions, goals, SimplePattern(min :@ ?, max :@ ?))(prover(pods, fv, ty, env))
    }

    override def invokeProver(pod: Pod) {
      invokeProver(List(), pod.obligations.conjuncts, List(pod))
    }
  }

  class Interpreter(implicit scope: Scope) extends TacticApplicationEngine with PodFactory with InvokeProver with CollectStats {
    import TacticApplicationEngine._
    import syntax.Subroutine
    import syntax.Subroutine.Arity

    def fac: Map[Any,Subroutine[Term,Pod] with Arity] = ListMap(
        "A" -> Subroutine(APod),
        "B" -> Subroutine(BPod),
        "C" -> Subroutine(CPod),
        "D" -> Subroutine(DPod))
  }

}
