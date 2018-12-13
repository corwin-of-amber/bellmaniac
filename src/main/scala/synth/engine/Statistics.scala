package synth.engine

import syntax.AstSugar._
import synth.pods.Pod
import semantics.LambdaCalculus
import TacticApplicationEngine.{Instantiated, PodOrigin}
import report.data.Cached
import java.io.File
import synth.pods.ConsPod



trait CollectStats extends TacticApplicationEngine {
  import TacticApplicationEngine.State
  
  val stats = collection.mutable.ListBuffer.empty[(Term,Long)]
  
  def collectStats[X](pod: Pod, op: => X): X = pod match {
    case ipod: Instantiated[_] => collectStats(ipod.it, op)
    case opod: PodOrigin => 
      val start = System.currentTimeMillis
      def finish = System.currentTimeMillis - start
      try op finally stats += ((opod.tactic, finish))
    case _ => op
  }

  override def invokeProver(pod: Pod) { 
    collectStats(pod, super.invokeProver(pod))
  }
  
  override def invokeSynthesis(h: Term, subterm: Term, templates: List[Term], fix: Boolean)(implicit s: State) = {
    collectStats(new Pod with PodOrigin { val tactic = TV("Sketch") }, super.invokeSynthesis(h, subterm, templates, fix))
  }
  
  override def finalize(s: State) {
    super.finalize(s)
    printStats
    saveStats()
  }
  
  import report.data.Deserialize._
  lazy val statsf = new Cached[List[Int]]("stats.json")
  
  
  def byTactic = {
    import TacticApplicationEngine.L
    def nameOf(tactic: Term) = LambdaCalculus.isApp(tactic) match {
      case Some((L("SynthAuto"), _)) => "Synth"
      case Some((L(name), _)) => name
      case _ => tactic.toString
    }
    
    stats groupBy { case (tactic, _) => nameOf(tactic) }
  }
  
  def printStats {
    val avgs =
      byTactic mapValues 
        { elements => seconds( average(elements map (_._2)) ) }
    
    avgs foreach { case (tacticName, avg) => println(s"${tacticName}    ${avg}sec") }
    val table = List("Slice", "Stratify", "Synth", "Sketch")
    println(table map (x => avgs.getOrElse(x, "")) mkString "  &  ")
  }
  
  def saveStats() = {
    val key = new File( ui.Config.config.filename() ).getName
    statsf += key -> (byTactic map { case (k,v) => (k.toString, (v map (_._2.toInt) toList)) })
  }
  
  def seconds(ms: Float) = Math.round(ms / 100) / 10.0
  
  def average[B](l: Seq[B])(implicit num: Numeric[B]) = num.toFloat(l.sum) / l.length
  
}
