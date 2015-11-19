package ui

import org.rogach.scallop.ScallopConf
import org.rogach.scallop.ScallopOption
import java.io.File



object Config {
  object Sources {
    var commandLine: Option[CommandLineConfig] = None;
  }

  trait CommandLineConfig {
    val prover: ScallopOption[String]
    val cert: ScallopOption[List[String]]
    val log: ScallopOption[List[String]]
    val opt: ScallopOption[Boolean]
    val cache: ScallopOption[Boolean]
    val tmpdir: ScallopOption[File]
    val filename: ScallopOption[String]
  }
  
  abstract class BaseCommandLineConfig(args: List[String]) extends ScallopConf(args toList) with CommandLineConfig {
    val prover = opt[String]("prover", default=Some("z3"))
    val cert = opt[String]("cert", default=Some("Synth")).map((_.split(",").toList))
    val log = opt[String]("log", default=Some("Synth")).map((_.split(",").toList))
    val tmpdir = opt[String]("tmpdir", default=Some("/tmp")).map(new File(_))
    val opt = toggle("opt", default=Some(true))
    val cache = toggle("cache", default=Some(true))
  }
  
  class CLIConfig(args: List[String]) extends BaseCommandLineConfig(args) {
    val filename = trailArg[String](required=false, default=Some("-"))
  }

  class TAEConfig(args: List[String]) extends BaseCommandLineConfig(args) {
    val filename = trailArg[String](required=false, default=Some("/tmp/synopsis.json"))
  }
  
  def tae(args: Array[String]) = { Sources.commandLine = Some[CommandLineConfig](new TAEConfig(args.toList)) }
  
  lazy val config = Sources.commandLine getOrElse { new CLIConfig(List.empty) };
}