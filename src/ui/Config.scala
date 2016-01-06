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
    val debug: ScallopOption[Boolean]
    val debugOnly: ScallopOption[Boolean]
    val dryRun: ScallopOption[Boolean]
    val filename: ScallopOption[String]
    
    def file() = new File(filename())
  }
  
  abstract class BaseCommandLineConfig(args: List[String]) extends ScallopConf(args toList) with CommandLineConfig {
    val prover = opt[String]("prover", default=Some("z3"))
    val cert = opt[String]("cert", default=Some("Synth")).map((_.split(",").toList))
    val log = opt[String]("log", default=Some("none")).map((_.split(",").toList))
    val tmpdir = opt[String]("tmpdir", default=Some("/tmp")).map(new File(_))
    val opt = toggle("opt", default=Some(true))
    val cache = toggle("cache", default=Some(true))
    // @@@ should only be in CLIConfig
    val debug = opt[Boolean]("debug", default=Some(false))
    val debugOnly = opt[Boolean]("debug-only", default=Some(false))
    val dryRun = opt[Boolean]("dry-run", default=Some(false))
  }
  
  class CLIConfig(args: List[String]) extends BaseCommandLineConfig(args) {
    val filename = trailArg[String](required=false, default=Some("-"))
  }

  class TAEConfig(args: List[String]) extends BaseCommandLineConfig(args) {
    val filename = trailArg[String](required=false, default=Some("/tmp/synopsis.json"))
  }
  
  def apply(cfg: CommandLineConfig) { Sources.commandLine = Some(cfg); }
  def tae(args: Array[String]) = { apply(new TAEConfig(args toList)); }
  
  lazy val config = Sources.commandLine getOrElse { new CLIConfig(List.empty) };
}