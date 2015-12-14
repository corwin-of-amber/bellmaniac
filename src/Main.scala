

import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.FileReader
import ui.CLI
import com.mongodb.util.JSON
import com.mongodb.BasicDBObject
import report.data.DisplayContainer
import syntax.Formula
import syntax.AstSugar._

abstract class Term
case class Var(name: String) extends Term
case class Fun(arg: String, body: Term) extends Term
case class App(f: Term, v: Term) extends Term

object Main {
  implicit val cc = new DisplayContainer
  
  def main(args: Array[String]) {
    ui.Config(new ui.Config.CLIConfig(args toList))
    val filename = ui.Config.config.filename()
    val f = new BufferedReader(
      if (filename == "-") new InputStreamReader(System.in) else new FileReader(filename))

    val blocks = CLI.getBlocks(f)
    for (block <- blocks){
      val json = JSON.parse(block).asInstanceOf[BasicDBObject]
      val prg = json.get("term")
      if (prg != null){
        val ff = Formula.fromJson(prg.asInstanceOf[BasicDBObject])
        println(s"The program is: ${ff.toPretty}")
        
      }
      else{
        println(s"The program is: null")
      }
    }
  }
}