import java.nio.file.Files
import java.nio.file.Paths
import java.nio.file.StandardCopyOption

trait Logger {
  // throw on exception on error
  var STRICT = true

  // print an important message
  def message(s: => String) = {
    print(Console.RED)
    println(s)
    print(Console.RESET)
  }

  // print an error
  def error(s: => String) = { 
    val elts = Thread.currentThread().getStackTrace()
    var caller = elts(3)
    message("Error occurred in " + caller.getMethodName + " at " + caller.getLineNumber)
    println(s)
    message("End of error message")
    if (STRICT)
      throw new RuntimeException("strict mode")
    null
  }
  
  def print(s: => Any) = Console.out.print(s.toString)
  def println(s: => Any) = Console.out.println(s.toString)
}

object GraphViz {
  type Graph[V, L] = List[(V, L, V)]
  import java.io.{PrintStream, File}

  val DOT_OUTPUT_FMT = "pdf"
  
  private val filext = DOT_OUTPUT_FMT;
  private val dotflags = f"-T$DOT_OUTPUT_FMT"
  
  def clean(s: Any) = 
    s.toString.replace("\n", "\\l").replace("\"", "'") + "\\l"

  def write[V, L](g: Graph[V, L], out: PrintStream) {
    out println  "digraph tmp {";    
    out println  "  node [shape=box] "
   
    for ((from, l, to) <-g)
      out.println("\"" + clean(from) + "\"->\"" + clean(to) + "\" [label=\"" + clean(l) +"\"]");
    out println "}";
  }

  private[this] def makeTempDot = {
    // write to a file
    val f = File.createTempFile("graph", ".dot");
    f.deleteOnExit;
    println("created dot file " + f.getAbsolutePath)
    f;
  }

  private[this] def executeDot(in: File) = {
    // render to a file (according to select format DOT_OUTPUT_FORMAT)
    val out = File.createTempFile("graph", f".$filext");
    out.deleteOnExit;
    val dot = Runtime.getRuntime.exec(f"dot $dotflags -o ${out.getAbsolutePath} ${in.getAbsolutePath}");
    
    if (dot.waitFor != 0)
      println("dot failed to process: " + in.getAbsolutePath);    
    
    out
  }

  private[this] def showDot(out: File) {
    val open = f"/tmp/open.$filext";
    Files.copy(out.toPath, Paths.get(open), StandardCopyOption.REPLACE_EXISTING)
    Runtime.getRuntime.exec(f"open $open"); // + out.getAbsolutePath);
  }

  def createDot[V, L](g: Graph[V, L]) = {
    val f = makeTempDot;
    val out = new PrintStream(f);
    write(g, out);
    out.flush;
    executeDot(f);
  }

  def display[V, L](g: Graph[V, L]) {
    val f = createDot(g);
    showDot(f);
  }
}

