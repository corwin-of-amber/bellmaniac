package report.data

import java.io._
import collection.JavaConversions._

import com.mongodb.DBObject
import com.mongodb.util.JSON

import syntax.AstSugar._
import syntax.Formula



class Cached(file: File) extends Map[String, Map[String, Term]] {

  def this(filename: String) = this(new File(filename))

  val store : Map[String, Map[String, Term]] = try {
    implicit val cc = new SerializationContainer {}
    JSON.parse(new BufferedReader(new FileReader(file)).readLine()) match {
      case d: DBObject =>
        d.toMap collect { case (k: String, v: DBObject) =>
          k -> (v.toMap collect { case(k: String, v: DBObject) =>
            k -> Formula.fromJson(v) } toMap) } toMap
      case _ => Map()
    }
  } catch { case e: FileNotFoundException => Map() }

  def save(pair: (String, Map[String, Term])) = {
    implicit val cc = new SerializationContainer {}
    val cachef = new FileWriter(file)
    cachef.write(JSON.serialize( cc.map((store + pair) mapValues (x => cc.map(x))) ))
    cachef.close()
  }

  override def get(key: String) = store.get(key)

  // currently unimplemented
  override def +[B1 >: Map[String, Term]](kv: (String, B1)) = ???
  override def iterator = ???
  override def -(key: String) = ???
}
