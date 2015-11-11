package report.data

import java.io._
import collection.JavaConversions._
import collection.mutable

import com.mongodb.DBObject
import com.mongodb.util.JSON

import syntax.AstSugar._
import syntax.Formula



class Cached(file: File) extends mutable.Map[String, Map[String, Term]] {

  def this(filename: String) = this(new File(filename))

  val store : mutable.Map[String, Map[String, Term]] = try {
    implicit val cc = new SerializationContainer {}
    JSON.parse(new BufferedReader(new FileReader(file)).readLine()) match {
      case d: DBObject =>
        d.toMap collect { case (k: String, v: DBObject) =>
          k -> (v.toMap collect { case(k: String, v: DBObject) =>
            k -> Formula.fromJson(v) } toMap ) }
      case _ => mutable.Map.empty
    }
  } catch { case e: FileNotFoundException => mutable.Map.empty }

  def save() = {
    implicit val cc = new SerializationContainer {}
    val cachef = new FileWriter(file)
    cachef.write(JSON.serialize( cc.map(store mapValues (x => cc.map(x)) toMap) ))
    cachef.close()
  }

  override def get(key: String) = store.get(key)
  override def +=(kv: (String, Map[String, Term])) = { store += kv ; save() ; this }

  // currently unimplemented
  override def +[B1 >: Map[String, Term]](kv: (String, B1)) = ???
  override def iterator = ???
  override def -(key: String) = ???
  override def -=(key: String) = ???
}
