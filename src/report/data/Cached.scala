package report.data

import java.io._
import collection.JavaConversions._
import collection.mutable
import com.mongodb.DBObject
import com.mongodb.util.JSON
import syntax.AstSugar._
import syntax.Formula
import com.mongodb.BasicDBList



trait FromJson[A] { def fromJson(json: DBObject)(implicit container: SerializationContainer): A }

object Deserialize {
  implicit object FormulaFromJson extends FromJson[Term] {
    def fromJson(json: DBObject)(implicit container: SerializationContainer) = Formula.fromJson(json)
  }
  implicit object ListFromJson extends FromJson[List[Int]] {
    def fromJson(json: DBObject)(implicit container: SerializationContainer) = json match {
      case l: BasicDBList => try l map (_.asInstanceOf[Int]) toList catch { case _: Throwable => throw new SerializationError("not a number", l) }
      case _ => throw new SerializationError("cannot deserialize non-list", json)
    }
  }
}

class Cached[A <: AnyRef](file: File)(implicit ds: FromJson[A]) extends mutable.Map[String, Map[String, A]] {

  def this(filename: String)(implicit ds: FromJson[A]) = this(new File(filename))

  val store : mutable.Map[String, Map[String, A]] = try {
    implicit val cc = new SerializationContainer {}
    JSON.parse(new BufferedReader(new FileReader(file)).readLine()) match {
      case d: DBObject =>
        d.toMap collect { case (k: String, v: DBObject) =>
          k -> (v.toMap collect { case(k: String, v: DBObject) =>
            k -> ds.fromJson(v) } toMap ) }
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
  override def +=(kv: (String, Map[String, A])) = { store += kv ; save() ; this }

  // currently unimplemented
  override def +[B1 >: Map[String, A]](kv: (String, B1)) = ???
  override def iterator = ???
  override def -(key: String) = ???
  override def -=(key: String) = ???
}
