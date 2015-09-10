package report.data

import semantics.TypedTerm
import syntax.Formula

import collection.JavaConversions._
import com.mongodb.{BasicDBObject, BasicDBList, DBObject}



trait SerializationContainer {
  def any(value: Any): Any = value match {
    case j: AsJson => j.asJson(this)
    case i: Int => i
    case s: String => s
    case o: DBObject => o
    case _ => value.toString
  }
  def anyRef(value: AnyRef): AnyRef = value match {
    case j: AsJson => j.asJson(this)
    case s: String => s
    case o: DBObject => o
    case _ => value.toString
  }
  def list[A <: AnyRef](elements: Iterable[A]) = {
    val l = new BasicDBList
    l.addAll(elements map anyRef)
    l
  }
}


trait AsJson {
  def asJson(container: SerializationContainer): DBObject
}


trait Numerator {
  def --> (value: Any): Int
  def <-- (index: Int): Any
}

class DisplayContainer extends SerializationContainer with Numerator {
  import syntax.AstSugar._

  override def any(value: Any): Any = value match {
    case t: Formula.TermTag =>
      val tag = new BasicDBObject("term", any(t.term))
      t.term match {
        case typed: TypedTerm => tag.append("type", typed.typ.toPretty)
        case _ => tag
      }
    case _ => super.any(value)
  }

  val mapped: collection.mutable.Map[Any,Int] = collection.mutable.Map.empty
  var max = 0

  def --> (value: Any) = mapped get value match {
    case Some(idx) => idx
    case _ => max = max + 1 ; mapped += (value -> max) ; max
  }

  def <-- (index: Int) = mapped find (_._2 == index) match {
    case Some((ns, _)) => ns
    case _ => val ns = new Uid
      mapped += (ns -> index) ; max = Math.max(max, index) ; ns
  }
}