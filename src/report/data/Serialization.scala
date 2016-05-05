package report.data

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
    case l: List[_] => list(l)
    case _ => value.toString
  }
  def byRef(value: AnyRef): AnyRef = anyRef(value)
  def list[A <: Any](elements: Iterable[A]) = {
    val l = new BasicDBList
    elements map any foreach { case x: Object => l.add(x) case x => ??? }
    l
  }
  def map[A <: AnyRef](elements: Iterable[(String,A)]) = {
    (new BasicDBObject /: elements) { case (d, (k,v)) => d.append(k, anyRef(v)) }
  }
  def map[A <: AnyRef](elements: (String,A)*): BasicDBObject = map(elements)
  def flatten(jsons: Stream[DBObject]) = jsons flatMap {
    case l: BasicDBList => l map (_.asInstanceOf[DBObject])
    case item => Some(item)
  }
}


trait AsJson {
  def asJson(container: SerializationContainer): DBObject
}


trait Numerator {
  def --> (value: AnyRef): Int
  def <-- (index: Int): AnyRef
}

class DisplayContainer extends SerializationContainer with Numerator {
  import syntax.AstSugar._
  import syntax.Formula
  import semantics.{TypedTerm, Id}

  override def any(value: Any): Any = value match {
    case t: Formula.TermTag => termTag(t)
    case Term_:(t) => withRefid(t.get.asJson(this), new Id(t))
    case _ => super.any(value)
  }

  override def anyRef(value: AnyRef): AnyRef = value match {
    case Term_:(t) => withRefid(t.get.asJson(this), new Id(t))
    case _ => super.anyRef(value)
  }

  override def byRef(value: AnyRef): AnyRef = -->?(value)

  def termTag(tag: Formula.TermTag) = {
    val json = new BasicDBObject("term", -->?(tag.term))
    tag.term match {
      case typed: TypedTerm => json.append("type", typed.typ.toPretty)
      case _ => json
    }
  }

  val mapped: collection.mutable.Map[AnyRef,Int] = collection.mutable.Map.empty
  var max = 0

  def --> (value: AnyRef) = mapped get value match {
    case Some(idx) => idx
    case _ => max = max + 1 ; mapped += (value -> max) ; max
  }

  def <-- (index: Int) = mapped find (_._2 == index) match {
    case Some((ns, _)) => ns
    case _ => val ns = new Uid
      mapped += (ns -> index) ; max = Math.max(max, index) ; ns
  }

  def -->? (value: AnyRef) = mapped get value match {
    case Some(idx) => ref(any(idx))
    case _ => anyRef(value)
  }

  def ref(refid: Any) = new BasicDBObject("ref", refid)

  def withRefid(json: DBObject, value: AnyRef) = {
    max = max + 1 ; mapped += (value -> max)
    json.put("_id", max)
    json
  }
}


class SerializationError(msg: String, val obj: AnyRef) extends Exception(msg)