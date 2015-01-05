
package semantics.smt

import scala.collection.mutable.HashMap
import com.microsoft.z3.Expr

import syntax.Identifier



class Z3Gate {
  
  val declarations = new HashMap[Identifier, Expr]
  
}