package synth.pods

import syntax.Identifier
import syntax.AstSugar._
import semantics.Prelude
import semantics.TypeTranslation.TypingSugar._
import semantics.TypeTranslation.TypedTerm
import semantics.TypeTranslation.Declaration
import semantics.TypeTranslation.TypedIdentifier
import semantics.pattern.SimplePattern



class NilPod(val domain: Term, val range: Term) {
  
  import Prelude.↓
  
  val nil = $TyTV(s"nil.${domain}${range}", domain -> range)
  val decl = 
      new Declaration(nil) where ∀:(domain, i => ~(↓(nil :@ i)))
      
  val NILPAT = SimplePattern(TypedTerm(Prelude.nil, domain -> range))
  val macros = Map[Identifier, Term => Option[Term]](Prelude.nil ~> { x => NILPAT(x) map (m => nil) })
}

object NilPod {
  def apply(domain: Term, range: Term) = new NilPod(domain, range)
}
