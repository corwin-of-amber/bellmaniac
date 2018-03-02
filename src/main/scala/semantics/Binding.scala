package semantics

import syntax.{Tree,Identifier,AstSugar}
import Scope.TypingException



object Binding {
  
  import AstSugar._

  val PREBIND_SET = new Binding(Set(I("↦"), I("∀"), I("∃")), Set())
  val BINDER_SET = PREBIND_SET ++ new Binding(Set(I(":")), Set())
  
  def prebind(program: Term) = PREBIND_SET.bind(program)
  def inline(program: Term) = BINDER_SET.inline(program)
}


class Binding(val left: Set[Identifier], val right: Set[Identifier]) {
  
  import AstSugar._

  class Binder extends Uid


  def ++(that: Binding) = new Binding(left ++ that.left, right ++ that.right)
  
  def bind(id: Identifier) = {
    val va = new Identifier(id.literal, id.kind, ns = new Binder)
    id match { case tid: TypedIdentifier => TypedIdentifier(va, tid.typ) case _ => va }
  }
  
  def bind(term: Term, bound: Map[Identifier, Identifier] = Map.empty): Term = {
    TypedTerm.preserve(term, bind0(term, bound))
  }
  
  def bind0(term: Term, bound: Map[Identifier, Identifier] = Map.empty): Term = {
    if (term.isLeaf)
      bound get term.root match {
        case Some(b) => new Tree(b)
        case _ => new Tree(term.root)
      }
    else {
      val rebind =
        if (left contains term.root)
          (term.subtrees dropRight 1) map getVarId map { va => (va -> bind(va)) }
        else if (right contains term.root) ???
        else List()
      new Tree(term.root, term.subtrees map (bind(_, bound ++ rebind)))
    }
  }
  
  private def getVarId(arg: Term) = 
    TypedLambdaCalculus.getDeclaredVariable(arg) getOrElse
    { throw new TypingException(s"not a valid binding: '$arg'") }
  
  def boundvars(term: Term): Set[Identifier] = {
    val (rebind, sub) =
      if (left contains term.root) (term.subtrees dropRight 1, List(term.subtrees.last))
      else if (right contains term.root) (term.subtrees drop 1, List(term.subtrees.head))
      else (List(), term.subtrees)
    ((rebind map getVarId) ++
        (sub map boundvars flatten)) toSet
  }
  
  def inline(definitions: List[(Term, Term)], program: Term): Term = {
    val self = (inline(definitions, _:Term))
    if (program =~ (":", 2))
      new Tree(program.root, program.subtrees(0) +: (program.subtrees drop 1 map self))
    else definitions find (program == _._1) match {
      case Some((x,y)) => self(bind(y))
      case _ => new Tree(program.root, program.subtrees map self)
    }
  }
  
  def inline(definitions: Term, program: Term): Term = {
    val labeled = definitions.nodes filter (_ =~ (":", 2)) map 
      (x => (x.subtrees(0), x.subtrees(1)))
    
    inline(labeled.toList, program)
  }
  
  def inline(program: Term): Term = inline(program, program)
  
}
