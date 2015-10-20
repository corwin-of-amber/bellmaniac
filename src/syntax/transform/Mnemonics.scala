package syntax.transform

import syntax.Identifier


/**
 * A helper class used to assign valid tokens to identifiers when translating
 * terms to some output formats (e.g., SMTLIB, Sketch).
 */
class Mnemonics {

  val mnemonics = new collection.mutable.HashMap[Identifier, String]

  /**
   * Gets a string mnemonic for this identifier; makes sure distinct
   * identifiers get distinct mnemonics (even if they have the same
   * literal).
   */
  def get(id: Identifier) = mnemonics get id match {
    case Some(x) => x
    case _ =>
      val lit = normalize(id)
      val newMne = (lit #:: (nat map (lit + _))) find (x => ! mnemonics.exists (_._2 == x)) get ;
      mnemonics += id -> newMne
      newMne
  }

  def release(ids: Iterable[Identifier]) = mnemonics --= ids
  def --=(ids: Iterable[Identifier]) = mnemonics --= ids

  def normalize(id: Identifier): String = normalize(id.literal.toString)

  def normalize(s: String) = {
    val esc = s map { c =>
      if (isIdentifierPart(c)) c
      else ESC getOrElse (c, "_")
    } mkString ;
    if (esc.length > 0 && isIdentifierStart(esc.charAt(0))) esc
    else "_" + esc
  }

  def isIdentifierPart(c: Character) = Character.isJavaIdentifierPart(c)
  def isIdentifierStart(c: Character) = Character.isJavaIdentifierStart(c)

  val ESC = Map('<' -> "lt", '+' -> "plus", '-' -> "minus", '@' -> "apply",
                'ψ' -> "psi", 'θ' -> "theta",
                '₀' -> "0", '₁' -> "1", '₂' -> "2", '₃' -> "3", '₄' -> "4", '₅' -> "5",
                '₆' -> "6", '₇' -> "7", '₈' -> "8", '₉' -> "9")

  /**
   * just the stream of naturals (taken from Scala docs)
   */
  def nat = {
    def loop(v: Int): Stream[Int] = v #:: loop(v + 1)
    loop(0)
  }
}
