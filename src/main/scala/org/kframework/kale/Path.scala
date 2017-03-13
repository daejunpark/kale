package org.kframework.kale


/**
  * works only for non-comm
  */
case class Path(positions: Seq[Int]) {
  /**
    * Returns the subterm of t at the current Path position
    */
  def apply(t: Term): Term = positions match {
    case head :: tail =>
      val elements = t.label match {
        case label: AssocLabel => label.asList(t).toSeq
        case _ => t.iterator().toSeq
      }
      Path(tail)(elements(positions.head))
    case Nil => t
  }
}
