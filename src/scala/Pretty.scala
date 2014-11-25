/*
 * A simple pretty printer
 *
 * The alogithm is by Lawrence C. Paulson, who simplified an algorithm
 * by Derek C. Oppen.
 *
 * Derek C. Oppen, Prettyprinting, ACM Transactions on Programming
 * Languages and Systems, Vol 2, No. 4, October 1980, Pages 465-483.
 *
 * Copyright (c) 2010 The MITRE Corporation
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the BSD License as published by the University
 * of California.
 */

/* A pretty printer based on ML programs with the following copyright

(**** ML Programs from Chapter 8 of

  ML for the Working Programmer, 2nd edition
  by Lawrence C. Paulson, Computer Laboratory, University of Cambridge.
  (Cambridge University Press, 1996)

Copyright (C) 1996 by Cambridge University Press.
Permission to copy without fee is granted provided that this copyright
notice and the DISCLAIMER OF WARRANTY are included in any copy.

DISCLAIMER OF WARRANTY.  These programs are provided `as is' without
warranty of any kind.  We make no warranties, express or implied, that the
programs are free of error, or are consistent with any particular standard
of merchantability, or that they will meet your requirements for any
particular application.  They should not be relied upon for solving a
problem whose incorrect solution could result in injury to a person or loss
of property.  If you do use the programs or functions in such a manner, it
is at your own risk.  The author and publisher disclaim all liability for
direct, incidental or consequential damages resulting from your use of
these programs or functions.
****)

*/

package cpsaextras

import java.io.PrintWriter

/** Abstract data type for pretty printing. */
sealed abstract class Pretty
private case class Str(s: String) extends Pretty
private case class Brk(n: Int) extends Pretty
private case class Blo(l: List[Pretty], indent: Int, n: Int) extends Pretty
private case class Grp(l: List[Pretty], indent: Int, n: Int) extends Pretty

object Pretty {
  // Exported constructors

  /** Create a string.
   * @param s string to be printed
   */
  def str(s: String): Pretty = {
    Str(s)
  }

  /** Create a break point.
   * @param n number of spaces
   */
  def brk(n: Int): Pretty = {
    Brk(n)
  }

  /** Create an indentation block.  When pretty printing, any of the
   * break points in the list can be used.
   * @param indent number of spaces to indent
   * @param es a list that includes break points
   */
  def blo(indent: Int, es: List[Pretty]): Pretty = {
    Blo(es, indent, len(es, 0))
  }

  /** Create an indentation group.  When pretty printing,
   * either all or none of the break points are used.
   * @param indent number of spaces to indent
   * @param es a list that includes break points
   */
  def grp(indent: Int, es: List[Pretty]): Pretty = {
    Grp(es, indent, len(es, 0))
  }

  private def len(es: List[Pretty], n: Int): Int = {
    es match {
      case Nil => n
      case e :: es => len(es, size(e) + n)
    }
  }

  private def size(e: Pretty): Int = {
    e match {
      case Str(s) => s.length
      case Brk(n) => n
      case Blo(_, _, n) => n
      case Grp(_, _, n) => n
    }
  }

  /** Print an object of type Pretty. */
  def pr(w: PrintWriter, margin: Int, e: Pretty): Unit = {
    printing(w, margin, List(e), margin, 0, false, margin)
  }

  private def printing(w: PrintWriter, margin: Int, es: List[Pretty],
		       blockspace:Int, after: Int, force: Boolean,
		       space: Int): Int = {
    es match {
      case Nil => space
      case e :: es =>
	val space1 = e match {
	  case Str(s) =>		// Place a string
	    w.print(s)
	    space - s.length
	  case Brk(n) =>		// Place breakable space
	    if (!force && n + breakdist(es, after) <= space)
	      blanks(w, n, space)	// Don't break
	    else {
	      w.println()		// Break
	      blanks(w, margin - blockspace, margin)
	    }
	  case Blo(bes, indent, _) =>	// Place a block
	    printing(w, margin, bes, space - indent,
		     breakdist(es, after), false, space)
	  case Grp(bes, indent, n) =>	// Place a group
	    val dist = breakdist(es, after)
	    printing(w, margin, bes, space - indent,
		     dist, n + dist > space, space)
	}
	printing(w, margin, es, blockspace, after, force, space1)
    }
  }

  // Find the distance to the nearest breakable space
  private def breakdist(es: List[Pretty], after: Int): Int = {
    es match {
      case Nil => after
      case Str(s) :: es => s.length + breakdist(es, after)
      case Brk(_) :: es => 0
      case Blo(_, _, n) :: es => n + breakdist(es, after)
      case Grp(_, _, n) :: es => n + breakdist(es, after)
    }
  }

  // Place spaces
  private def blanks(w: PrintWriter, n: Int, space: Int): Int = {
    if (n <= 0)
      space
    else {
      w.print(' ')
      blanks(w, n - 1, space - 1)
    }
  }
}
