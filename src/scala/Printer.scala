/*
 * A CPSA specific pretty printer
 *
 * Copyright (c) 2009 The MITRE Corporation
 *
 * This program is free software: you can redistribute it and/or
 * modify it under the terms of the BSD License as published by the
 * University of California.
 */

package cpsaextras

import java.io.PrintWriter

object Printer {

  /** CPSA specific pretty printer.
   * The pretty printer that indents a constant amount for each list.  The
   * top-level lists are laid out specially.  Whenever some breaks
   * occur, all breaks are forced.  Also, breaks are only placed before
   * strings and lists.  CPSA protocols are handled specially.  Each
   * defrole is handled as are top-level lists.
   *
   * @param w the output writer
   * @param margin the width to be filled
   * @param indent the number of spaces in an indent
   * @param x the S-expression to be pretty printed
   */
  def pp[A](w: PrintWriter, margin: Int, indent: Int, x: SExpr[A]): Unit = {
    Pretty.pr(w, margin, pretty(indent, x))
  }

  private def pretty[A](indent: Int, x: SExpr[A]): Pretty = {
    x match {
      case L(_, (x@S(_, "defprotocol")) :: xs) =>
	roles(indent, xs, List(block(indent, x), Pretty.str("(")))
      case x@L(_, S(_, "defmacro") :: _) =>
	block(indent, x)
      case x@L(_, S(_, "herald") :: _) =>
	block(indent, x)
      case _ =>
	group(indent, x)
    }
  }

  // Role specific pretty printer
  private def roles[A](indent: Int, xs: List[SExpr[A]],
		       acc: List[Pretty]): Pretty = {
    xs match {
      case Nil =>
	Pretty.grp(indent, (Pretty.str(")") :: acc).reverse)
      case (x@S(_, _)) :: xs =>
	roles(indent, xs, block(indent, x) :: Pretty.str(" ") :: acc)
      case (x@Q(_, _)) :: xs =>
	roles(indent, xs, block(indent, x) :: Pretty.brk(1) :: acc)
      case (x@N(_, _)) :: xs =>
	roles(indent, xs, block(indent, x) :: Pretty.str(" ") :: acc)
      case (x@L(_, S(_, "defrole") :: _)) :: xs =>
	roles(indent, xs, group(indent, x) :: Pretty.brk(1) :: acc)
      case (x@L(_, _)) :: xs =>
	roles(indent, xs, block(indent, x) :: Pretty.brk(1) :: acc)
    }
  }

  // A pretty printer for top-level S-expressions
  private def group[A](indent: Int, x: SExpr[A]): Pretty = {
    x match {
      case L(a, l) => grouplist(indent, l)
      case _ => block(indent, x)
    }
  }

  private def grouplist[A](indent: Int, xs: List[SExpr[A]]): Pretty = {
    xs match {
      case Nil => Pretty.str("()")
      case x :: xs =>
	grouprest(indent, xs, List(block(indent, x), Pretty.str("(")))
    }
  }

  private def grouprest[A](indent: Int, xs: List[SExpr[A]],
			acc: List[Pretty]): Pretty = {
    xs match {
      case Nil =>
	Pretty.grp(indent, (Pretty.str(")") :: acc).reverse)
      case (x@S(_, _)) :: xs =>
	grouprest(indent, xs, block(indent, x) :: Pretty.str(" ") :: acc)
      case (x@Q(_, _)) :: xs =>
	grouprest(indent, xs, block(indent, x) :: Pretty.brk(1) :: acc)
      case (x@N(_, _)) :: xs =>
	grouprest(indent, xs, block(indent, x) :: Pretty.str(" ") :: acc)
      case (x@L(_, _)) :: xs =>
	grouprest(indent, xs, block(indent, x) :: Pretty.brk(1) :: acc)
    }
  }

  // A pretty printer for interior lists using block style breaking.
  private def block[A](indent: Int, x: SExpr[A]): Pretty = {
    x match {
      case L(a, l) => blocklist(indent, l)
      case _ => Pretty.str(x.toString())
    }
  }

  private def blocklist[A](indent: Int, xs: List[SExpr[A]]): Pretty = {
    xs match {
      case Nil => Pretty.str("()")
      case x :: xs =>
	blockrest(indent, xs, List(block(indent, x), Pretty.str("(")))
    }
  }

  private def blockrest[A](indent: Int, xs: List[SExpr[A]],
			acc: List[Pretty]): Pretty = {
    xs match {
      case Nil =>
	Pretty.blo(indent, (Pretty.str(")") :: acc).reverse)
      case x :: xs =>
	blockrest(indent, xs, block(indent, x) :: Pretty.brk(1) :: acc)
    }
  }
}
