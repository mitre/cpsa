/*
 * S-expressions
 *
'* Copyright (c) 2010 The MITRE Corporation
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the BSD License as published by the University
 * of California.
 */

package cpsaextras

import java.io._

/**
 * Annotated S-expressions.  Each S-expression can be annotated with
 * something of type A.
 */
sealed abstract class SExpr[A] {
  /** The annotation. */
  val a: A
}
/** Case of a symbol. */
case class S[A](a: A, s: String) extends SExpr[A] {
  override def toString(): String = {
    s.toString()
  }
}
/** Case of a string. */
case class Q[A](a: A, q: String) extends SExpr[A] {
  override def toString(): String = {
    "\"" + q.toString() + "\""
  }
}
/** Case of a number. */
case class N[A](a: A, n: Int) extends SExpr[A] {
  override def toString(): String = {
    n.toString()
  }
}
/** Case of a list of S-expressions. */
case class L[A](a: A, l: List[SExpr[A]]) extends SExpr[A] {
  override def toString(): String = {
    l.toString()
  }
}

/** The file position annotation. */
final case class Pos(file: String, line: Int, column: Int) {
  override def toString (): String = {
    file + ":" + line + ":" + column + ": "
  }
}

/** An S-expression reader.
 *
 * @param file name of the input file
 * @param in stream associated with the input file
 */
class SExprReader(file: String, in: Reader) {
  private var line = 1			// Stream line number
  private var column = 1		// Stream column

  // A scanner token
  private sealed abstract class Token
  // A token for a non-list S-expression
  private case class Atom(a: SExpr[Pos]) extends Token
  // A token for the left parenthesis
  private case class LParen(p: Pos) extends Token
  // A token for the right parenthesis
  private case class RParen(p: Pos) extends Token
  // A token for end-of-file
  private case object Eof extends Token

  /**
   * Reads an S-expression annotated with file positions.
   * @return an S-expression or null on end-of-file
   */
  def read(): SExpr[Pos] = {
    scan() match {
      case Atom(a) => a
      case LParen(p) => list(p, Nil)
      case RParen(p) =>
	in.close()
	throw new IOException(p + "Close of unopened list")
      case Eof =>
	in.close()
	null
    }
  }

  // Parse a non top-level list
  private def list(pos: Pos, acc: List[SExpr[Pos]]): SExpr[Pos] = {
    scan() match {
      case Atom(a) => list(pos, a :: acc)
      case LParen(p) => list(pos, list(p, Nil) :: acc)
      case RParen(_) => L(pos, acc.reverse)
      case Eof =>
	in.close()
	throw new IOException(pos + "Unexpected end of input in list")
    }
  }

  // Scanner

  // Consume white space and then dispatch on the first character
  private def scan(): Token = {
    val ch = get()
    if (Character.isWhitespace(ch))
      scan()
    else ch match {
      case -1 => Eof
      case '(' => LParen(Pos(file, line, column))
      case ')' => RParen(Pos(file, line, column))
      case ';' => comment()
      case _ => atom(ch)
    }
  }

  // Consume a comment and then resume scanning
  private def comment(): Token = {
    get() match {
      case -1 => Eof
      case '\n' => scan()
      case _ => comment()
    }
  }

  // Scan an atom
  private def atom(ch: Int): Token = {
    val p = Pos(file, line, column)	// Position of atom
    ch match {
      case '"' => string(p, new StringBuilder())
      case '+' => numOrSym(p, singleton(ch))
      case '-' => numOrSym(p, singleton(ch))
      case _ =>
	if (Character.isDigit(ch))
	  number(p, singleton(ch))
	else if (isSym(ch))
	  symbol(p, singleton(ch))
	else {
	  in.close()
	  throw new IOException(p + "Bad char in atom")
	}
    }
  }

  // Create a string buffer with one character
  private def singleton(ch: Int): StringBuilder = {
    val sb = new StringBuilder()
    sb.append(ch.toChar)
    sb
  }

  // Scan a string atom
  private def string(p: Pos, sb: StringBuilder): Token = {
    val ch = get()
    if (ch == -1) {
      in.close()
      throw new IOException(p + "End of input in string")
    }
    else if (ch == '"')
      Atom(Q(p, sb.toString().intern()))
    else if (isStr(ch)) {
      sb.append(ch.toChar)
      string(p, sb)
    }
    else {
      in.close()
      throw new IOException(p + "Bad char for string")
    }
  }

  // Scan a number atom
  private def number(p: Pos, sb: StringBuilder): Token = {
    val ch = peek()
    if (ch == -1)
      Atom(N(p, Integer.parseInt(sb.toString())))
    else if (Character.isDigit(ch)) {
      get()
      sb.append(ch.toChar)
      number(p, sb)
    }
    else if (isSym(ch)) {
      in.close()
      throw new IOException(p + "Bad char after number")
    }
    else
      Atom(N(p, Integer.parseInt(sb.toString())))
  }

  // See if an atom is an number or a symbol
  private def numOrSym(p: Pos, sb: StringBuilder): Token = {
    val ch = peek()
    if (ch == -1)
      symbol(p, sb)
    else if (Character.isDigit(ch))
      number(p, sb)
    else
      symbol(p, sb)
  }

  // Scan a symbol
  private def symbol(p: Pos, sb: StringBuilder): Token = {
    val ch = peek()
    if (ch == -1)
      Atom(S(p, sb.toString().intern()))
    else if (isSym(ch)) {
      get()
      sb.append(ch.toChar)
      symbol(p, sb)
    }
    else
      Atom(S(p, sb.toString().intern()))
  }

  // Is character a constituent of a symbol?
  private def isSym(ch: Int) = {
    ch match {
      case '+' => true
      case '-' => true
      case '*' => true
      case '/' => true
      case '<' => true
      case '=' => true
      case '>' => true
      case '!' => true
      case '?' => true
      case ':' => true
      case '$' => true
      case '%' => true
      case '_' => true
      case '&' => true
      case '~' => true
      case '^' => true
      case _ => Character.isLetterOrDigit(ch)
    }
  }

  // Is character a constituent of a string?
  private def isStr(ch: Int) = {
    ch match {
      case '"' => false
      case '\\' => false
      case _ => !Character.isISOControl(ch)
    }
  }

  // Character reader with look ahead

  private var peeked = false		// Is look ahead active?
  private var seen = 0			// peeked character

  // Get next character and set the current file position.
  private def get(): Int = {
    val next =
      if (peeked) {
	peeked = false
	seen
      }
      else
	in.read()
    if (next == '\n') {
      line += 1
      column = 1
    }
    else
      column += 1
    next
  }

  // Read ahead if need be
  private def peek(): Int = {
    if (peeked)
      seen
    else {
      peeked = true
      seen = in.read()
      seen
    }
  }
}
