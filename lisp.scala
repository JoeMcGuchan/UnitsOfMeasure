package lisp

object ast {
  trait Value
  case object UndefinedValue extends Value
  case class B(b: Boolean) extends Value   
  case class S(sym: String) extends Value                     // Symbol
  case object NullValue extends Value

  class P(var car: Value, var cdr: Value) extends Value       // Pair
  {
    override def toString = s"P($car, $cdr)"
    // NOTE: we don't override equals to respect referential equality
  }
  object P {
    def apply(a: Value, b: Value): P = new P(a, b)
    def unapply(v: Value): Option[(Value, Value)] = v match {
      case p:P => Some((p.car, p.cdr))
      case _ => None
    }
  }

  //Unit of Measure is a value that can parametise things
  trait UoM extends Value
  case object UoMNull extends UoM // For Unitless Values
  case class UoMBase(name : String) extends UoM //Base Value
  // As opposed to F#, I think it will be more elegant to 
  // incorporate multiplication factors into the UoM
  case class UoMFact(x:Float) extends UoM
  // Unlike integers, products for UoMs can't be described
  // As functions, they are fundamental
  case class UoMProd(l:UoM, r:UoM) extends UoM
  case class UoMInv(u:UoM) extends UoM //u^(-1)

  case class I(n: Int, u:UoM) extends Value
  case class Fl(f: Float, u:UoM) extends Value

  case class F(f: Value => Value) extends Value
  case class Fsubr(f: (Value, Env, Cont) => Value) extends Value
  case class Fexpr(f: Value => Value) extends Value

  // Env is a list of frames (each a list of key/value pairs)
  // We use object structures for easy reification/reflection.
  type Env = P
  // Similarly, continuations are values too...
  type Cont = F

  def list(e: Value): List[Value] = e match {
    case NullValue => Nil
    case P(first, rest) => first :: list(rest)
  }
  def valueOf(es: List[Value]): Value = es match {
    case Nil => NullValue
    case first::rest => P(first, valueOf(rest))
  }
}

import ast._
object eval {
}

import scala.util.parsing.combinator._
object parser extends JavaTokenParsers with PackratParsers {
  def exp: Parser[Value] =
    "#f" ^^ { case _ => B(false) } |
    "#t" ^^ { case _ => B(true) } |
    wholeNumber ^^ { case s => I(s.toInt) } |
    """[^\s\(\)'"]+""".r ^^ { case s => S(s) } |
    "'" ~> exp ^^ { case s => P(S("quote"), P(s, N)) } |
    "()" ^^ { case _ => N } |
    "(" ~> exps <~ ")" ^^ { case vs => vs }

  def exps: Parser[Value] =
      exp ~ exps ^^ { case v~vs => P(v, vs) } |
      exp ^^ { case v => P(v, N) }
}

import eval._
import parser._
object repl {
  var global_env = make_init_env()
  def parse(s: String) = {
    val Success(e, _) = parseAll(exp, s)
    e
  }
  def evl(e: Value) = { base_eval(e, global_env, F{ v => v } ) }
  def ev(s: String) = evl(parse(s))
  def clean() = {
    global_env = make_init_env()
  }
}

object pp {
  def addParen(p: (Boolean, String)) = {
    val (need_paren, s) = p
    if (need_paren) "("+s+")" else s
  }
  def pp(v: Value): (Boolean, String) = v match {
    case B(b) => (false, if (b) "#t" else "#f")
    case I(n,u) => (false, 
      n.toString + "<" + addParen(pp(u)) + ">")
    case I(x,u) => (false, 
      x.toString + "<" + addParen(pp(u)) + ">")
    case S(s) => (false, s)
    case NullValue => (true, "")
    case P(a, NullValue) => (true, addParen(pp(a)))
    case P(a, d) =>
      val s1 = addParen(pp(a))
      val (need_paren2, s2) = pp(d)
      if (need_paren2) (true, s1+" "+s2)
      else (true, s1+" . "+s2)
    case UoMNull => (true, "")
    case UoMBase(name) => (false, name)
    case UoMFact(x) => (false, x.toString)
    case UoMProd(l, r) => (false, 
      addParen(pp(l)) + " * " + addParen(pp(r)))
    case UoMInv(u:UoM) => (false,
      addParen(pp(u)) + "^-1")
    case _ => (false, v.toString)
  }
  def show(v: Value) = addParen(pp(v))
  def display(v: Value) = print(show(v))
  def newline() = println("")
}


import repl._
import pp._
import utils._
class lisp_Tests extends TestSuite {  before { clean() }
}

import lisp._
import ast._
object debug {
  val enable = false
  var depth: Int = 0
  val indentTab = " "

  def apply[T](msg: String, env: Env, cont: Cont)(body: Cont => T) = trace[T](msg, env, cont)(body)

  def trace[T](msg: String, env: Env, cont: Cont)(body: Cont => T) = {
    indentedDebug(s"==> ${pad(msg)}?")
    indentedDebug(env.format)
    depth += 1
    val newCont = F { v =>
      depth -= 1
      indentedDebug(s"<== ${pad(msg)} = ${pad(v.toString)}")
      cont.f(v)
    }
    body(newCont)
  }

  def padding = indentTab * depth

  def pad(s: String, padFirst: Boolean = false) =
    s.split("\n").mkString(if (padFirst) padding else "", "\n" + padding, "")

  def indentedDebug(msg: String) =
    if(enable) println(pad(msg, padFirst = true))

  implicit class EnvDeco(val env: Env) extends AnyVal {
    def format: String =
      "---------env-------\n" ++
      list(env).map(formatFrame).mkString("\n") ++
      "\n---------env-------\n"

    def formatFrame(frame: Value): String = list(frame).map {
      case P(S(name), body) => name + " -> " + body
    }.mkString("\n")
  }
}
