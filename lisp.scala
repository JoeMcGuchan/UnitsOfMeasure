package lisp

object ast {
  trait Value
  case object Undefined extends Value
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
    //def base_eval(exp: Value, env: Env, cont: Cont): Value = {
  def base_eval(exp: Value, env: Env, cont: Cont): Value = debug(s"eval ${pp.show(exp)}", env, cont) { (cont) =>
    exp match {
      case I(_,_) | B(_) | Fl(_,_) => cont.f(exp)
      case S(sym) => eval_var(exp, env, cont)
      case P(fun, args) => eval_application(exp, env, cont)
    }
  }

  def eval_var(exp: Value, env: Env, cont: Cont): Value = exp match {
    case S(x) => cont.f(get(env, x))
  }

  def eval_quote(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(_, P(x, NullValue)) => cont.f(x)
  }

  def eval_if(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(_, P(c, P(a, P(b, NullValue)))) => base_eval(c, env, F{ cv => cv match {
      case B(false) => base_eval(b, env, cont)
      case B(true) => base_eval(a, env, cont)
    }})
  }

  def eval_set_bang(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(_, P(S(x), P(rhs, NullValue))) => base_eval(rhs, env, F{ v =>
      cont.f(set(env, x, v))
    })
  }

  def eval_lambda(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(_, P(params, body)) => cont.f(F({args =>
      eval_begin(body, extend(env, params, args), F{v => v})
    }))
  }

  def eval_begin(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(e, NullValue) => base_eval(e, env, cont)
    case P(e, es) => base_eval(e, env, F{ _ => eval_begin(es, env, cont) })
  }

  def eval_define(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(_, P(r@S(name), body)) => {
      val p = P(r,Undefined)
      env.car = P(p, env.car)
      eval_begin(body, env, F{v =>
        p.cdr = v
        cont.f(r)})
    }
  }

  def evlist(exp: Value, env: Env, cont: Cont): Value = exp match {
    case NullValue => cont.f(NullValue)
    case P(first, rest) => base_eval(first, env, F{v => evlist(rest, env, F{vs => cont.f(P(v,vs))})})
  }

  def eval_application(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(fun, args) => base_eval(fun, env, F{ vf => vf match {
      case F(f) => evlist(args, env, F{ vas => cont.f(f(vas)) })
      case Fsubr(f) => f(exp, env, cont)
      case Fexpr(f) => cont.f(f(args))
    }})
  }

  def eval_let(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(_,P(P(params, P(args,NullValue)),P(e,NullValue))) => {
      base_eval(e, extend(env,params,args), cont)
    }
  }

  def extend(env: Env, params: Value, args: Value): Env = {
    val frame = valueOf((list(params) zip  list(args)).map{t => P(t._1, t._2)})
    P(frame, env)
  }

  def eval_fsubr(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(_, P(params, body)) => cont.f(Fsubr({(exp, env, cont) =>
      eval_begin(body, extend(env, params, P(exp, P(env, P(cont, NullValue)))), F{x => x})
    }))
  }

  def eval_fexpr(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(_, P(params, body)) => cont.f(Fexpr({args =>
      eval_begin(body, extend(env, params, args), F{v => v})
    }))
  }

  def findFrame(frame: Value, x: String): Option[P] = frame match {
    case NullValue => None
    case P(P(S(y),_), _) if (x==y) => Some(frame.asInstanceOf[P].car.asInstanceOf[P])
    case P(_, rest) => findFrame(rest, x)
  }

  def find(env: Env, x: String): P = env match {
    case P(first,rest) => findFrame(first, x) match {
      case Some(p) => p
      case None => rest match {
        case next:Env => find(next, x)
        case _ => sys.error(s"unbound variable $x")
      }
    }
  }

  def get(env: Env, x: String): Value = find(env, x).cdr
  def set(env: Env, x: String, v: Value): Value = {
    val p = find(env, x)
    p.cdr = v
    v
  }

  def make_init_env() = {
    lazy val init_env: Env = P(valueOf(List(
      P(S("eq?"), F({args => args match { case P(a, P(b, NullValue)) => B(a==b) }})),
      P(S("+"), F({args => args match { case P(I(a,UoMNull), P(I(b,UoMNull), NullValue)) => I(a+b,UoMNull) }})),
      P(S("-"), F({args => args match { case P(I(a,UoMNull), P(I(b,UoMNull), NullValue)) => I(a-b,UoMNull) }})),
      P(S("*"), F({args => args match { case P(I(a,UoMNull), P(I(b,UoMNull), NullValue)) => I(a*b,UoMNull) }})),
      P(S("<"), F({args => args match { case P(I(a,UoMNull), P(I(b,UoMNull), NullValue)) => B(a < b) }})),
      P(S("eval"), F({args => args match {case P(e,NullValue) => base_eval(e,init_env,F({x => x})) }})),
      //as far as I can tell everything is already as lists anyway
      P(S("list"), F({args => args})),
      //cons seems like it doesn't need to do any more than simply rearrange the arguments ahead of 
      P(S("cons"), F(args => args match { case P(a, P(b, NullValue)) => P(a,b)})), 
      P(S("car"), F(args => args match { case P(P(a, b),NullValue) => a})), 
      P(S("cdr"), F(args => args match { case P(P(a, b),NullValue) => b})), 


      P(S("if"), Fsubr({(exp: Value, env: Env, cont: Cont) => eval_if(exp, env, cont)})),
      P(S("quote"), Fsubr({(exp: Value, env: Env, cont: Cont) => eval_quote(exp, env, cont)})),
      P(S("set!"), Fsubr({(exp: Value, env: Env, cont: Cont) => eval_set_bang(exp, env, cont)})),
      P(S("lambda"), Fsubr({(exp: Value, env: Env, cont: Cont) => eval_lambda(exp, env, cont)})),
      P(S("begin"), Fsubr({(exp: Value, env: Env, cont: Cont) => eval_begin(exp, env, cont)})),
      P(S("define"), Fsubr({(exp: Value, env: Env, cont: Cont) => eval_define(exp, env, cont)})),
      P(S("fsubr"), Fsubr({(exp: Value, env: Env, cont: Cont) => eval_fsubr(exp, env, cont)})),
      P(S("fexpr"), Fsubr({(exp: Value, env: Env, cont: Cont) => eval_fexpr(exp, env, cont)})),
      P(S("let"), Fsubr({(exp: Value, env: Env, cont: Cont) => eval_let(exp, env, cont)}))
      )), NullValue)
     init_env
  }
}

import scala.util.parsing.combinator._
object parser extends JavaTokenParsers with PackratParsers {
  def exp: Parser[Value] =
    "#f" ^^ { case _ => B(false) } |
    "#t" ^^ { case _ => B(true) } |
    wholeNumber ^^ { case s => I(s.toInt,UoMNull) } |
    """[^\s\(\)'"]+""".r ^^ { case s => S(s) } |
    "'" ~> exp ^^ { case s => P(S("quote"), P(s, NullValue)) } |
    "()" ^^ { case _ => NullValue } |
    "(" ~> exps <~ ")" ^^ { case vs => vs }

  def exps: Parser[Value] =
      exp ~ exps ^^ { case v~vs => P(v, vs) } |
      exp ^^ { case v => P(v, NullValue) }
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
    case Fl(x,u) => (false, 
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
