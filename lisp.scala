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
  //Empty unit
  case object UoMOne extends UoM
  //Base unit
  case class UoMBase(n:String) extends UoM
  // As opposed to F#, I think it will be more elegant to 
  // incorporate multiplication factors into the UoM
  // of course, these factors are values in their own right,
  // because why not
  case class UoMNum(x:Value) extends UoM
  // Unlike integers, products for UoMs can't be described
  // As functions, they are fundamental. However, nothing
  // parses to a product or Inv.
  case class UoMProd(l:Value, r:Value) extends UoM
  // Rather than inverse, I've used powers as it will make
  // my algorithms faster
  case class UoMPow(u:Value, n:Int) extends UoM

  // syntactically, you can parametise I by
  // any value and it will parse, However
  // on execution the value must be a unit of measure
  case class I(n: Int, u:Value) extends Value
  case class Fl(f: Double, u:Value) extends Value

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
      case I(n,u) => base_eval(u,env,F{v=>cont.f(I(n,simplify(v)))})
      case Fl(x,u) => base_eval(u,env,F{v=>cont.f(Fl(x,simplify(v)))}) 
      case UoMNum(x) => base_eval(x,env,F{y=>cont.f(UoMNum(y))})  
      case B(_) | UoMBase(_) | UoMProd(_,_) |UoMOne => cont.f(exp)
      case S(sym) => eval_var(exp, env, cont)
      case P(fun, args) => eval_application(exp, env, cont)
    }
  }

  def eval_var(exp: Value, env: Env, cont: Cont): Value = exp match {
    case S(x) => cont.f(get(env, x))
  }

  def eval_application(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(fun, args) => base_eval(fun, env, F{ vf => vf match {
      case F(f) => evlist(args, env, F{ vas => cont.f(f(vas)) })
      case Fsubr(f) => f(exp, env, cont)
      case Fexpr(f) => cont.f(f(args))
    }})
  }

  def evlist(exp: Value, env: Env, cont: Cont): Value = exp match {
    case NullValue => cont.f(NullValue)
    case P(first, rest) => base_eval(first, env, F{v => evlist(rest, env, F{vs => cont.f(P(v,vs))})})
  }

  def eval_equality(args: Value): Value = args match {
    case P(I(a,u), P(I(b,v), NullValue)) => unify_values(u,v) match {
      case UoMOne => B(a==b)
      case UoMNum(I(x,UoMOne)) => B(a*x == b)
    }
  }

  def eval_add(args: Value): Value = args match {
    case P(I(a,u), P(I(b,v), NullValue)) => unify_values(u,v) match {
      case UoMOne => I(a+b,v)
      case UoMNum(I(x,UoMOne)) => I(a*x + b,v)
      case UoMNum(Fl(x,UoMOne)) => Fl(a*x + b,v)
    }
    case P(Fl(a,u), P(I(b,v), NullValue)) => unify_values(u,v) match {
      case UoMOne => Fl(a+b,v)
      case UoMNum(I(x,UoMOne)) => Fl(a*x + b,v)
      case UoMNum(Fl(x,UoMOne)) => Fl(a*x + b,v)
    }
    case P(I(a,u), P(Fl(b,v), NullValue)) => unify_values(u,v) match {
      case UoMOne => Fl(a+b,v)
      case UoMNum(I(x,UoMOne)) => Fl(a*x + b,v)
      case UoMNum(Fl(x,UoMOne)) => Fl(a*x + b,v)
    }
    case P(Fl(a,u), P(Fl(b,v), NullValue)) => unify_values(u,v) match {
      case UoMOne => Fl(a+b,v)
      case UoMNum(I(x,UoMOne)) => Fl(a*x + b,v)
      case UoMNum(Fl(x,UoMOne)) => Fl(a*x + b,v)
    }
  }

  def eval_subtract(args: Value): Value = args match {
    case P(I(a,u), P(I(b,v), NullValue)) => eval_add(P(I(a,u),P(I(-b,v),NullValue)))
  }

  def eval_mult(args: Value): Value = args match {
    case P(u:UoM, P(v:UoM, NullValue)) => simplify(UoMProd(u,v))
    case P(I(a,u), P(I(b,v), NullValue)) => I(a*b,simplify(UoMProd(u,v)))
    case P(I(a,u), P(Fl(b,v), NullValue)) => Fl(a*b,simplify(UoMProd(u,v)))
    case P(Fl(a,u), P(I(b,v), NullValue)) => Fl(a*b,simplify(UoMProd(u,v)))
    case P(Fl(a,u), P(Fl(b,v), NullValue)) => Fl(a*b,simplify(UoMProd(u,v)))
    case P(I(a,UoMOne), P(u:UoM, NullValue)) => simplify(UoMProd(UoMNum(I(a,UoMOne)),u))
    case P(Fl(a,UoMOne), P(u:UoM, NullValue)) => simplify(UoMProd(UoMNum(Fl(a,UoMOne)),u))
    case P(u:UoM, P(I(a,UoMOne), NullValue)) => simplify(UoMProd(UoMNum(I(a,UoMOne)),u))
    case P(u:UoM, P(Fl(a,UoMOne), NullValue)) => simplify(UoMProd(UoMNum(Fl(a,UoMOne)),u))
  }

  def eval_divide(args: Value): Value = args match {
    case P(a, P(b, NullValue)) => eval_mult(P(a,P(eval_power(P(b,P(I(-1,UoMOne),NullValue))),NullValue)))
  }

  def eval_power(args: Value): Value = args match {
    case P(Fl(a,u), P(I(n,UoMOne), NullValue)) => Fl(scala.math.pow(a,n),simplify(UoMPow(u,n)))
    case P(u : UoM,P(I(n,UoMOne), NullValue)) => simplify(UoMPow(u,n))
  }

  def eval_lessthan(args: Value): Value = args match {
    case P(I(a,u), P(I(b,v), NullValue)) => unify_values(u,v) match {
      case UoMOne => B(a < b)
      case UoMNum(I(x,UoMOne)) => B(a*x < b)
      case UoMNum(Fl(x,UoMOne)) => B(a*x < b)
    }
  }

  //returns fl()
  def eval_unify(args: Value): Value = args match {
    case P(a,P(b,NullValue)) => unify_values(a,b)
  }

  def eval_if(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(_, P(c, P(a, P(b, NullValue)))) => base_eval(c, env, F{ cv => cv match {
      case B(false) => base_eval(b, env, cont)
      case B(true) => base_eval(a, env, cont)
    }})
  }

  def eval_quote(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(_, P(x, NullValue)) => cont.f(x)
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

  //adds the unit to the environment as a base unit
  def eval_unit(exp: Value, env: Env, cont: Cont): Value = exp match {
    case P(_, exps@P(S(_), _)) => eval_unit_propegate(exps,env,cont)
  }

  def eval_unit_propegate(exp: Value, env: Env, cont: Cont): Value = exp match {
    case NullValue => NullValue
    case P(s@S(name),exps) => {
      val p = P(s,UoMBase(name))
      env.car = P(p, env.car)
      eval_unit_propegate(exps: Value, env: Env, cont: Cont)
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

  // simplifies the UoM as far as it will go
  // this means of the form prod(x,prod(pow(x1,n1),...prod(pow(xn,nn),One)))
  // where xi is either a base or power of base
  // and all bases are non inverses first than aphabetical order and x is the
  // multiplying factor if one exists
  def simplify(u: Value): UoM = u match {
    case UoMOne => UoMOne
    case UoMNum(n) => UoMProd(UoMNum(n),UoMOne)
    case UoMBase(s) => UoMProd(UoMPow(UoMBase(s),1),UoMOne)
    case UoMPow(v,n) => foldUoM(powUoM(n),simplify(v))
    case UoMProd(v,w) => merge(simplify(v),simplify(w))
  }

  //takes something of prod(x,prod(pow(x1,n1),...prod(pow(xn,nn),One)))
  //and applies f to every element
  def foldUoM(f:(UoM => UoM),u:UoM): UoM = u match {
    case UoMProd(l:UoM,r:UoM) => UoMProd(f(l),foldUoM(f,r))
    case UoMOne => UoMOne
  }

  // takes u and v written in above structure and merges them together
  def merge(u:UoM,v:UoM): UoM = u match {
    case UoMOne => v
    case UoMProd(UoMNum(x),us:UoM) => multfirst(x,merge(us,v))
    case UoMProd(UoMPow(UoMBase(s),n),us:UoM) => insert(UoMPow(UoMBase(s),n),merge(us,v))
  }

  //takes an x and raises it to the power of n
  def powUoM(n:Int): (UoM => UoM) = u => u match {
    case UoMPow(v:UoM,m) => UoMPow(v,m*n)
    case UoMNum(I(m,UoMOne)) => UoMNum(I(scala.math.pow(m,n).toInt,UoMOne))
    case UoMNum(Fl(x,UoMOne)) => UoMNum(Fl(scala.math.pow(x,n),UoMOne))
    case UoMOne => UoMOne
  }

  //takes something written in the above structure
  //and multiples it by x
  def multfirst(xv:Value,u:UoM): UoM = xv match {
    case I(n,UoMOne) => u match {
      case UoMOne => UoMProd(UoMNum(xv),UoMOne)
      case UoMProd(UoMNum(I(m,UoMOne)),w:UoM) => UoMProd(UoMNum(I(n*m,UoMOne)),w)
      case UoMProd(UoMNum(Fl(y,UoMOne)),w:UoM) => UoMProd(UoMNum(Fl(n*y,UoMOne)),w)
      case UoMProd(UoMPow(UoMBase(_),_),w:UoM) => UoMProd(UoMNum(xv),u)
    }
    case Fl(x,UoMOne) => u match {
      case UoMOne => UoMProd(UoMNum(xv),UoMOne)
      case UoMProd(UoMNum(I(m,UoMOne)),w:UoM) => UoMProd(UoMNum(Fl(x*m,UoMOne)),w)
      case UoMProd(UoMNum(Fl(y,UoMOne)),w:UoM) => UoMProd(UoMNum(Fl(x*y,UoMOne)),w)
      case UoMProd(UoMPow(UoMBase(_),_),w:UoM) => UoMProd(UoMNum(xv),u)
    }
  }

  // takes a u of the form pow(base(s),n) and v of the 
  // above structure and finds a place
  // to inset u into the alphabetical order
  def insert(u:UoM,v:UoM) : UoM = u match {
    case UoMPow(UoMBase(s),n) => v match {
      case UoMOne => UoMProd(u,UoMOne)
      case UoMProd(UoMNum(x),vs:UoM) => UoMProd(UoMNum(x),insert(u,vs))
      case UoMProd(UoMPow(UoMBase(s2),n2),vs:UoM) => if (s < s2) {
        UoMProd(u,v)
      } else if (s == s2) {
        if (n == -n2) vs
        else UoMProd(UoMPow(UoMBase(s),n+n2),vs)
      } else /*s > s2*/ {
        UoMProd(UoMPow(UoMBase(s2),n2),insert(u,vs))
      }
    }
  }

  /* useful functions in debugging
  // checks if arranged in the form 
  def standard_form(u:Value) : Boolean = u match {
    case UoMProd(UoMNum(_),v) => standard_form_nonumber(v)
    case _ => standard_form_nonumber(u)
  }

  def standard_form_nonumber(u:Value) : Boolean = u match {
    case UoMOne => true
    case UoMProd(UoMPow(UoMBase(_),_),UoMOne) => true
    case UoMProd(UoMPow(UoMBase(s1),_),UoMProd(UoMPow(UoMBase(s2),n),v)) => 
      (s1 < s2) && standard_form_nonumber(UoMProd(UoMPow(UoMBase(s2),n),v))
  }
  */

  // returns the value that u (the unit) must be mutiplied
  // by to reach v. Returns 0 if there is no such factor
  def unify_values(u: Value, v: Value) : Value = simplify(UoMProd(u,UoMPow(v,-1))) match {
    case UoMOne => UoMOne
    case UoMProd(UoMNum(x),UoMOne) => UoMNum(x)
    case _ => NullValue 
  }

  def make_init_env() = {
    lazy val init_env: Env = P(valueOf(List(
      P(S("eq?"), F(eval_equality)),
      P(S("+"), F(eval_add)),
      P(S("-"), F(eval_subtract)),
      P(S("*"), F(eval_mult)),
      P(S("/"), F(eval_divide)),
      P(S("^"), F(eval_power)),
      P(S("<"), F(eval_lessthan)),
      P(S("eval"), F({args => args match {case P(e,NullValue) => base_eval(e,init_env,F({x => x})) }})),
      //as far as I can tell everything is already as lists anyway
      P(S("list"), F({args => args})),
      //cons seems like it doesn't need to do any more than simply rearrange the arguments ahead of 
      P(S("cons"), F(args => args match { case P(a, P(b, NullValue)) => P(a,b)})), 
      P(S("car"), F(args => args match { case P(P(a, b),NullValue) => a})), 
      P(S("cdr"), F(args => args match { case P(P(a, b),NullValue) => b})), 
      P(S("unify"), F(eval_unify)),

      P(S("if"), Fsubr(eval_if)),
      P(S("quote"), Fsubr(eval_quote)),
      P(S("set!"), Fsubr(eval_set_bang)),
      P(S("lambda"), Fsubr(eval_lambda)),
      P(S("begin"), Fsubr(eval_begin)),
      P(S("define"), Fsubr(eval_define)),
      P(S("unit"), Fsubr(eval_unit)),
      P(S("fsubr"), Fsubr(eval_fsubr)),
      P(S("fexpr"), Fsubr(eval_fexpr)),
      )), NullValue)
     init_env
  }
}

import scala.util.parsing.combinator._
object parser extends JavaTokenParsers with PackratParsers {
  def exp: Parser[Value] =
    "#f" ^^ { case _ => B(false) } |
    "#t" ^^ { case _ => B(true) } |
    wholeNumber ~ ("[" ~> exp <~ "]") ^^ { case s~u => I(s.toInt,u) } |
    decimalNumber ~ ("[" ~> exp <~ "]") ^^ { case s~u => Fl(s.toDouble,u) } |
    wholeNumber ^^ { case s => I(s.toInt,UoMOne) } |
    decimalNumber ^^ { case s => Fl(s.toDouble,UoMOne) } |
    """[^\s\(\)\[\]'"]+""".r ^^ { case s => S(s) } |
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
      n.toString + "[" + addParen(pp(u)) + "]")
    case Fl(x,u) => (false, 
      x.toString + "[" + addParen(pp(u)) + "]")
    case S(s) => (false, s)
    case NullValue => (true, "")
    case P(a, NullValue) => (true, addParen(pp(a)))
    case P(a, d) =>
      val s1 = addParen(pp(a))
      val (need_paren2, s2) = pp(d)
      if (need_paren2) (true, s1+" "+s2)
      else (true, s1+" . "+s2)
    case UoMOne => (true, "")
    case UoMBase(name) => (false, name)
    case UoMNum(x) => 
      val s = addParen(pp(x))
      (false, x.toString)
    case UoMProd(l, r) => (false, 
      addParen(pp(l)) + " " + addParen(pp(r)))
    case UoMPow(u:UoM, n:Int) => (false,
      addParen(pp(u)) + "^" + n)
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
  test("true") {
    assertResult(B(true))(ev("#t"))
  }

  test("unit") {
    ev("(unit m)")
    assertResult(I(5,UoMProd(UoMPow(UoMBase("m"),1),UoMOne)))(ev("5[m]"))
  }

  test("conversion of ints") {
    assertResult(I(5,UoMOne))(ev("5"))
  }

  test("m^2") {
    ev("(unit m)")
    assertResult(UoMProd(UoMPow(UoMBase("m"),2),UoMOne))(ev("(* m m)"))
  }

  test("simplify") {
    assertResult(
      UoMProd(UoMPow(UoMBase("m"),2),UoMProd(UoMPow(UoMBase("s"),1),UoMOne))
    )(
      simplify(UoMProd(UoMBase("s"),UoMPow(UoMBase("m"),2)))
    )
  }

  test("number") {
    assertResult(I(-1,UoMOne))(ev("-1"))
  }

  test("add 1 to 1") {
    assertResult(I(2,UoMOne))(ev("(+ 1 1)"))
  }

  test("multiply by -1") {
    assertResult(I(-2,UoMOne))(ev("(* -1 2)"))
  }

  test("ms^-2") {
    ev("(unit m s)")
    assertResult(I(-1,(simplify(UoMProd(UoMBase("m"),UoMPow(UoMBase("s"),-2))))))(ev("-1[(* m (^ s -2))]"))
  }

  test("power distribution") {
    ev("(unit m s)")
    assertResult(B(true))(ev("(eq? 2[(^ (* m s) 2)] 2[(* (^ m 2) (^ s 2))])"))
  }

  test("Add") {
    ev("(unit m)")
    assertResult(B(true))(ev("(eq? (+ 2[m] 3[m]) 5[m])"))
  }

  test("Add conversion") {
    ev("(unit m)")
    ev("(define km (* m 1000))")
    assertResult(B(true))(ev("(eq? (+ 2[km] 1[m]) 2001[m])"))
  }

  test("define conversion") {
    ev("(unit m)")
    ev("(define feetinmeters 0.3048)")
    ev("(define ft (* feetinmeters m))")
    assertResult(B(true))(ev("(< 3[ft] 1[m])"))
  }

  test("gravity") {
    ev("(unit m s kg)")
    ev("(define mass 5.9722[kg])")
    ev("(define G 6.674[(* (^ m 3) (* (^ kg -1) (^ s -2)))])")
    ev("(define gravfield (lambda (r) (* -1 (* G (* mass (^ r -2))))))")
    display((ev("(gravfield 3.4[m])")))
  }

  test("fsubr history (carried over from assignment one)") {
    ev("(define old-set! set!)")
    ev("(define history '())")
    ev("""(define save! (fexpr (lhs rhs)
   ((lambda (old-val)
     (eval (list 'old-set! lhs rhs))
     (old-set! history (cons (list
        lhs
        old-val (eval lhs)) history)))
   (eval lhs))))""")
    ev("""(set! set! (fsubr (exp env cont)
      (eval (list 'save! (car (cdr exp)) (car (cdr (cdr exp)))))
      (cont (car (cdr exp)))))""")
    ev("(define test 1)")
    ev("(set! test (* test 2))")
    assertResult(I(2,UoMOne))(ev("test"))
    ev("(set! test (* test 2))")
    assertResult(I(4,UoMOne))(ev("test"))
  }

  test("imperial") {
    ev("(unit oz)")
    ev("(define lb (* 16 oz))")    
    ev("(define st (* 14 lb))")
    display(ev("(+ 5[st] (+ 7[lb] 2[oz]))"))
  }

  test("imperial reverse") {
    ev("(unit oz)")
    ev("(define lb (* 16 oz))")    
    ev("(define st (* 14 lb))")
    ev("(define reduce ( lambda (stv lbv ozv) ("
        +"if (< (- stv 1[st]) 0[oz]) ("
          +"if (< (- stv 1[lb]) 0[oz]) ("
            +"list (stv lbv ozv)"
          +") (reduce (stv (+ lbv 1) (- ozv 1[lb])))"
        +") (reduce ((+ lbv 1) stv (- ozv 1[st])))"
      +")))")
    display(ev("(reduce (list (0 0 1234[oz])))"))
  } 
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