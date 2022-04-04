package hw4

import scala.collection.immutable.HashMap 
import hw4._


package object hw4 {
  type Env = HashMap[Var,LocVal]
}

case class Mem(m: HashMap[LocVal,Val], top: Int) {
  def add(l: LocVal, value: Val) = Mem(m + (l -> value), l.l + 1)
  def extended(v: Val): (Mem, LocVal) = {
    val new_mem = Mem(m.updated(LocVal(top),v), top+1)
    (new_mem,LocVal(top))
  }
  def updated(l: LocVal, new_val: Val): Option[Mem] = {
    m.get(l) match {
      case Some(v) => Some(Mem(m.updated(l, new_val), top))
      case None => None
    }
  }
  def get(l: LocVal): Option[Val] = m.get(l)
  def getLocs(): List[LocVal] = m.keySet.toList
  def exists(l: LocVal): Boolean = m.exists((a: (LocVal, Val)) => a._1 == l)
}

sealed trait Val
case object SkipVal extends Val
case class IntVal(n: Int) extends Val
case class BoolVal(b: Boolean) extends Val
case class ProcVal(args: List[Var], expr: Expr, env: Env) extends Val
case class LocVal(l: Int) extends Val
sealed trait RecordValLike extends Val
case object EmptyRecordVal extends RecordValLike
case class RecordVal(field: Var, loc: LocVal, next: RecordValLike) extends RecordValLike


sealed trait Program
sealed trait Expr extends Program
case object Skip extends Expr
case object False extends Expr
case object True extends Expr
case class NotExpr(expr: Expr) extends Expr
case class Const(n: Int) extends Expr
case class Var(s: String) extends Expr {
  override def toString = s"Var(${"\""}${s}${"\""})"
}
case class Add(l: Expr, r: Expr) extends Expr
case class Sub(l: Expr, r: Expr) extends Expr
case class Mul(l: Expr, r: Expr) extends Expr
case class Div(l: Expr, r: Expr) extends Expr
case class LTEExpr(l: Expr, r: Expr) extends Expr
case class EQExpr(l: Expr, r: Expr) extends Expr
case class Iszero(c: Expr) extends Expr
case class Ite(c: Expr, t: Expr, f: Expr) extends Expr
case class Let(i: Var, v: Expr, body: Expr) extends Expr
case class Proc(args: List[Var], expr: Expr) extends Expr
case class Asn(v: Var, e: Expr) extends Expr
case class BeginEnd(expr: Expr) extends Expr
case class FieldAccess(record: Expr, field: Var) extends Expr
case class FieldAssign(record: Expr, field: Var, new_val: Expr) extends Expr
case class Block(f: Expr, s: Expr) extends Expr
case class PCallV(ftn: Expr, arg: List[Expr]) extends Expr
case class PCallR(ftn: Expr, arg: List[Var]) extends Expr
case class WhileExpr(cond: Expr, body: Expr) extends Expr
sealed trait RecordLike extends Expr
case object EmptyRecordExpr extends RecordLike
case class RecordExpr(field: Var, initVal: Expr, next: RecordLike) extends RecordLike








object MiniCInterpreter {

  case class Result(v: Val, m: Mem)
  case class UndefinedSemantics(msg: String = "", cause: Throwable = None.orNull) extends Exception("Undefined Semantics: " ++ msg, cause)
  case class Res(e: Env, m: Mem)  
  
  //def eval(env: Env, mem: Mem, expr: Expr): Result = Result(SkipVal, mem)
  def eval(env: Env, mem: Mem, expr: Expr): Result = expr match{
    case Skip =>{
      Result(SkipVal, mem)
    }
    case False =>{
      Result(BoolVal(false), mem)
    }
    case True =>{
      Result(BoolVal(true), mem)
    }
    case NotExpr(n) => eval(env, mem, n).v match{
      case (x: BoolVal) => {
        if (x.b == true){
          Result(BoolVal(false), mem)
        }
        else Result(BoolVal(true), mem)
      }
      case _ => throw new UndefinedSemantics(s"Exception!")
    }
    case Const(n) => Result(IntVal(n), mem)
    case s : Var => {
      if(env.exists((a: (Var, LocVal)) => a._1 == s)) {
        env(s) match{
          case(f: LocVal) => {
            if(mem.exists(f)){
              //println(s"[Var] ${f} ${mem.m(f)}")
              Result(mem.m(f), mem)
            }
            else throw new UndefinedSemantics(s"Exception 1!")
          }
          case _ => throw new UndefinedSemantics(s"Exception!")
        }
        
      }else throw new UndefinedSemantics(s"Exception 2!")
    }
    case Add(l, r) => eval(env, mem, l) match{
      case Result(IntVal(li), mem1) => eval(env, mem1, r) match {
        case Result(IntVal(ri), mem2) => {val rest = Result(IntVal(li + ri), mem2)
          // println(s"[ADD] ${rest.v}")
          rest
        }
        case _ => throw new UndefinedSemantics(s"Exception!")
      }
      case _ => throw new UndefinedSemantics(s"Exception!")
    }
    case Sub(l, r) => eval(env, mem, l) match{
      case Result(IntVal(li), mem1) => eval(env, mem1, r) match {
        case Result(IntVal(ri), mem2) => Result(IntVal(li - ri), mem2)
        case _ => throw new UndefinedSemantics(s"Exception!")
      }
      case _ => throw new UndefinedSemantics(s"Exception!")
    }
    case Mul(l, r) => eval(env, mem, l) match{
      case Result(IntVal(li), mem1) => eval(env, mem1, r) match {
        case Result(IntVal(ri), mem2) => Result(IntVal(li * ri), mem2)
        case _ => throw new UndefinedSemantics(s"Exception!")
      }
      case _ => throw new UndefinedSemantics(s"Exception!}")
    }
    case Div(l, r) => eval(env, mem, l) match{
      case Result(IntVal(li), mem1) => eval(env, mem1, r) match {
        case Result(IntVal(ri), mem2) => {
          if(ri == 0) throw new UndefinedSemantics(s"Exception!!")
          Result(IntVal(li / ri), mem2)
        }
        case _ => throw new UndefinedSemantics(s"Exception!")
      }
      case _ => throw new UndefinedSemantics(s"Exception!")
    }
    case LTEExpr(l, r) => eval(env, mem, l) match{
      case Result(IntVal(li), mem1) => eval(env, mem1, r) match {
        case Result(IntVal(ri), mem2) => Result(BoolVal(li <= ri), mem2)
        case _ => throw new UndefinedSemantics(s"Exception!")
      }
      case _ => throw new UndefinedSemantics(s"Exception!")
    }
    case EQExpr(l, r) => eval(env, mem, l) match{
      case Result(IntVal(li), mem1) => eval(env, mem1, r) match {
        case Result(IntVal(ri), mem2) => Result(BoolVal(li == ri), mem2)
        case _ => Result(BoolVal(false), mem1)
      }
      case Result(BoolVal(li), mem1) => eval(env, mem1, r) match {
        case Result(BoolVal(ri), mem2) => Result(BoolVal(li == ri), mem2)
        case _ => Result(BoolVal(false), mem1)
      }
      case Result(SkipVal, mem1) => eval(env, mem1, r) match {
        case Result(SkipVal, mem2) => Result(BoolVal(true), mem2)
        case _ => Result(BoolVal(false), mem1)
      }
      case _ => throw new UndefinedSemantics(s"Exception!")
    }
    case Iszero(x) => (eval(env, mem, x).v) match{
      case(z:  IntVal ) => if(z.n == 0) Result(BoolVal(true), mem) else Result(BoolVal(false), mem)
      case _ => throw new UndefinedSemantics(s"Exception!")
    }
    case Ite(c, t, f) => eval(env, mem, c).v match{
      case (v:  BoolVal ) => if (v.b) eval(env, mem, t) else eval(env, mem, f)
      case _ => throw new UndefinedSemantics(s"Exception!")
    }
    case Let(i, v, body) => {
      val res = eval(env, mem, v)
      val new_mem = res.m.extended(res.v)
      val new_env = env + (i -> new_mem._2)
      val new_res= eval(new_env, new_mem._1, body)
      // println(s"[Let] ${new_res.v}")
      new_res
    }
    case Proc(args, expr) => {
      val res = Result(ProcVal(args, expr, env), mem)
      // println(s"[Proc] ${res.v}")
      res
    }
    //let cnt = 0 in let f = proc (x) begin cnt := cnt + 1; cnt end in let a = f (1) in let b = f (1) in a + b
    case Asn(v, e) => {
      val value = eval(env, mem, e)
      if(!env.exists((a: (Var, Val)) => a._1 == v)){ throw new UndefinedSemantics(s"Exception!")}
      else {
        Result(value.v, Mem(value.m.m + (env(v) -> value.v), value.m.top))
      } 
    }
    case BeginEnd(expr) => {
      eval(env, mem, expr)
    }
    case FieldAccess(record, field) =>{
      val new_rec = eval(env, mem, record)
      def FieldFind(rec: RecordValLike, fiel: Var): LocVal = rec match{
        case (r: RecordVal) => {
          if(r.field == fiel){
            r.loc
          }
          else FieldFind(r.next, fiel)
        }
        case _ => throw new UndefinedSemantics(s"Exception!")
      }
      new_rec.v match{
        case (r: RecordVal) => {val new_res = Result(new_rec.m.m(FieldFind(r, field)), new_rec.m)
          // println(s"[Access] ${new_res.v}")
          new_res
        }
        case _ => throw new UndefinedSemantics(s"Exception!")
      }
    }
    case FieldAssign(record, field, value) =>{
      val new_rec = eval(env, mem, record)
      def FieldFind(rec: RecordValLike, fiel: Var): LocVal = rec match{
        case (r: RecordVal) => {
          if(r.field == fiel){
            r.loc
          }
          else FieldFind(r.next, fiel)
        }
        case _ => throw new UndefinedSemantics(s"Exception!")
      }
      new_rec.v match{
        case (r: RecordVal) => {
          val new_val = eval(env, new_rec.m, value)
          val loc = FieldFind(r, field)
          // val new_mem = Mem(new_val.m + (loc -> new_val.v), new_val.m.top)
          val new_mem = new_val.m.updated(loc, new_val.v)
          new_mem match{
            case Some(t) => {val new_res = Result(new_val.v, t)
              // println(s"[Assign] ${new_res.v}")
              new_res
            }
            case None => throw new UndefinedSemantics(s"Exception!")
          }
          
        }
        case _ => throw new UndefinedSemantics(s"Exception!")
      }
      
    }
    case Block(f, s) => {
      val res = eval(env, mem, f)
      val new_res = eval(env, res.m, s)
      // println(s"[Block] ${f} ${s}")
      new_res
    }
    case PCallV(ftn, arg) => {
      // println(s"[Func] ${ftn}")
      val res = eval(env, mem, ftn) // res.v, res.m
      // println(s"[PCALV] ${res.v}\n\n")
      res.v match{
        case (func: ProcVal) => {
          if(func.args.length != arg.length) throw new UndefinedSemantics(s"Exception!")
          else{
            def fore(i: Int, meme: Mem): (List[Val], Mem) = {
              if(i < arg.length){
                val new_res = eval(env, meme, arg(i))
                val returned = fore(i + 1, new_res.m)
                (List[Val](new_res.v) ::: returned._1, returned._2)
              }
              else{
                (Nil, meme)
              }
            }
            val rett = fore(0, res.m)
            val list =  rett._1 // list = {v1, v2, v3 ...}
            def fill(i: Int, enve: Env, meme: Mem): Res = {
              if(i >= func.args.length){
                Res(enve, meme)
              }
              else{
                val new_res = fill(i + 1, enve, meme)
                val new_env = new_res.e + (func.args(i) -> LocVal(new_res.m.top))
                val new_mem = new_res.m.add(LocVal(new_res.m.top), list(i))
                Res(new_env, new_mem)
              } 
            }
            val new_res = fill(0, func.env, rett._2)
            val Rest = eval(new_res.e, new_res.m, func.expr)
            // println(s"[Result] ${Rest.v}\n\n")
            Rest
          }
        }
        //case(func: Val) => res
        case _ => throw new UndefinedSemantics(s"${res.v} is not a ProcVal!");
        
      }
    }
    case PCallR(ftn, arg) => {
      val res = eval(env, mem, ftn) 
      res.v match{
        case (func: ProcVal) => {
          if(func.args.length != arg.length) throw new UndefinedSemantics(s"Exception!")
          else{
            def fill(i: Int, enve: Env): Env = {
              if(func.args.lift(i) == None){
                enve
              }
              else{
                val new_res = fill(i + 1, enve)
                if(env.exists((a: (Var, LocVal)) => a._1 == arg(i))){
                  val new_env = new_res + (func.args(i) -> env(arg(i)))
                  new_env
                }
                else throw new UndefinedSemantics(s"Exception!")
              }
            }
            val new_res = fill(0, func.env)
            eval(new_res, res.m, func.expr)
          }
        }
        case _ => throw new UndefinedSemantics(s"Exception!")
      }    
    }
    case WhileExpr(cond, body) =>{
      eval(env, mem, cond) match{
        case Result(BoolVal(false), mem1) => Result(SkipVal, mem1)
        case Result(BoolVal(true), mem1) => {
          val apple = eval(env, mem1, body) 
          eval(env, apple.m, WhileExpr(cond, body))
        }
        case _ => throw new UndefinedSemantics(s"Exception!")
      }
    }
    case EmptyRecordExpr => Result(EmptyRecordVal, mem)
    case RecordExpr(field, initVal, next) => {
      eval(env, mem, initVal) match{
        case Result(r: Val, mem1) => {
          val apple = eval(env, mem1, next)
          apple.v match{
            case nxt : RecordValLike => {
              val new_m = apple.m.extended(r) //(new_mem, loc)
              val rest = Result(RecordVal(field, new_m._2, nxt), new_m._1)
              // println(s"[RECORD] ${rest.v}\n\n")
              rest
            }
            case _ => throw new UndefinedSemantics(s"[Record`Expr 2]")
          }
          
        }
        case _ => throw new UndefinedSemantics(s"[Record`Expr]")
      }

      // val res = eval(env, mem, initVal)
      // val loc = res.m.top
      // val new_mem = res.m.add(field, loc)
      // val new_record = RecordVal(field, loc, next)
      // Result(new_record, new_mem)
    }

  }
  def gc(env: Env, mem: Mem): Mem = {
    def getList(r: RecordValLike, list: List[LocVal]): List[LocVal] = {
      r match{
        case(x: RecordVal) =>{
          getList(x.next, list ::: List[LocVal](x.loc))
        }
        case _ => list
      }
    }
    def rec(i: Int, list: List[Var], meme: Mem, list2: List[LocVal]): (Mem, List[LocVal]) ={
      if(i == list.length){ 
        return (meme, list2)
      }
      else{
        val new_loc = env(list(i))
        if(mem.exists(new_loc)){
          val new_val = mem.m(new_loc)
          val new_mem = Mem(meme.m + (new_loc -> new_val), meme.top)
          println(new_val)
          new_val match{
            case (x: LocVal) => {
              println(x)
              rec(i + 1, list, new_mem, list2 ::: List[LocVal](x))
            }
            case (r: RecordVal) => {
              println(r.loc)
              val new_list = getList(r, List[LocVal]())
              rec(i + 1, list, new_mem, list2 ::: new_list)
            }
            case (r: ProcVal) => {
              val res = gc(r.env, mem)
              val neww_mem = Mem(res.m.++(new_mem.m),mem.top)
              rec(i + 1, list, neww_mem, list2)
            }
            case _ => rec(i + 1, list, new_mem, list2)
          }
        }
        else{
          rec(i + 1, list, mem, list2)
        }
      }
          
    }
    def rec2(i: Int, list: List[LocVal], meme: Mem): Mem = {
      if(i == list.length){ 
        return meme
      }
      else{
        val new_loc = list(i)
        if(mem.exists(new_loc)){
          val new_val = mem.m(new_loc)
          val new_mem = Mem(meme.m + (new_loc -> new_val), meme.top)
          print(new_val)
          new_val match{
            case (x: LocVal) => {
              rec2(i + 1, list ::: List[LocVal](x), new_mem)
            }
            case (r: RecordVal) => {
              val new_list = getList(r, List[LocVal]())
              rec2(i + 1, list ::: new_list, new_mem)
            }
            case (r: ProcVal) => {
              val res = gc(r.env, mem)
              val neww_mem = Mem(res.m.++(new_mem.m),mem.top)
              rec2(i + 1, list, neww_mem)
            }
            case _ => rec2(i + 1, list, new_mem)
          }
        }
        else{
          rec2(i + 1, list, mem)
        }
      }
    }
    val new_mem = Mem(new HashMap[LocVal,Val], mem.top)
    val keys = env.keySet.toList
    val list2 = List[LocVal]()
    val res = rec(0, keys, new_mem, list2)
    println("\n\n\n\n\n\n\n")
    val new_res = rec2(0, res._2, res._1)
    println("\n\n",new_res)
    new_res
  }
  
  def apply(program: String): (Val, Mem) = {
    val parsed = MiniCParserDriver(program)
    val res = eval(new Env(), Mem(new HashMap[LocVal,Val],0), parsed)
    (res.v, res.m)
  }

}


object Hw4App extends App {
  
  println("Hello from Hw4!")

}