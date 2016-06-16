package codegen

import Main._
import syntax.transform.Mnemonics
import syntax.Identifier
import syntax.AstSugar._
import semantics.Scope

import scala.collection.JavaConversions._
import java.io.BufferedReader
import java.io.FileReader
import java.io.BufferedWriter



class CppOutput (implicit scope: Scope) {

  val INFIX = List("&&","+","-","*","/","%","||","<")
  val PREFIX = List("!")
  val REDUCTIONS = List("min","max")
  import CppOutput._
  def mne(s: String): String = mn get I(s)
  def exprToFormalParam(e:Expr): String = {
    e match {
      case Interval(name: String) =>
        s"DEFINTERVALFUNC(${mne(name)})"
      case _ =>
        ???
    }
  }
  
  def exprToArg(e:Expr): String = {
    e match {
      case Interval(name: String) =>
        s"PARAM(${mne(name)})"
      case _ =>
        exprToCode(e)
    }
  }
  
  def exprToCode(e:Expr): String = {
    e match {
      case Num(value: Int) =>
        value.toString()
      case GetBound(i: Interval, sel: Lowup) => 
        sel match {
          case LOWER => 
            s"DEFBEGIN(${mne(i.name)})"
          case UPPER =>
            s"DEFEND(${mne(i.name)})"
        }
      case Var(name: String, ii: Interval) =>
        mne(name)
      //Corresponds to MAPSTO
      case FunApp(f, List(FunApp("[]",elts))) if REDUCTIONS.contains(f)=>
        ((elts map exprToCode) reduce ((x,y) => s"${mne(f)}($x,$y)") )
        //s"${f}(${().mkString(",")})"
      case FunApp(f: String, args: List[Expr]) =>
        if (INFIX.contains(f) && args.length == 2) 
          s"(${exprToArg(args(0))} $f ${exprToArg(args(1))})"
        else if (PREFIX.contains(f) && args.length == 1)
          s"($f${exprToArg(args(0))})"
        else{ 
          /*println("BOO: " +args.length.toString() + " "+ 
              (args.map(x=>exprToCode(x))).toString());*/
          s"${mne(f)}(${(args.map(x=>exprToArg(x))).mkString(",")})"
        }
      //f is either FuncPre or FuncDef
      case Slash(isFunction: Boolean, slashes: List[Expr]) =>
        //  assert(!isFunction)    // TODO this assertion is required; but right now isFunction == true when it's not supposed to be
        slashes map exprToCode reduceLeftOption 
          ((x,y) => s"SLASH(${x}, ${y})") getOrElse "UNDEFINED"
        //??? //shouldn't be here anymore
      case Guarded(cond: Expr, v: Expr) =>
        s"GUARDED(${exprToCode(cond)},${exprToCode(v)})"
      case MemRead(arrayName: String, indices: List[Expr]) =>
        s"${mne(arrayName)}(${(indices.map(x=>exprToCode(x))).mkString(",")})"
      case VarB(name: String, lb:Expr, ub: Expr)  =>
        ???
    }
  }
  def repeatChar(char:Char, n: Int) = List.fill(n)(char).mkString
  def addIndent(i:Int,s:String): String = {
    repeatChar('\t',i) + s
  }
  def getLambdas(stmt: Stmt,indent: Int): String = {
    stmt match {
      case Block(l) => ((l map (a => getLambdas(a,indent))) filter (a=> a != "")) mkString "\n"
      case Fork(l) => ((l map (a => getLambdas(a,indent))) filter (a=> a != "")) mkString "\n"
      case If(cond,caseThen,caseElse) => 
        getLambdas(caseThen,indent) + "\n" + getLambdas(caseElse,indent)
      case FunctionCallWithBody(name,args,body) => s"void ${mn.get(name)}(${args map exprToFormalParam mkString ","}){\n${apply(body,indent+1)}\n}"
      case _ => ""
    }
  }
  def apply(fd : FunDef,indent: Int): String = {
    //TODO: Add code to output all lambdas
    
    getLambdas(fd.body,indent) + s"\nvoid ${fd.name}(${fd.args map exprToFormalParam mkString ","}){\n${apply(fd.body,indent+1)}\n}"
  }
  def cilkForkCode(stmts: List[Stmt],indent: Int) : String = {
    stmts match {
      case stmt :: Nil => apply(stmt,indent) + "\n"+ addIndent(indent,"cilk_sync;\n")
      case stmt :: rest => addIndent(indent,s"cilk_spawn ${apply(stmt,0)};\n") + cilkForkCode(rest,indent)
      case Nil => ???
    }
  }
  def apply(s: Stmt, indent: Int): String = {
    //Traverse over Stmt and print with appropriate 
    //Special case for in-fix operators, macros, operator versus function
    val res = s match {
      case DefIntervalSplit(i, ss, whichPart) =>
        addIndent(indent,s"DEFINTERVALSTMT_${whichPart}(${mne(i.name)}, ${mne(ss.name)});")
      case DefIntervalUnion(i, (l,u)) =>
        addIndent(indent,s"DEFINTERVALSTMT_UNION(${mne(i.name)}, ${mne(l.name)}, ${mne(u.name)});")
      case DefVar(v, typ) => 
        addIndent(indent,s"${typ} ${v};")
      case Assign(v,e) => 
        addIndent(indent,s"$v = ${exprToCode(e)};")
      case MemWrite(arrayName,indices,rhs) => 
        addIndent(indent,s"${mne(arrayName)}(${(indices.map(e=>exprToCode(e))).mkString(",")}) = ${exprToCode(rhs)};")
      case FunctionCall(name,params) =>
        addIndent(indent,s"${name}(${(params map exprToArg).mkString(",")});")
      case For(v,lb,ub,dir,stmt) =>
        addIndent(indent,s"FOR_${dir}(${v},${exprToCode(lb)},${exprToCode(ub)}){") + s"\n${apply(stmt,indent+1)}\n" + addIndent(indent,"}")
      case If(Var(v,_),caseThen,Block(List())) if (v == "true")=>
        apply(caseThen,indent)
      case If(cond,caseThen,Block(List())) =>
        addIndent(indent,s"if(${exprToCode(cond)}){\n") + apply(caseThen,indent+1) + "\n" + addIndent(indent,"}\n")
      case If(cond,caseThen,caseElse) =>
        addIndent(indent,s"if(${exprToCode(cond)}){\n") + apply(caseThen,indent+1) + "\n" + addIndent(indent,"} else {\n") + apply(caseElse,indent+1) + "\n" + addIndent(indent,"}\n")
      case Fork(stmts) => //TODO: not here, but get parallel number of each stmt and re-organize AST
        cilkForkCode(stmts,indent)
        //??? //TODO: use cilk primitives as needed 
      case Block(stmts) =>
        (stmts.map(x =>  apply(x,indent))).mkString("\n")
      case Parallel(i, stmt) =>
        apply(stmt,indent) + s"    /*bazinga $i*/"
      case FunctionCallWithBody(name,params,body) => 
        apply(FunctionCall(mn.get(name),params),indent)
      case Verbatim(code) =>
        addIndent(indent,code+"\n")
    };
    res
    
  }
     
}

object CppOutput {

  /*
  val PREFACE_PATH = "./src/codegen/templates/preface.cpp"
  
  def readPreface(filename: String = PREFACE_PATH) = {
    val reader = new BufferedReader(new FileReader(filename))
    reader.lines.iterator.toStream   // can be just 'reader.lines' if we turn on -Xexperimental
  }
  */
  val mn = new Mnemonics {
    override def isIdentifierPart(c: Character) = c < 0x100 && super.isIdentifierPart(c)
  }
  
  val PREFACE = """
#include "preface.h"
#include "input.h"
"""
  
  def writePrefaceTo(w: BufferedWriter) = {
    w.write(PREFACE); w.newLine();
    //readPreface().foreach(x => { w.write(x); w.newLine() })
  }

}
