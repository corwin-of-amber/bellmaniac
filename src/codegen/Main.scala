
package codegen

import scala.collection.JavaConversions._
import org.rogach.scallop.ScallopConf
import org.rogach.scallop.ScallopOption
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.FileReader
import ui.CLI
import com.mongodb.util.JSON
import com.mongodb.BasicDBObject
import report.data.DisplayContainer
import syntax.Formula
import syntax.AstSugar._
import syntax.Tree
import semantics.LambdaCalculus._
import semantics.TypedTerm.{preserve, typeOf_!}
import scala.collection.mutable.ListMap
import syntax.Identifier
import semantics.Prelude
import semantics.TypedTerm
import syntax.transform.Mnemonics
import semantics.Scope
import synth.pods.ConsPod
import report.console.NestedListTextFormat
import report.console.NestedListTextFormat
import java.io.BufferedWriter
import java.io.FileWriter
import java.io.File
import semantics.TranslationError
import report.data.SerializationError
import com.mongodb.DBObject
import syntax.AstSugar._
import synth.engine.OptimizationPass
import semantics.TypeTranslation.In

object Main {
  
  class CommandLineConfig(args: List[String]) extends ScallopConf(args toList) {
    val filenames = trailArg[List[String]](required=true) //opt[String]("files", required=true).map((_.split(",").toList))
    val outputfile = opt[String]("outfile", default=Some("output.cpp"))
  }
 
  def isAllDigits(x: String) = x forall Character.isDigit
  
  abstract class Expr

  abstract class Direction
  case object BWD extends Direction
  case object FWD extends Direction
  
  abstract class Lowup
  case object LOWER extends Lowup
  case object UPPER extends Lowup
  
  val fPreDefs = List("min","max","cons","+","ψ","θ","-","w","?","nil","δ","d","S","w'", "v")
  val memPreDefs = List("ψ","θ")
  val intervalDefs = List('I','J','K','L','M','N')
  val varList = List("i","j","k","p","q")
  val builtinIntervals = Set("R","N","B") 
  
  //TODO: incorporate bazinga info!   
  case class Num(value: Int) extends Expr
  case class Interval(name: String) extends Expr
  case class GetBound(i: Interval, sel: Lowup) extends Expr
  case class Var(name: String, ii: Interval) extends Expr
  case class FunApp(f: String, args: List[Expr]) extends Expr
  case class Slash(isFunction: Boolean, slashes: List[Expr]) extends Expr
  case class Guarded(cond: Expr, v: Expr) extends Expr
  case class MemRead(arrayName: String, indices: List[Expr]) extends Expr
  case class VarB(name: String, lb:Expr, ub: Expr) extends Expr
  

  case class FunDef (name: String,args: List[Interval],body:Block)
  
  abstract class Stmt {
    def toPrettyTree : Tree[String] = this match {
      case DefIntervalSplit(i, superset, whichPart) =>
        new Tree(s"${i} = ${whichPart}(${superset});")
      case DefIntervalUnion(i, (lower, upper)) =>
        new Tree(s"${i} = UNION(${lower}, ${upper});")
      case DefVar(v, typ) => 
        new Tree(s"${typ} ${v};")
      case Assign(v,e) => new Tree(s"$v = $e;")
      case MemWrite(arrayName,indices,rhs) => 
        new Tree(s"$arrayName(${indices.mkString(",")}) = ${rhs};")
      case FunctionCall(name,params) =>
        new Tree(s"$name(${params.mkString(",")});")
      case For(v,lb,ub,dir,stmt) =>
        new Tree(s"FOR(${v},${lb},${ub},${dir})", List(stmt.toPrettyTree))
      case If(cond,caseThen,caseElse) =>
        new Tree(s"if(${cond})", List(caseThen.toPrettyTree, caseElse.toPrettyTree))
      case Fork(stmts) => //TODO: not here, but get parallel number of each stmt and re-organize AST
        new Tree("{fork}", stmts map (_.toPrettyTree) )
      case Block(stmts) =>
        new Tree("{}", stmts map (_.toPrettyTree) )
      case Parallel(i, stmt) =>
        new Tree(s"$i:", List(stmt.toPrettyTree))
      case FunctionCallWithBody(name,params,body) =>
        new Tree(s"$name(${params.mkString(",")})",List(body.toPrettyTree))
      case Verbatim(code) => 
        new Tree(code)
    }
  }
  case class DefIntervalSplit(I: Interval, superset: Interval, whichPart: Lowup) extends Stmt
  case class DefIntervalUnion(I: Interval, subparts: (Interval, Interval)) extends Stmt
  case class DefVar(v: String, typ: String) extends Stmt
  case class Assign(v: String, e:Expr) extends Stmt
  case class MemWrite(arrayName: String,indices: List[Expr],rhs: Expr) extends Stmt
  case class FunctionCall(name: String, params: List[Expr]) extends Stmt
  case class For(v:String,lb:Expr,ub:Expr,dir:Direction,stmts:Stmt) extends Stmt
  case class If(cond:Expr,caseThen:Stmt,caseElse:Stmt) extends Stmt
  case class Fork(stmts:List[Stmt]) extends Stmt//can run these in parallel!
  case class Block(stmts:List[Stmt]) extends Stmt
  case class Parallel(i:Int, s:Stmt) extends Stmt
  case class FunctionCallWithBody (name: Identifier, params: List[Interval], body:Block) extends Stmt
  case class Verbatim(code: String) extends Stmt
  
  def getIntervalsUsed(e: Expr) : Set[String] = e match {
    case Num(value) => Set()
    case Interval(name) => Set(name)
    case GetBound(Interval(name), sel: Lowup) => Set(name)
    case Var(v, Interval(name)) => Set() //Set(name)
    case FunApp(f: String, args: List[Expr]) => (args map getIntervalsUsed).flatten.toSet
    case Slash(isFunction: Boolean, slashes: List[Expr]) => (slashes map getIntervalsUsed).flatten.toSet
    case Guarded(cond: Expr, v: Expr) => (List(cond,v) map getIntervalsUsed).flatten.toSet
    case MemRead(arrayName: String, indices: List[Expr]) => (indices map getIntervalsUsed).flatten.toSet
    case VarB(name: String, lb:Expr, ub: Expr) => (List(lb,ub) map getIntervalsUsed).flatten.toSet
  }
  
  def getVariablesUsed(e: Expr) : Set[String] = e match {
    case Num(value) => Set()
    case Interval(name) => Set()
    case GetBound(Interval(name), sel: Lowup) => Set()
    case Var(v, Interval(name)) => Set(v)
    case FunApp(f: String, args: List[Expr]) => (args map getVariablesUsed).flatten.toSet
    case Slash(isFunction: Boolean, slashes: List[Expr]) => (slashes map getVariablesUsed).flatten.toSet
    case Guarded(cond: Expr, v: Expr) => (List(cond,v) map getVariablesUsed).flatten.toSet
    case MemRead(arrayName: String, indices: List[Expr]) => (indices map getVariablesUsed).flatten.toSet
    case VarB(name: String, lb:Expr, ub: Expr) => (List(lb,ub) map getVariablesUsed).flatten.toSet
  }
  
  def getIntervalsUsed(s: Stmt) : Set[String] = {
    def getIntervalsUsedAux(s: Stmt) : Set[String] = s match {
      case DefIntervalSplit(Interval(i), superset, whichPart) =>
        Set(i)
      case DefIntervalUnion(Interval(i), (lower, upper)) =>
        Set(i)
      case DefVar(v, typ) => 
        Set()
      case Assign(v,e) => 
        getIntervalsUsed(e)
      case MemWrite(arrayName,indices,rhs) => 
        getIntervalsUsed(rhs)
      case FunctionCall(name,params) =>
        //println("FunctionCall :" + name + " " + params.toString)
        (params flatMap getIntervalsUsed).toSet
        //??? //Cannot visit this - Why was this?
      case For(v,lb,ub,dir,stmt) =>
        getIntervalsUsed(lb) ++ getIntervalsUsed(ub)  ++ getIntervalsUsedAux(stmt)
      case If(cond,caseThen,caseElse) =>
        getIntervalsUsed(cond) ++ getIntervalsUsedAux(caseThen) ++ getIntervalsUsedAux(caseElse)
      case Fork(stmts) => //TODO: not here, but get parallel number of each stmt and re-organize AST
        (stmts map getIntervalsUsedAux).flatten.toSet
      case Block(stmts) =>
        (stmts map getIntervalsUsedAux).flatten.toSet
      case Parallel(i, stmt) =>
        getIntervalsUsedAux(stmt)
      case Verbatim(code) => Set()
    }
    getIntervalsUsedAux(s) -- builtinIntervals //TODO: Use library of built-in sets from Bellmania Frontend
  }
  implicit val cc = new DisplayContainer
  
  def isSlash(t: Term): Option[(List[Term])] = 
    if (t =~ ("/", 2)) { 
      isSlash(t.subtrees(0)) match {
        case Some(slashes) => Some(slashes :+ t.subtrees(1))
        case _ => Some(t.subtrees)
      }
    }
    else if (t =~ (":", 2)) isSlash(t.subtrees(1))
    else None
  
  object P {
    def unapply(t: Term): Option[(String, Term, List[Term])] = {
      if (t.isLeaf) {
          Some(("LEAF",t,null))
          //if (typeOf_!(t).isLeaf || (ctx.vars contains t) || t.root.literal.isInstanceOf[Int]) t
          //else TypedTerm(t, scalar)
      }
      else if (t =~ ("|!", 2)) { 
        //Guarded Expr
        val v = t.subtrees(0);
        val cond = t.subtrees(1);
        Some(("GUARD",cond,List(v)))
      }
      else if (t =~ ("<", 2) || t =~ ("<₁", 2) || t =~ ("<₂", 2)) {     // Oh the subscripts are pretty damn hackish
        //LT Expr
        Some(("LT",t.subtrees(0),List(t.subtrees(1))))
      }
      else if (t =~ ("∧", 2)) { 
        //AND Expr
        Some(("AND",t.subtrees(0),List(t.subtrees(1))))
      }
      else if (t =~ ("∨", 2)) { 
        //OR Expr
        Some(("OR",t.subtrees(0),List(t.subtrees(1))))
      }
      else if (t =~ ("¬", 1)) {
        Some(("NOT", t.subtrees(0), null))
      }
      else if (t =~ ("program", 1)){//higher level program
        unapply(t.subtrees(0))
      }
      else if (t =~ ("fix", 1)){//fixed point
        Some(("FIX",t.subtrees(0),null))
      }
      else if (t =~ (":", 2)){
        //Just a label, ignore LHS
        if (t.subtrees(0).root.literal.toString() == "bazinga")
          Some(("BAZINGA",t.subtrees(0).subtrees(0),List(t.subtrees(1))))
        else unapply(t.subtrees(1))
        
      }
      else if (isInterval(t.root) && t.subtrees.size == 1){
        Some(("IN_INTERVAL",T(t.root), List(t.subtrees(0))))
      }
      else{
        isSlash(t) match{
          case Some(slashes) => Some(("SLASH",null,slashes))
          case _ =>
            isApp(t) match {
              case Some((f, args)) =>
                Some(("APPLY",f, args))
              case _ =>
                isAbsBaz(t) match {
                  case Some((vars, body, lbls)) => 
                    val baz = for (x <- lbls if (x =~ ("bazinga",1))) yield x.subtrees(0)
                    if (baz.isEmpty)
                      Some(("MAPSTO",body, vars))
                    else
                      Some("BAZINGA",baz(0),List((vars :\ body)( _ ↦ _)))
                  case _ =>
                    Some(("NONE END:  " + t.root.literal.toString() + "|" +t.subtrees.size.toString()),null,null)
                }
            }
        }
      }
    }
  }
  
    // returns args and body
  def uncurryb(fun: Term): (List[Term], Term, List[Term]) = {
    if (fun =~ ("↦", 2))
      uncurryb(fun.subtrees(1)) match { case (args, body, lbls) => (fun.subtrees(0) :: args, body, lbls) }
    else if (fun =~ (":", 2)) {
      val (a,b,c) = uncurryb(fun.subtrees(1))
      (a,b,fun.subtrees(0) :: c)
    }
    else (List(), fun, List())
  }
  def isAbsBaz(t: Term): Option[(List[Term], Term, List[Term])] =
    if (t =~ ("↦", 2)) Some(uncurryb(t))
    else if (t =~ (":", 2)) {
      isAbsBaz(t.subtrees(1)) match {
        case Some((a,b,c)) => Some((a,b,t.subtrees(0) :: c))
        case _ => None
      }
    }
    else None
  
  object ListP {
    def unapply(t: Term) = {
      ConsPod.`⟨ ⟩?`(t)
    }
  }
  case class Context (
      val inputArray: Identifier, 
      val fixVar: Option[Identifier],
      val loops: Map[String, Direction],
      val insideFix: Boolean = false, 
      val localVars : List[Term] = List(), 
      val tmpVar: String = ""
      ) {
    def inp (i: Identifier) = {
        Context(i, fixVar, loops, insideFix, localVars, tmpVar) 
      }  
    def fix(v: Identifier) = {
      assert(insideFix && fixVar.isEmpty)
      Context(inputArray, Some(v), loops, insideFix, localVars, tmpVar) 
    }
    def setFix = {
      assert(! insideFix)
      Context(inputArray, fixVar, loops, true, localVars, tmpVar) 
    }
    def + (i: Term) = {
      Context(inputArray, fixVar, loops, insideFix,localVars :+ i,tmpVar) 
    }
    def ++ (l: List[Term]) = {
      Context(inputArray, fixVar, loops, insideFix,localVars ++ l,tmpVar) 
    }
    def tmp (s: String) = {
      Context(inputArray, fixVar, loops, insideFix,localVars,s) 
    }
  }
  
  def isRoutine(i: Identifier)= (i.literal.toString().indexOf('[') >= 0)
  
  def isScalar(v: Term) = (typeOf_!(v).isLeaf)
  
  def isInterval(i: Identifier)= i.kind == "set"
  
  def toInterval(typ: Term) = {
    Interval(typ.leaf.literal.toString)
  }
  
  def toVar(t:Term) = {
    Var(t.leaf.literal.toString,toInterval(typeOf_!(t)))
  }
  
  def FormulaToExpr(ff:Term) (implicit ctx: Context) : Expr = {
    ff match {
      case P("LEAF",t:Term,null) =>
          val v = t.root.literal.toString
          if (t.root.kind == "variable" && typeOf_!(t).isLeaf) Var(v,Interval((typeOf_!(t).leaf).literal.toString()))
          else if (isInterval(t.leaf)) Interval(v)
          else if (v=="true") Var("true",Interval("B"))
          else if (v.matches("[+-]?\\d+")) Num(Integer.parseInt(v))
          else throw new Exception("Leaf not analyzed: " + t.toString())
      case P("GUARD",cond:Term,List(v:Term)) =>
        Guarded(FormulaToExpr(cond),FormulaToExpr(v))
      case P("LT",a:Term, List(b:Term)) =>
        FunApp("<",List(FormulaToExpr(a),FormulaToExpr(b)))
      case P("AND",a:Term, List(b:Term)) =>
        FunApp("&&",List(FormulaToExpr(a),FormulaToExpr(b)))
      case P("OR",a:Term, List(b:Term)) =>
        FunApp("||",List(FormulaToExpr(a),FormulaToExpr(b)))
      case P("NOT",a:Term, _) =>
        FunApp("!",List(FormulaToExpr(a)))
      case P("FIX",t:Term,null) =>
        ???
        //FunApp(FuncPre("FIX"),List(FormulaToExpr(t)))
      case ListP(elts) =>
        FunApp("[]",(elts map FormulaToExpr))
      case P("APPLY",f,args) if (f.isLeaf)=>
        if (ctx.inputArray == f.root || ctx.fixVar == Some(f.root)){
          MemRead(ctx.inputArray.literal.toString,(args map FormulaToExpr))
        }
        else {
          if ( f.root.literal.toString == "θ" && ctx.fixVar == None){
            println("THETA")
          }
          println(s"FUNCTION: ${f.root.literal.toString}, FIXVAR: ${ctx.fixVar.toString}")
          FunApp(f.root.literal.toString, (args map FormulaToExpr))
        }
      case P("MAPSTO",body,vars) =>
        throw new Exception("MAPSTO in Expr")
        //val vs = (vars map FormulaToExpr);
        //FuncDef(vs,FormulaToExpr(body))
      case P("BAZINGA",baz,List(e)) =>
        ???
      case P("SLASH",null,slashes) =>
        val isFunc = (typeOf_!(ff).isLeaf);
        Slash(isFunc,(slashes map FormulaToExpr))
      case P("IN_INTERVAL",interval,List(i)) =>
        val intv = interval.root.literal.toString();
        FunApp("In", List(Interval(intv),FormulaToExpr(i)))
      case _ =>
        throw new Exception(s"Unreognized operation: ${ff.root.literal}  (${ff.subtrees.size}-ary ${ff.root.kind})")
    }
  }
  var tmpCtr = 0
  
  def createTempName() = {
    tmpCtr = tmpCtr +1
    "tmp" + tmpCtr
  }
  
  val minFn = Prelude.min
  val maxFn = Prelude.max
  
  val reduceFns = List(minFn,maxFn)
  val reduceFnsStr = List("min","max")
  /* Predicates in Conditions affecting Bounds */

  def getAndPreds(expr: Expr): List[Expr] = {
     expr match {
      case FunApp("&&",List(p1,p2)) => List.concat(getAndPreds(p1), getAndPreds(p2))
      case _ => List(expr)
    }
  }
  def getOrPreds(expr: Expr): List[Expr] = {
     expr match {
      case FunApp("||",List(p1,p2)) => List.concat(getOrPreds(p1), getOrPreds(p2))
      case _ => List(expr)
    }
  }
  def mLower(l1:Expr,l2:Expr) = {
    (l1,l2) match {
      case (null,l2) => l2
      case (l1,null) => l1
      case (l1,l2) => FunApp("max",List(l1,l2))
    }
  }
  def mUpper(u1:Expr,u2:Expr) = {
    (u1,u2) match {
      case (null,u2) => u2
      case (u1,null) => u1
      case (u1,u2) => FunApp("min",List(u1,u2))
    }
  }
  def mergeBounds(b1: (Expr,Expr,Seq[Expr]), b2: (Expr,Expr,Seq[Expr])): (Expr,Expr,Seq[Expr]) = {
    val (l1,u1,s1) = b1
    val (l2,u2,s2) = b2
    (mLower(l1,l2),mUpper(u1,u2),s1 ++ s2)
  }
  def isTrivial(e:Expr) ={
    e match {
      case FunApp("In",List(Interval(ii),Var(j,Interval(jj)))) if (ii == jj) => true
      case _ => false
    }
  }
  def getBoundsFromPred(e:Expr,varStr:String) :(Expr,Expr,Seq[Expr]) = {
    e match {
      case FunApp("<",List(Var(i,inti), erhs))if i == varStr => (null,erhs,Seq())
      case FunApp("<",List(elhs,Var(i,inti))) if i == varStr=> (FunApp("+",List(elhs,Num(1))),null,Seq())
      case FunApp("In",List(Interval(intv), Var(i,_))) if (i == varStr)=> 
        (GetBound(Interval(intv),LOWER),GetBound(Interval(intv),UPPER),Seq())
      case FunApp("In",List(Interval(intv), FunApp("-",List(Var(i,_),Num(n))) )) if (i == varStr)=> 
        (FunApp("+",List(GetBound(Interval(intv),LOWER),Num(n))),
            FunApp("+",List(GetBound(Interval(intv),UPPER),Num(n))),
            Seq())
      case _ => (null,null,Seq(e) filterNot isTrivial) //Be careful
        
    }
  }
  def crossBounds[Y] (xs:List[Y],ys:List[Y]): List[(Y,Y)] = {
    for (x <- xs; y <- ys) yield (x, y)
  }
  
  def mergeSplitBounds(b1s: List[(Expr,Expr,Seq[Expr])],b2s: List[(Expr,Expr,Seq[Expr])]) : List[(Expr,Expr,Seq[Expr])] = {
    crossBounds(b1s, b2s) map { case (b1,b2) => mergeBounds(b1,b2) }
  }
  def getCNFBounds(expr:Expr, i:String): List[List[(Expr,Expr,Seq[Expr])]] = {
    val ands = getAndPreds(expr)  
    val cnf = ands.map(getOrPreds)
    println("CNF: " + cnf.toString)
    cnf  map (l => l map ( e => getBoundsFromPred(e,i)))
  }
  
  def getSplitBounds(expr:Expr,i:String) : List[(Expr,Expr,Seq[Expr])] = {
    val cnfBounds = getCNFBounds(expr,i)
    cnfBounds reduceLeft mergeSplitBounds
  }
  
  
  def liftLoops(ff:Term)(implicit ctx:Context) = {
    //find all loops that are at the top level
    //compute definitionStmt and computationStmt for them
    //replace them with appropriate tmp var
    //return {definitionStmt;computationStmt}* block
    //TODO: WHEN can I say that I've found a subtree that is independent and should be computed with a temporary?
    val internals = ff.nodes collect {   
      case st@P("APPLY",f,List(P("MAPSTO",body,vars))) if (reduceFns contains f)
        =>
          //found one
          val condition = OptimizationPass.surroundingGuards(ff, st) match {
            case Some(l) => 
              FormulaToExpr(&&(l))
            case None =>
              ???
          }
          if (vars.size == 1){
            val tmpStr = createTempName()
            val ivlVar = Interval(typeOf_!(vars(0)).leaf.literal.toString)
            val ivlBody = Interval(typeOf_!(body).leaf.literal.toString)
            println("BODY inner loop: " + body.toPretty)
            val forStmt = For(
                vars(0).root.literal.toString,
                GetBound(ivlVar,LOWER),
                GetBound(ivlVar,UPPER),
                FWD,   // direction does not really matter here, all reductions are associative
                Assign(tmpStr,FunApp(f.root.literal.toString, List(
                                    Var(tmpStr,ivlBody),
                                    FormulaToExpr(body)
            ))))
            val conditionedForStmt = If(condition,forStmt,Block(List()))
            val initVar = Var(s"INIT${f.root.literal}".toUpperCase,ivlBody)
            val blk = Block(List(DefVar(tmpStr, "TYPE"), Assign(tmpStr, initVar),conditionedForStmt )) //TODO: Figure out correcttype from interval string?
            ((st,T($TV(tmpStr).root,List())),blk)
          }
          else ???
    }
    
    (TypedTerm.replaceDescendants(ff,internals map (_._1) toList)(scope) 
        ,simplifyStmtN(10,(Block(internals map (_._2) toList))))
    //simplifyStmt(Block((ff.subtrees map (t => InternalSub(t,ff)))))
  }
 
  
  def FormulaToStmt(ff: Term) (implicit ctx: Context): Stmt = {
    //println(ff.toPretty); println(ctx)
    ff match {
      case P("LEAF", t, null) =>
        if (t.root == ctx.inputArray) {
          Block(List())
        }
        else {
          println(t)
          println(ctx.inputArray)
          ???
        }
      case P("GUARD", cond, List(v)) =>
        If(FormulaToExpr(cond),FormulaToStmt(v),Block(List()))
      case P("FIX", t, null) =>
        if (ctx.fixVar.isDefined) throw new Exception("FixVar found already")
        else FormulaToStmt(t)(ctx.setFix)
      case T(`@:`.root, List(T(`↦`.root, List(va, body)), arg)) =>
          if (va.leaf.literal.toString().startsWith("?")){ //
            FormulaToStmt(body)
          }
          else
            Block(List(FormulaToStmt(arg),
                FormulaToStmt(body)(ctx inp va.leaf) )) 

      case P("APPLY",f,args) =>
        if (f.isLeaf && isRoutine(f.leaf)) {
          //A[I,J] etc
          val style = "rec";
          val name :: params = f.root.literal.toString().split(raw"[\[,\]]").toList;
          FunctionCall(s"func${name}_${style}",(params map (Interval(_))))
        }
        else {
          f match {
            case P("SLASH",null,quads) => 
              Block(quads map (q => q :@(args) ) map FormulaToStmt)
            case _ => ???
          }
        }
      case P("MAPSTO",body,vars) =>
        //has to become a for loop, for on variables of MAPSTO - fixVar if its there
        //all variables must be scalar types
        val (loopvars,ctxWFix) = 
          if (ctx.insideFix && ctx.fixVar.isEmpty) 
            (vars.tail,ctx fix vars.head.leaf)
          else
            (vars,ctx)
        loopvars foreach (v => if (! isScalar(v)) 
          throw new Exception("expected scalar variable"))
        val newCtx =  ctxWFix ++ loopvars
        println(s"FIXVAR: ${ctxWFix.fixVar},BODY: ${body.toPretty}") 
        if (! isScalar(body)){ 
          FormulaToStmt(body)(newCtx)
        }
        else {
        //check if body has other loops(only immediate ones), if yes,
        //replace those loops with tmp in the expression tree and get Stmts (using FormulaToStmt) for tmp computation
          val (newBody,tmpStmt) = liftLoops(body)(newCtx)
          val initOrig = MemWrite(ctx.inputArray.literal.toString,
              (newCtx.localVars map toVar),
              FormulaToExpr(newBody)(newCtx))
          val init: Stmt = tmpStmt match {
              case Block(List()) => initOrig
              case _ => Block(List(tmpStmt,initOrig))
              }
          (loopvars :\ init) { (v,inner) => 
              val iV = Interval(typeOf_!(v).leaf.literal.toString)
              For(v.leaf.literal.toString,
                  GetBound(iV,LOWER),
                  GetBound(iV,UPPER),
                  ctx.loops.getOrElse(v.leaf.literal.toString, FWD),
                  inner)
          }
        }
      case P("BAZINGA",baz,List(e)) =>
        //println(s"BAZ: ${e.toPretty}")
        Parallel(Integer.parseInt(baz.root.literal.toString),FormulaToStmt(e))
      case P("SLASH",null,quads) =>
        Block((quads map FormulaToStmt))
      case P("IN_INTERVAL",t,List(v)) =>
        ???
      case _ =>
        throw new Exception("Not analyzed Term: " + ff.root.literal.toString() + "|" + ff.subtrees.size.toString() )
    }
  }
  
  def localIntervalDefs(argIntervals: List[Interval]) : Stmt = {
    val argIntervalIds = argIntervals map (i => S(i.name))
    val unions =
      scope.sorts.mastersHie flatMap { 
      case T(master, List(T(lower, _), T(upper, _)))  if !(argIntervalIds contains master) && 
                                                          (argIntervalIds contains lower) && 
                                                          (argIntervalIds contains upper) =>
        println(s"${master}  ${argIntervalIds.head}")
        println(s"${master}   ${upper}   ${lower}")
        List(DefIntervalUnion(Interval(master.literal.toString), (Interval(lower.literal.toString), (Interval(upper.literal.toString)))))
      case _ => List()
      }
    val splits =
      argIntervals flatMap { interval =>
        val hie = scope.sorts.findSortHie(new Identifier(interval.name)).getOrElse { throw new TranslationError(s"cannot find type '${interval.name}'") }
        hie.subtrees match {
          case x@List(lower, upper) =>
            x zip List(LOWER, UPPER) map { case (s, w) =>
              DefIntervalSplit(Interval(s.root.literal.toString), interval, w)
            }
          case _ => List()
        }
      }
    Block(unions ++ splits)
  }
  
  implicit class StmtConcat(val stmt: Stmt) extends AnyVal {
    def toList =  stmt match { case Block(stmts) => stmts   case _ => List(stmt) }
    def toBlock = stmt match { case b@Block(_)   => b       case _ => Block(List(stmt)) }
    def ++(next: Stmt) = Block(toList ++ next.toList)
  }
  
  val ↦ = TI("↦")
  val `:` = TI(":")
  
  def generateBaseCase(name: String,style: String,argIntervals: List[Interval],elseBranch : Stmt) = {
    If(FunApp("BASE_CONSTRAINT",argIntervals),FunctionCall(s"func${name}_${style}",argIntervals),elseBranch)
  }
  
  var loopDirections: Map[String, Direction] = Map.empty  // it's horrible to have a global for this @@@
  
  var scope: Scope = new Scope
  
  var copyOptRanges : List[Interval] = List()
  
  def addCopyOpt(e: Expr)(implicit ctx: List[String], writeRegions: List[List[Interval]], blockDimensions : Set[Interval] ) : Expr = {
    e match {
      case FunApp(f: String, args: List[Expr]) => FunApp(f,(args map addCopyOpt))
      case Slash(isFunction: Boolean, slashes: List[Expr]) => Slash(isFunction, slashes map addCopyOpt)
      case Guarded(cond: Expr, v: Expr) => Guarded(addCopyOpt(cond), addCopyOpt(v))
      case MemRead(arrayName: String, List(Var(i,ii),Var(j,jj))) if (ctx.indexOf(i) > ctx.indexOf(j) && !regionOverlaps(List(ii,jj),writeRegions) && (List(ii,jj) forall blockDimensions.contains)) => 
        if (!copyOptRanges.isEmpty && copyOptRanges != List(ii,jj)) e
        else {
          copyOptRanges = List(ii,jj) 
          FunApp(arrayName+ "CopyOpt", List(Var(i,ii),Var(j,jj),Var(ii.name,ii),Var(jj.name,jj)))
        }
      case _ => e
    }
  }
  
  def addCopyOpt(block: Stmt) (implicit ctx: List[String], writeRegions: List[List[Interval]],blockDimensions : Set[Interval] ) : Stmt = {
    block match {
      case For(v,lb,ub,dir,body) =>
        For(v,lb,ub,dir,addCopyOpt(body)(ctx :+ v,writeRegions, blockDimensions))
      case Parallel(i,stmt) => Parallel(i,addCopyOpt(stmt))
      case Block(l) => Block(l map addCopyOpt)
      case If(cond,caseThen,caseElse) =>
        If(cond,addCopyOpt(caseThen),addCopyOpt(caseElse))
      case MemWrite(arrayName,indices,rhs) => 
        MemWrite(arrayName,indices,addCopyOpt(rhs))
      case Assign(v, e) => 
        Assign(v,addCopyOpt(e))
      case _ => block
    }
  }
  case class CannotCopyOptimize() extends Exception
  
  def collectWriteRegions(block : Stmt) : List[List[Interval]] = block match {
    case For(v,lb,ub,dir,body) =>
        collectWriteRegions(body)
    case Parallel(i,stmt) => collectWriteRegions(stmt)
    case Block(l) => l flatMap collectWriteRegions
    case If(cond,caseThen,caseElse) =>
      collectWriteRegions(caseThen) ++ collectWriteRegions(caseElse)
    case MemWrite(arrayName,indices,rhs) => 
      List(
        indices map {
          case Var(i,ii) => ii
          case _ => throw CannotCopyOptimize()
        }
      )
    case _ => List()
  }
  
  def regionOverlaps(region: List[Interval], withRegions:  List[List[Interval]]) = {
    withRegions.exists { 
      rightRegion =>   (region.length == rightRegion.length) && 
              ((region zip rightRegion) forall  { case (x,y) => intervalOverlaps(x,y)} ) 
      }
  }
  
  def intervalOverlaps(I : Interval, J: Interval) = {
    I.name == J.name
    //TODO: Use info from Scope in case I,J have subset relationship
  }
  
  def prepareCopyOpt(s: Stmt): Stmt = {
    if (!copyOptRanges.isEmpty){
      val s1 = Verbatim("__declspec(align(ALIGNMENT)) TYPE V[B * B];")
      val s2 = FunctionCall("copy_dist_part", List(Var("V",Interval("U")),copyOptRanges(0), copyOptRanges(1)))
      Block(List(s1,s2,s))
      //
	    //copy_dist_part(V,PARAM(K1),PARAM(K2));
    }
    else s
      
  }
  def FormulaToFunction(name: String,style: String, argIntervals: List[Interval], ff:Term) : FunDef = {
    copyOptRanges = List()
    val localDefs = localIntervalDefs(argIntervals)
    val blockWOCilk = FormulaToFunction(ff)
    val block = blockWOCilk match {
      case Block(l) if (style == "rec") => Block(cilkParallelize(l))
      case _ => blockWOCilk
    }
    val blockWCO = if (style == "loop") prepareCopyOpt(addCopyOpt(block)(List(),collectWriteRegions(block),argIntervals.toSet)) else block
    val body = localDefs ++ blockWCO
    FunDef(s"func${name}_${style}", argIntervals, (if (style == "rec") generateBaseCase(name,"loop",argIntervals,body) else body).toBlock)
  }
  
  def FormulaToFunction(ff: Term) : Stmt = {
    //find inputArray
    ff match {
      case T(`↦`.root,List(v,body)) =>
        simplifyStmtN(10,FormulaToStmt(body)(Context(v.leaf, None, loopDirections)))
      case T(Prelude.program.root,List(body)) => 
        FormulaToFunction(body)
      case T(`:`.root,List(label,body)) =>
        FormulaToFunction(body)
      case _ => throw new Exception("Cannot find inputArray at the top level")
   }
  }
  
  def stripColons(t:Term): Term = {
    if (t =~ (":",2) && t.subtrees(0).root != "bazinga") {
      //println(t.subtrees(0).root.literal.toString)
      stripColons(t.subtrees(1))
    }
    else TypedTerm.preserve(t, T(t.root,t.subtrees map stripColons)) 
  }
  def cilkParallelize(l: List[Stmt]) : List[Stmt]= {
    l match {
      case Nil => List()
      case stmt :: rest => 
        stmt match {
          case Parallel(i, s) =>
            //Find all Parallel statements from rest that are level i and put them in a Fork
            var parsi : List[Stmt] = List(s)
            var newrest : List[Stmt] = List()
            for (pstmt <- rest){
              pstmt match {
                case Parallel(iprime,sprime) if (i == iprime) => 
                  parsi = parsi :+ sprime
                case _ => 
                  newrest = newrest :+ pstmt
              }
            }
            def forceFunctionCall(sprime: Stmt) = { 
              //Wraps sprime statement in a function if it is not a function call
              sprime match {
                    case FunctionCall(f,_) => sprime
                    case _ => //Wrap it in a function
                      FunctionCallWithBody($I("func"),
                          getIntervalsUsed(sprime).toList map (a => Interval(a)),sprime.toBlock)
                  }
            }
            Fork(parsi map forceFunctionCall) ::  cilkParallelize(newrest)
          case _ => 
            stmt :: cilkParallelize(rest)
        }
    }
  }
  def simplifyExprInStmt(s:Stmt)(implicit loopBounds: List[(String,Expr,Expr)]) : Stmt= {
    s match {
      case Block(l) => Block(l map simplifyExprInStmt)
      case Fork(l) => Fork(l map simplifyExprInStmt)
      case Parallel(i, s) => Parallel(i, simplifyExprInStmt(s))
      case For(v,lb,ub,dir,stmts)  => For(v,simplifyExpr(lb),simplifyExpr(ub),dir,simplifyExprInStmt(stmts))
      case If(cond,caseThen,caseElse) => If(simplifyExpr(cond), simplifyExprInStmt(caseThen), simplifyExprInStmt(caseElse))
      case FunctionCallWithBody(name,params,Block(l)) => FunctionCallWithBody(name,params,Block(l map simplifyExprInStmt))
      case DefIntervalSplit(ii, superset, whichPart)  => DefIntervalSplit(ii, superset, whichPart) 
      case DefIntervalUnion(ii, subparts)  => DefIntervalUnion(ii, subparts)
      case DefVar(v, typ)  => DefVar(v, typ) 
      case Assign(v, e)  =>  Assign(v, simplifyExpr(e)) 
      case MemWrite(arrayName,indices,rhs)  => MemWrite(arrayName,indices map simplifyExpr,simplifyExpr(rhs))
      case FunctionCall(name, params)  => FunctionCall(name, params map simplifyExpr)  
      case Verbatim(code) => Verbatim(code)
    }
  }
  
  def isSubset(small: String,big: String) = {
    val hie = scope.sorts.findSortHie(S(big)).getOrElse { throw new TranslationError(s"cannot find type '${big}'") }
    (hie.nodes map (_.root)) contains S(small)
  }
  
  def leq(a: Expr, b: Expr): Boolean = {
    //if a is known to be less than or equal to b return true
    //else return false
    (a,b) match {
      case (GetBound(Interval(i1), LOWER),GetBound(Interval(i2), LOWER)) =>
        if (isSubset(i2,i1)) true
        else false
      case (GetBound(Interval(i1), UPPER),GetBound(Interval(i2), UPPER)) =>
        if (isSubset(i1,i2)) true
        else false
      case _ => false
    }
  }
  
  def simplifyExpr(e:Expr)(implicit loopBounds: List[(String,Expr,Expr)]) : Expr = {
    e match { //TODO: Debug why FunApp(In,List(Interval(J₀), Var(i,Interval(J₀)) doesn't simplify?
      case FunApp(f1,List(a,b)) if (simplifyExpr(a) == simplifyExpr(b)) && (reduceFnsStr contains f1) => simplifyExpr(a)
      case FunApp(f1,List(FunApp(f2,List(x,y)),b)) if ( (simplifyExpr(x) == simplifyExpr(b)) || (simplifyExpr(y) == simplifyExpr(b))) && f1==f2 && (reduceFnsStr contains f1) => 
        simplifyExpr(FunApp(f1,List(x,y)))
      //case FunApp("In",List(Interval(jj),Var(i,Interval(ii)))) if ii == jj => Var("true",Interval("B")) - This is not sound, Cannot rely on the interval with Variable as being already enforced
      //This interval should be found from loop level
      case FunApp("min",List(a,b)) if leq(a,b) => a
      case FunApp("min",List(a,b)) if leq(b,a) => b
      case FunApp("max",List(a,b)) if leq(a,b) => b
      case FunApp("max",List(a,b)) if leq(b,a) => a        
      case FunApp("&&",List(Var("true",_),b)) => simplifyExpr(b)
      case FunApp("&&",List(a,Var("true",_))) => simplifyExpr(a)
      case Num(value) => e
      case Interval(name) => e
      case GetBound(i,sel) => e
      case Var(name, ii) => e
      case FunApp(f, args) => FunApp(f, args map simplifyExpr)
      case Slash(isFunction, slashes) => Slash(isFunction, slashes map simplifyExpr)
      case Guarded(cond,v) =>  Guarded(simplifyExpr(cond),simplifyExpr(v))
      case MemRead(arrayName,indices) => MemRead(arrayName,indices map simplifyExpr)
      case VarB(name, lb, ub) => VarB(name, simplifyExpr(lb), simplifyExpr(ub))
    }
  }
  def simplifyOverallStmt (s:Stmt) : Stmt = simplifyExprInStmt(simplifyStmt(s))(List())
  
  def simplifyStmtN(n:Int,stmt:Stmt): Stmt = {
    Function.chain(List.fill(n)(simplifyOverallStmt _))(stmt)
  }
  
  def simplifyStmt(stmt: Stmt): Stmt = {
    stmt match {
      case Block(l) => 
        //look at each child - if its a Block itself just lift it up
        val blockList = l map simplifyStmt flatMap (_.toList)
        if (blockList.size == 1) blockList.head
        else Block(blockList)
      case Fork(l) => 
        //look at each child - if its a Block itself just lift it up
        val blockList = l map simplifyStmt flatMap (_.toList)
        Fork(blockList)
      case Parallel(i, s) => Parallel(i, simplifyStmt(s))
      case For(i,lb,ub,dir,If(cond,caseThen,Block(List()))) if (!(getVariablesUsed(cond) contains i)) => 
        If(cond,For(i,lb,ub,dir,simplifyStmt(caseThen)),Block(List()))
      case For(i,lb,ub,dir,If(cond,caseThen,Block(List()))) =>
        val spBounds = getSplitBounds(cond,i) map (lu => mergeBounds(lu,(lb,ub,Seq())))
        def makeBigAnd(conds: Seq[Expr]) = {
          conds reduceOption ((a,b) => FunApp("&&",List(a,b))) getOrElse Var("true",Interval("B"))
        }
        Block(spBounds map {case (l,u,conds) => 
          val ifStmt = if (conds.isEmpty) simplifyStmt(caseThen) else If(makeBigAnd(conds),simplifyStmt(caseThen),Block(List()))
          For(i,l,u,dir,simplifyStmt(ifStmt)) }) 
      case For(v,lb,ub,dir,Block(stmts :+ MemWrite(an,indices,Guarded(cond,e)))) =>
        For(v,lb,ub,dir,If(cond,Block((stmts map simplifyStmt) :+ MemWrite(an,indices,e)),Block(List())))
      case For(v,lb,ub,dir,stmts)  => For(v,lb,ub,dir,simplifyStmt(stmts))
      case If(cond,caseThen,caseElse) => If(cond, simplifyStmt(caseThen), simplifyStmt(caseElse))
      //TODO: reduce min(min to two mins using temp
      case  MemWrite(arrayName,indices,FunApp(f1,List(FunApp(f2,args :+ Var(t,tt))))) if ((reduceFnsStr contains f1)  && (f2 == "[]") && args.length >= 2 && t.startsWith("tmp")) =>
        val assignments = args.reverse map (a => Assign(t,FunApp(f1,List(a,Var(t,tt)))))
        Block(assignments :+ MemWrite(arrayName,indices,Var(t,tt)))
      case Assign(v1,FunApp(f,List(Var(v2,ii),Guarded(cond,e)))) if ((v1 == v2) &&  (reduceFnsStr contains f))=>
        If(cond,Assign(v1,FunApp(f,List(Var(v2,ii),e))),Block(List()))
      case Assign(v1,FunApp(f,List(Guarded(cond,e),Var(v2,ii)))) if ((v1 == v2) &&  (reduceFnsStr contains f))=>
        If(cond,Assign(v1,FunApp(f,List(e,Var(v2,ii)))),Block(List()))
      case MemWrite(arrayName,indices,Guarded(cond,e)) =>
        If(cond,MemWrite(arrayName,indices,e),Block(List()))
      case MemWrite(arrayName1,indices1,FunApp(f1,List(MemRead(arrayName2,indices2),Guarded(cond,e)))) if ((reduceFnsStr contains f1) && (arrayName1 == arrayName2) && (indices1 == indices2)) => 
        If(cond,MemWrite(arrayName1,indices1,FunApp(f1,List(MemRead(arrayName2,indices2),e))),Block(List()))
      case MemWrite(arrayName1,indices1,FunApp(f1,List(FunApp("[]",List(MemRead(arrayName2,indices2),Guarded(cond,e)))) )) if ((reduceFnsStr contains f1) && (arrayName1 == arrayName2) && (indices1 == indices2)) => 
        If(cond,MemWrite(arrayName1,indices1,FunApp(f1,List(FunApp("[]",List(MemRead(arrayName2,indices2),e))))),Block(List()))
      case MemWrite(arrayName1,indices1,FunApp(f1,List(FunApp("[]",(init@MemRead(arrayName2,indices2)):: rest)))) if (reduceFnsStr contains f1) && (arrayName1 == arrayName2) && (indices1 == indices2) => 
        val tmpName = createTempName()
        val tmpVar = Var(tmpName,Interval("R"))
        def assignStmt(e: Expr): Stmt = Assign(tmpName,FunApp(f1,List(FunApp("[]",List(tmpVar,e)))))
        Block((List(DefVar(tmpName, "TYPE"), Assign(tmpName, init)) ++ (rest map (x => 
          x match {
            case Guarded(g,e) => If(g,assignStmt(e),Block(List()))
            case _ => assignStmt(x)
          }))) :+ MemWrite(arrayName1,indices1,tmpVar))
        //If(g,MemWrite(arrayName1,indices1,FunApp(f1,List(FunApp("[]",List(z,y))))),MemWrite(arrayName,indices,z))
        /* If last stmt of a for loop is array write then lift the guard*/
      /*case MemWrite(arrayName,indices,rhs) =>
        rhs match {
          case FuncPre(f) =>
            if (f==arrayName) Block(List())
            else stmt
          case _ => stmt
        }*/
      case FunctionCallWithBody(name,params,Block(l)) =>
         FunctionCallWithBody(name,params,Block(l map simplifyStmt))
      case DefIntervalSplit(ii, superset, whichPart)  => DefIntervalSplit(ii, superset, whichPart) 
      case DefIntervalUnion(ii, subparts)  => DefIntervalUnion(ii, subparts)
      case DefVar(v, typ)  => DefVar(v, typ) 
      case Assign(v, e)  =>  Assign(v, e) 
      case MemWrite(arrayName,indices,rhs)  => MemWrite(arrayName,indices,rhs)
      case FunctionCall(name, params)  => FunctionCall(name, params)  
      case Verbatim(code) => Verbatim(code)
    }
  }
  
  def getMetaData(json: DBObject) {
    loopDirections = json.toMap map { case (k,v) => k.toString -> v.toString } collect {
      case (i, "FWD") => i -> FWD
      case (j, "BWD") => j -> BWD
    } toMap
  }
  
  def main(args: Array[String]) {
    
    //val e = E(MemRead("dist"),List(E(Var("i")),E(Var("j"))))
    //println(e)
    //implicit val scope = examples.Paren.scope
    //println(scope)
    val cliOpts = new CommandLineConfig(args toList)
    val outf = new BufferedWriter(new FileWriter (cliOpts.outputfile()))
    CppOutput.writePrefaceTo(outf)

    import syntax.Nullable._
    
    for (filename <- cliOpts.filenames()){
      val f = new BufferedReader( new FileReader(filename))
      val blocks = CLI.getBlocks(f)
      for (block <- blocks){
        val json = JSON.parse(block).asInstanceOf[BasicDBObject]
        scope = json.get("scope") andThen_ (Scope.fromJson, examples.Paren.scope)
            //  { throw new SerializationError("scope not found", json) })  // TODO change to "throw" when all JSONs contain proper scope
        val prg = json.get("term") andThen_ (Formula.fromJson, { throw new SerializationError("program term is missing", json); })
        val style = json.getString("style") 
        val title = json.getString("program")
        json.get("tag") andThen_ (getMetaData, {})
        val r = """(.*)\[(.*)\]$""".r
        val x = r.findFirstMatchIn(title)
        val name = x.get.group(1) 
        
        val arg_intervals = x.get.group(2).split(",").toList map (a => Interval(a))
        println(name)
        println(arg_intervals)

        println(s"The program is: ${prg.toPretty}")
        val ffwnocolons = stripColons(prg)
        println(ffwnocolons.toPretty)
        val fundef = FormulaToFunction(name,style,arg_intervals,ffwnocolons)
        println(s"The program AST is: ")
        println(fundef)
        val nl = new NestedListTextFormat[String]("  ","  ")()
        nl.layOut(fundef.body.toPrettyTree)
        println("\nThe code is:")
        val cppGen = new codegen.CppOutput()(scope)
        val code = cppGen(fundef,0)
        println(code)
        
        outf.write(code + "\n")
      }
    }
    outf.close()
  }
}