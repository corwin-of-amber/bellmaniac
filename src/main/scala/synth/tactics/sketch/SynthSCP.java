package synth.tactics.sketch;

import java.io.OutputStreamWriter;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.Map.Entry;
import java.io.PrintWriter;

import sketch.compiler.ast.corea.FEReplacer;
import sketch.compiler.ast.core.Annotation;
import sketch.compiler.ast.core.FieldDecl;
import sketch.compiler.ast.core.Function;
import sketch.compiler.ast.core.Function.LibraryFcnType;
import sketch.compiler.ast.core.Package;
import sketch.compiler.ast.core.exprs.ExprArrayInit;
import sketch.compiler.ast.core.exprs.ExprFunCall;
import sketch.compiler.ast.core.exprs.ExprLocalVariables;
import sketch.compiler.ast.core.exprs.ExprVar;
import sketch.compiler.ast.core.stmts.*;
import sketch.compiler.ast.core.typs.StructDef;
import sketch.compiler.ast.core.typs.StructDef.StructFieldEnt;
import sketch.compiler.ast.spmd.stmts.SpmdBarrier;
import sketch.compiler.ast.spmd.stmts.StmtSpmdfork;
import sketch.util.annot.CodeGenerator;

import static synth.tactics.sketch.NanoJson.toJson;



@CodeGenerator
public class SynthSCP extends FEReplacer
{
	boolean outtags = false;
	private static final int	tabWidth	= 2;
	protected final PrintWriter	out;
	protected int	indent	= 0;
	protected String	pad	= "";

    protected final boolean printLibraryFunctions;
	public SynthSCP outputTags(){

		outtags = true;
		return this;
	}

	public SynthSCP() {
		out = new PrintWriter(new OutputStreamWriter(System.out, StandardCharsets.UTF_8), true);
		printLibraryFunctions = false;
	}

	protected void printTab () {
		if(indent*tabWidth!=pad.length()) {
			StringBuffer b=new StringBuffer();
			for(int i=0;i<indent*tabWidth;i++)
				b.append(' ');
			pad=b.toString();
		}
		out.print(pad);
	}

	protected void print (String s) {
		out.print (s);
	}

	protected void printLine (String s) {
		printTab();
		out.println(s);
		out.flush();
	}

	protected void printIndentedStatement (Statement s) {
		if(s==null) return;
		if(s instanceof StmtBlock)
			s.accept(this);
		else {
			indent++;
			s.accept(this);
			indent--;
		}
	}

    private Map<String,String> sorts = new HashMap<>();
	private Map<Integer,String> leafSorts = new TreeMap<>();
    private List<String> calls = new LinkedList<>();
    private List<Object> areas = new LinkedList<>();
    private List<Integer> offsets = null;

    private Map<String, List<String>> paramSorts = new TreeMap<>();
    private Map<String, List<Integer>> paramOffsets = new TreeMap<>();
    
    private String encode(String s) { return encode(s, StandardCharsets.UTF_8); }
    private String encode(String s, Charset encoding) {
        /* String in Sketch is a bit messed up, it's actually bytes */
        byte[] arr = new byte[s.length()];
        for (int i = 0; i < s.length(); i++)
            arr[i] = (byte)s.charAt(i);
        return new String(arr, encoding);
    }
    
    private <A> List<A> singletonList(A a) { 
    	List<A> l = new ArrayList<>();
    	l.add(a);
    	return l;
    }
    
    /**
     * Writes parameters (stored in paramSorts and paramOffsets) to standard output.
     */
    private void produceParameters() {
        for (Entry<String,List<String>> kv : paramSorts.entrySet()) {
        	List<String> value = kv.getValue();
        	List<Integer> offsets = paramOffsets.get(kv.getKey());
        	if (offsets != null) {
        		for (int d : offsets) value.add(offset(value.get(0), d));  // TODO all members of value
        	}
        	out.println("/* {" + kv.getKey() + ": " + toJson(singletonList(value)) + "} */");
        }
    }

	public Object visitFunction(Function func)
	{
		for (Annotation ann : func.getAnnotation("Param")) {
            out.println("/*" + func.getName() + "*/");
            String value = encode(ann.contents());
            if (value.contains(":"))
                out.println("/* {" + value + "} */");
            else {
            	calls = new LinkedList<>();
	            super.visitFunction(func);
	            paramSorts.put(value, calls);
            }
        }

		for (Annotation ann : func.getAnnotation("OffsetsForParam")) {
            out.println("/*" + func.getName() + "*/");
            String value = encode(ann.contents());
            offsets = null;
            super.visitFunction(func);
            if (offsets != null) paramOffsets.put(value, offsets);
		}
		
        for (Annotation ann : func.getAnnotation("Inv")) {
            out.println("/*" + func.getName() + "*/");
            areas = new LinkedList<>();
            super.visitFunction(func);
            if (areas.isEmpty())
            	out.println("/* WARN: Invariant '" + encode(ann.contents()) + "' is empty */");
            out.println("/* {" + encode(ann.contents()) + ": " + toJson(areas) + "} */");
        }

        for (Annotation sortAnn : func.getAnnotation("Sort")) {
            sorts.put(func.getName(), encode(sortAnn.contents()));
            out.println(sortAnn.tag + " " + func.getName() + " = " + encode(sortAnn.contents()));
            for (Annotation leafAnn : func.getAnnotation("Leaf"))
                leafSorts.put(Integer.parseInt(leafAnn.contents()), encode(sortAnn.contents()));
        }

		/*
		if(outtags && func.getTag() != null){ out.println("T="+func.getTag()); }
		printTab();
		out.println("/*" + func.getCx() + "* /");
		printTab();
		//From the custom code generator you have access to any annotations attached to the function.
		//You can use these annotations to pass information to your code generator.
        for (Entry<String, Vector<Annotation>> anitv : func.annotationSet()) {
            for (Annotation anit : anitv.getValue()) {
                out.print(anit.toString() + " ");
            }
        }
        out.print("\n");
		out.println((func.getInfo().printType == PrintFcnType.Printfcn ? "printfcn " : "") + func.toString());
		super.visitFunction(func);
		out.flush();*/
		return func;
	}
	
    @Override
    public Object visitExprFunCall(ExprFunCall funCall)
    {
        String sort = sorts.get(funCall.getName());
        if (sort != null) {
        	if (!calls.contains(sort))
        		calls.add(sort);
        	/*
        	switch (funCall.getParams().get(0).toString()) {
        	case "i + 1": calls.add(offset(sort, -1));  break; // the offset is negated. this is not a typo 
        	case "i - 1": calls.add(offset(sort, +1));  break;
        	default:      calls.add(sort);
        	}*/
        }
        if (funCall.getName().equals("offsets")) {
        	boolean[] bits = parseArray(funCall.getParams().get(0).toString());
        	offsets = new ArrayList<>();
        	assert(bits.length == 2);  // @@@
        	if (bits[0]) offsets.add(-1);
        	if (bits[1]) offsets.add(+1);
        }
        if (funCall.getName().equals("Scope_2d")) {
        	int n = leafSorts.size();
            boolean[][] mat = twoDim(parseArray(funCall.getParams().get(0).toString()), 3*n);
            boolean lt = funCall.getParams().get(1).toString() .equals( "1" );
            areas.add(area(mat));
            if (lt) areas.add("<");
        }
        else if (funCall.getName().equals("Scope_2d_easier")) {
            boolean[][] mat = twoDim(parseArray(funCall.getParams().get(0).toString()), 3);  /* should be number of parameters in sketch */
            boolean lt = funCall.getParams().get(1).toString() .equals( "1" );
            areas.add(areap(mat));
            if (lt) areas.add("<");
        }
        return super.visitExprFunCall(funCall);
    }

    private boolean[] parseArray(String s) {
        if (s.startsWith("{") && s.endsWith("}")) {
            String[] elems = s.substring(1, s.length() - 1).split(",");
            boolean[] arr = new boolean[elems.length];
            for (int i = 0; i < elems.length; i++)
                arr[i] = Integer.parseInt(elems[i]) != 0;
            return arr;
        }
        throw new RuntimeException("expected a bit array, got '" + s + "'");
    }

    private boolean[][] twoDim(boolean[] arr, int n)
    {
        boolean[][] mat = new boolean[n][];
        for (int i = 0; i < n; i++) {
            mat[i] = new boolean[n];
            System.arraycopy(arr, i*n, mat[i], 0, n);
        }
        return mat;
    }

    private final int OFFSET_RANGE = 3;
    private final int OFFSET_START = -1;
    
    private String offset(String sort, int offset) {
    	if (offset == 0) return sort;
    	else if (offset < 0) return sort + "~" + sort + "-" + (-offset);
    	else return sort + "~" + sort + "+" + offset;
    }
    
    private String leaf(int idx)
    {
    	String sort = leafSorts.get(idx / OFFSET_RANGE);
    	int offset = -(idx % OFFSET_RANGE + OFFSET_START);
    	return offset(sort, offset);
    }
    
    private String param(int idx)
    {
    	return "P" + "₁₂₃".charAt(idx);
    }
    
    private List<List<String>> area(boolean[][] mat)
    {
        List<List<String>> area = new ArrayList<>();
        for (int i = 0; i < mat.length; i++) {
            for (int j = 0; j < mat[i].length; j++) {
            	System.out.print((mat[i][j] ? 1 : 0) + " ");
                if (mat[i][j]) {
                    area.add(Arrays.asList(leaf(i), leaf(j)));

                }
            }
            System.out.println();
        }
        return area;
    }


    private List<List<String>> areap(boolean[][] mat)
    {
        List<List<String>> area = new ArrayList<>();
        for (int i = 0; i < mat.length; i++) {
            for (int j = 0; j < mat[i].length; j++) {
            	System.out.print((mat[i][j] ? 1 : 0) + " ");
                if (mat[i][j]) {
                    area.add(Arrays.asList(param(i), param(j)));

                }
            }
            System.out.println();
        }
        return area;
    }

    @Override
    public Object visitPackage(Package spec)
    {

        //The name resolver is used to find functions and structs matching a particular name.
        nres.setPackage(spec);
        printLine("/* BEGIN PACKAGE " + spec.getName() + " */");

        for (StructDef tsOrig : spec.getStructs()) {
            tsOrig.accept(this);
        }

        for (FieldDecl field : spec.getVars())
        {
        	System.out.println("Field --- " + field.getNames());
            field.accept(this);
        }

        TreeSet<Function> orderedFuncs = new TreeSet<Function>(new Comparator<Function>()
        {
            public int compare(Function o1, Function o2) {
                final int det_order =
                        o1.getInfo().determinsitic.compareTo(o2.getInfo().determinsitic);
                return det_order + (det_order == 0 ? 1 : 0) *
                        o1.getName().compareTo(o2.getName());
            }
        });
        orderedFuncs.addAll(spec.getFuncs());

        for (Function oldFunc : orderedFuncs) {
            if (oldFunc.getInfo().libraryType != LibraryFcnType.Library || printLibraryFunctions) {
                oldFunc.accept(this);
            }
        }
        
        produceParameters();
        
        printLine("/* END PACKAGE " + spec.getName() + "*/");
        return spec;
    }



	public Object visitStmtFor(StmtFor stmt)
	{
		if(outtags && stmt.getTag() != null){ out.println("T="+stmt.getTag()); }
        printLine("for(" + stmt.getInit() + "; " + stmt.getCond() + "; " +
                stmt.getIncr() + ")" + (stmt.isCanonical() ? "/*Canonical*/" : ""));
		printIndentedStatement(stmt.getBody());
		return stmt;
	}

	public Object visitStmtSpmdfork(StmtSpmdfork stmt)
	{
		if(outtags && stmt.getTag() != null){ out.println("T="+stmt.getTag()); }
		printLine("spmdfork("+stmt.getNProc() + ")");
		printIndentedStatement(stmt.getBody());
		return stmt;
	}

        public Object visitSpmdBarrier(SpmdBarrier stmt)
        {
                printLine("spmdbarrier();");
                return stmt;
        }

	@Override
	public Object visitStmtIfThen(StmtIfThen stmt)
	{
		if(outtags && stmt.getTag() != null){ out.println("T="+stmt.getTag()); }
    	printLine("if(" + stmt.getCond() + ")/*" + stmt.getCx() + "*/");
    	printIndentedStatement(stmt.getCons());
    	if(stmt.getAlt() != null){
    		printLine("else");
    		printIndentedStatement(stmt.getAlt());
    	}
		return stmt;
	}

	@Override
	public Object visitStmtWhile(StmtWhile stmt)
	{
		if(outtags && stmt.getTag() != null){ out.println("T="+stmt.getTag()); }
    	printLine("while(" + stmt.getCond() + ")");
    	printIndentedStatement(stmt.getBody());
		return stmt;
	}

	@Override
	public Object visitStmtDoWhile(StmtDoWhile stmt)
	{
		if(outtags && stmt.getTag() != null){ out.println("T="+stmt.getTag()); }
		printLine("do");
		printIndentedStatement(stmt.getBody());
    	printLine("while(" + stmt.getCond() + ")");
		return stmt;
	}

	@Override
	public Object visitStmtLoop(StmtLoop stmt)
	{
		if(outtags && stmt.getTag() != null){ out.println("T="+stmt.getTag()); }
    	printLine("loop(" + stmt.getIter() + ")");
    	printIndentedStatement(stmt.getBody());
		return stmt;
	}

	@Override
	public Object visitStmtBlock(StmtBlock stmt)
	{
		if(outtags && stmt.getTag() != null){ out.println("T="+stmt.getTag()); }
		printLine("{");
		indent++;
		super.visitStmtBlock(stmt);
		indent--;
		printLine("}");
		out.flush();
		return stmt;
	}


	@Override
	public Object visitStmtAssert(StmtAssert stmt)
	{
		if(outtags && stmt.getTag() != null){ out.println("T="+stmt.getTag()); }
		printLine(stmt.toString() + ";" + " //" + stmt.getMsg());
		return super.visitStmtAssert(stmt);
	}

    @Override
    public Object visitStmtAssume(StmtAssume stmt) {
        if (outtags && stmt.getTag() != null) {
            out.println("T=" + stmt.getTag());
        }
        printLine(stmt.toString() + ";" + " //" + stmt.getMsg());
        return super.visitStmtAssume(stmt);
    }

	@Override
	public Object visitStmtAssign(StmtAssign stmt)
	{
		if(outtags && stmt.getTag() != null){ out.println("T="+stmt.getTag()); }
		printLine(stmt.toString()  + ';');
		return super.visitStmtAssign(stmt);
	}


	@Override
	public Object visitStmtEmpty(StmtEmpty stmt)
	{
		printLine(stmt.toString());
		return super.visitStmtEmpty(stmt);
	}

	@Override
	public Object visitStmtExpr(StmtExpr stmt)
	{
		if(outtags && stmt.getTag() != null){ out.println("T="+stmt.getTag()); }
        {
            printLine(stmt.toString() + ";");
            stmt.getExpression().accept(this);
        }
        return stmt;
	}

    public Object visitStmtFunDef(StmtFunDecl stmt) {
        printLine(stmt.toString());
        return stmt;
    }

	@Override
	public Object visitStmtReturn(StmtReturn stmt)
	{
		printLine(stmt.toString());
		return super.visitStmtReturn(stmt);
	}

    // @Override
    // public Object visitStmtAngelicSolve(StmtAngelicSolve stmt) {
    // printLine("angelic_solve");
    // return super.visitStmtAngelicSolve(stmt);
    // }

	@Override
	public Object visitStmtVarDecl(StmtVarDecl stmt)
	{
		if(outtags && stmt.getTag() != null){ out.println("T="+stmt.getTag()); }

        for (int i = 0; i < stmt.getNumVars(); i++) {
            String str = stmt.getType(i) + " " + stmt.getName(i);
            if (stmt.getInit(i) != null) {
                str += " = " + stmt.getInit(i);
            }
            printLine(str + ";");
        }

        return stmt;
	}

	@Override
	public Object visitFieldDecl(FieldDecl field)
	{
		printLine(field.toString());
		return super.visitFieldDecl(field);
	}

	public Object visitStmtReorderBlock(StmtReorderBlock block){
		printLine("reorder");
		block.getBlock().accept(this);
		return block;
	}

	public Object visitStmtInsertBlock (StmtInsertBlock sib) {
		printLine ("insert");
		sib.getInsertStmt ().accept (this);
		printLine ("into");
		sib.getIntoBlock ().accept (this);
		return sib;
	}


	@Override
	public Object visitStructDef(StructDef ts) {
	    printLine("struct " + ts.getName() + " {");
        for (StructFieldEnt ent : ts.getFieldEntriesInOrder()) {
	        printLine("    " + ent.getType().toString() + " " + ent.getName() + ";");
	    }
        for (Entry<String, Vector<Annotation>> at : ts.annotationSet()) {
            for (Annotation ann : at.getValue()) {
                printLine("    " + ann);
            }
        }
	    printLine("}");
	    return ts;
	}

    @Override
    public Object visitStmtMinLoop(StmtMinLoop stmtMinLoop) {
        printTab();
        print("minloop");
        printIndentedStatement(stmtMinLoop.getBody());
        return stmtMinLoop;
    }

    @Override
    public Object visitStmtMinimize(StmtMinimize stmtMinimize) {
        printLine("minimize(" + stmtMinimize.getMinimizeExpr().accept(this) + ")");
        return stmtMinimize;
    }

}
