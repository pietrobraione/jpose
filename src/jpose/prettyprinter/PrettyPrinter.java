package jpose.prettyprinter;

import java.util.List;
import java.util.Objects;
import java.util.Map.Entry;
import java.util.SequencedMap;
import java.util.stream.Collectors;

import jpose.semantics.types.SemConfiguration;
import jpose.semantics.types.SemObject;
import jpose.syntax.SyBool;
import jpose.syntax.SyBoolFalse;
import jpose.syntax.SyBoolTrue;
import jpose.syntax.SyDeclClass;
import jpose.syntax.SyDeclClassLit;
import jpose.syntax.SyDeclMethod;
import jpose.syntax.SyDeclMethodLit;
import jpose.syntax.SyDeclVariable;
import jpose.syntax.SyDeclVariableLit;
import jpose.syntax.SyExpression;
import jpose.syntax.SyExpressionAdd;
import jpose.syntax.SyExpressionAnd;
import jpose.syntax.SyExpressionEq;
import jpose.syntax.SyExpressionGetfield;
import jpose.syntax.SyExpressionId;
import jpose.syntax.SyExpressionIf;
import jpose.syntax.SyExpressionInstanceof;
import jpose.syntax.SyExpressionInvoke;
import jpose.syntax.SyExpressionLet;
import jpose.syntax.SyExpressionLt;
import jpose.syntax.SyExpressionNew;
import jpose.syntax.SyExpressionNot;
import jpose.syntax.SyExpressionOr;
import jpose.syntax.SyExpressionPutfield;
import jpose.syntax.SyExpressionSub;
import jpose.syntax.SyExpressionValue;
import jpose.syntax.SyExpressionVariable;
import jpose.syntax.SyInt;
import jpose.syntax.SyIntLit;
import jpose.syntax.SyLoc;
import jpose.syntax.SyLocLit;
import jpose.syntax.SyPrimitiveConstant;
import jpose.syntax.SyPrimitiveConstantBool;
import jpose.syntax.SyPrimitiveConstantInt;
import jpose.syntax.SyPrimitiveConstantSymbol;
import jpose.syntax.SyProgram;
import jpose.syntax.SyProgramLit;
import jpose.syntax.SyReferenceConstant;
import jpose.syntax.SyReferenceConstantLoc;
import jpose.syntax.SyReferenceConstantNull;
import jpose.syntax.SyReferenceConstantSymbol;
import jpose.syntax.SySymbol;
import jpose.syntax.SySymbolExpression;
import jpose.syntax.SySymbolField;
import jpose.syntax.SyType;
import jpose.syntax.SyTypeBool;
import jpose.syntax.SyTypeClass;
import jpose.syntax.SyTypeInt;
import jpose.syntax.SyValue;
import jpose.syntax.SyValueAdd;
import jpose.syntax.SyValueAnd;
import jpose.syntax.SyValueEq;
import jpose.syntax.SyValueFieldRel;
import jpose.syntax.SyValueIte;
import jpose.syntax.SyValueLt;
import jpose.syntax.SyValueNot;
import jpose.syntax.SyValueOr;
import jpose.syntax.SyValuePrimitiveConstant;
import jpose.syntax.SyValueReferenceConstant;
import jpose.syntax.SyValueSub;
import jpose.syntax.SyValueSubtypeRel;
import jpose.syntax.SyValueUnassumed;

public final class PrettyPrinter {
	public String typeToString(SyType type) {
		Objects.requireNonNull(type);
		
		if (type instanceof SyTypeBool) {
			return "bool";
		} else if (type instanceof SyTypeInt) {
			return "int";
		} else if (type instanceof SyTypeClass(String className)) {
			return className;
		} else {
			throw new AssertionError("Unexpected type");
		}
	}
	
	public String boolToString(SyBool bool) {
		Objects.requireNonNull(bool);

		if (bool instanceof SyBoolTrue) {
			return "true";
		} else if (bool instanceof SyBoolFalse) {
			return "false";
		} else {
			throw new AssertionError("Unexpected bool");
		}
	}
	
	public String intToString(SyInt i) {
		Objects.requireNonNull(i);

		if (i instanceof SyIntLit(int n)) {
			return Integer.toString(n);
		} else {
			throw new AssertionError("Unexpected int");
		}
	}
	
	public String locToString(SyLoc l) {
		Objects.requireNonNull(l);

		if (l instanceof SyLocLit(int p)) {
			return "L" + Integer.toString(p);
		} else {
			throw new AssertionError("Unexpected location");
		}
	}
	
	public String symbolToString(SySymbol s) {
		Objects.requireNonNull(s);

		if (s instanceof SySymbolExpression(int n)) {
			return Integer.toString(n);
		} else if (s instanceof SySymbolField(int n, List<String> l)) { 
			return Integer.toString(n) + "_" + l.stream().collect(Collectors.joining("_"));
		} else {
			throw new AssertionError("Unexpected symbol");
		}
	}

	public String primitiveConstantToString(SyPrimitiveConstant p) {
		Objects.requireNonNull(p);

		if (p instanceof SyPrimitiveConstantBool(SyBool b)) {
			return boolToString(b);
		} else if (p instanceof SyPrimitiveConstantInt(SyInt i)) {
			return intToString(i);
		} else if (p instanceof SyPrimitiveConstantSymbol(SySymbol s)) {
			return "X" + symbolToString(s);
		} else {
			throw new AssertionError("Unexpected primitive constant");
		}
	}
	
	public String referenceConstantToString(SyReferenceConstant u) {
		Objects.requireNonNull(u);
		
		if (u instanceof SyReferenceConstantNull) {
			return "null";
		} else if (u instanceof SyReferenceConstantLoc(SyLoc l)) {
			return locToString(l);
		} else if (u instanceof SyReferenceConstantSymbol(SySymbol s)) {
			return "Y" + symbolToString(s);
		} else {
			throw new AssertionError("Unexpected reference constant");
		}
	}
	
	public String valueToString(SyValue sigma) {
		Objects.requireNonNull(sigma);
		
		if (sigma instanceof SyValueUnassumed) {
			return "BOT";
		} else if (sigma instanceof SyValuePrimitiveConstant(SyPrimitiveConstant p)) {
			return primitiveConstantToString(p);
		} else if (sigma instanceof SyValueReferenceConstant(SyReferenceConstant u)) {
			return referenceConstantToString(u);
		} else if (sigma instanceof SyValueAdd(SyValue sigma1, SyValue sigma2)) {
			return "(" + valueToString(sigma1) + " + " + valueToString(sigma2) + ")";
		} else if (sigma instanceof SyValueSub(SyValue sigma1, SyValue sigma2)) {
			return "(" + valueToString(sigma1) + " - " + valueToString(sigma2) + ")";
		} else if (sigma instanceof SyValueLt(SyValue sigma1, SyValue sigma2)) {
			return "(" + valueToString(sigma1) + " < " + valueToString(sigma2) + ")";
		} else if (sigma instanceof SyValueAnd(SyValue sigma1, SyValue sigma2)) {
			return "(" + valueToString(sigma1) + " && " + valueToString(sigma2) + ")";
		} else if (sigma instanceof SyValueOr(SyValue sigma1, SyValue sigma2)) {
			return "(" + valueToString(sigma1) + " || " + valueToString(sigma2) + ")";
		} else if (sigma instanceof SyValueNot(SyValue sigma1)) {
			return "(~" + valueToString(sigma1) + ")";
		} else if (sigma instanceof SyValueEq(SyValue sigma1, SyValue sigma2)) {
			return "(" + valueToString(sigma1) + " = " + valueToString(sigma2) + ")";
		} else if (sigma instanceof SyValueSubtypeRel(SyValue sigma1, SyType t)) {
			return "(" + valueToString(sigma1) + " <: " + typeToString(t) + ")";
		} else if (sigma instanceof SyValueFieldRel(SySymbol s1, String fname, SySymbol s2)) {
			return "(Y" + symbolToString(s1) + "." + fname + " = Z" + symbolToString(s2) + ")";
		} else if (sigma instanceof SyValueIte(SyValue sigma1, SyValue sigma2, SyValue sigma3)) {
			return "ite(" + valueToString(sigma1) + ", " + valueToString(sigma2) + ", " + valueToString(sigma3) + ")";
		} else {
			throw new AssertionError("Unexpected value");
		}
	}
	
	public String expressionToString(SyExpression e) {
		Objects.requireNonNull(e);
		
		if (e instanceof SyExpressionVariable(String x)) {
			return x;
		} else if (e instanceof SyExpressionValue(SyValue sigma)) {
			return valueToString(sigma);
		} else if (e instanceof SyExpressionNew(String c)) {
			return "new " + c;
		} else if (e instanceof SyExpressionGetfield(SyExpression e1, String fname)) {
			return "(" + expressionToString(e1) + "." + fname + ")";
		} else if (e instanceof SyExpressionPutfield(SyExpression e1, String fname, SyExpression e2)) {
			return "(" + expressionToString(e1) + "." + fname + " := " + expressionToString(e2) + ")";
		} else if (e instanceof SyExpressionLet(String x, SyExpression e1, SyExpression e2)) {
			return "let " + x + " := " + expressionToString(e1) + " in " + expressionToString(e2);
		} else if (e instanceof SyExpressionAdd(SyExpression e1, SyExpression e2)) {
			return "(" + expressionToString(e1) + " + " + expressionToString(e2) + ")";
		} else if (e instanceof SyExpressionSub(SyExpression e1, SyExpression e2)) {
			return "(" + expressionToString(e1) + " - " + expressionToString(e2) + ")";
		} else if (e instanceof SyExpressionLt(SyExpression e1, SyExpression e2)) {
			return "(" + expressionToString(e1) + " < " + expressionToString(e2) + ")";
		} else if (e instanceof SyExpressionAnd(SyExpression e1, SyExpression e2)) {
			return "(" + expressionToString(e1) + " && " + expressionToString(e2) + ")";
		} else if (e instanceof SyExpressionOr(SyExpression e1, SyExpression e2)) {
			return "(" + expressionToString(e1) + " || " + expressionToString(e2) + ")";
		} else if (e instanceof SyExpressionNot(SyExpression e1)) {
			return "(~" + expressionToString(e1) + ")";
		} else if (e instanceof SyExpressionEq(SyExpression e1, SyExpression e2)) {
			return "(" + expressionToString(e1) + " = " + expressionToString(e2) + ")";
		} else if (e instanceof SyExpressionInstanceof(SyExpression e1, String c)) {
			return "(" + expressionToString(e1) + " instanceof " + c + ")";
		} else if (e instanceof SyExpressionIf(SyExpression e1, SyExpression e2, SyExpression e3)) {
			return "if " + expressionToString(e1) + " then " + expressionToString(e2) + " else " + expressionToString(e3);
		} else if (e instanceof SyExpressionInvoke(SyExpression e1, String m, SyExpression e2)) {
			return "(" + expressionToString(e1) + "." + m + "[" + expressionToString(e2) + "])";
		} else if (e instanceof SyExpressionId(String idName)) {
			return "(@ " + idName + ")";
		} else {
			throw new AssertionError("Unexpected expression");
		}
	}
	
	public String declVariableToString(boolean semicolon, SyDeclVariable F) {
		Objects.requireNonNull(F);
		
		if (F instanceof SyDeclVariableLit(SyType t, String x)) {
			return typeToString(t) + " " + x + (semicolon ? ";" : "");
		} else {
			throw new AssertionError("Unexpected variable declaration");
		}
	}
	
	public String declMethodToString(SyDeclMethod D) {
		Objects.requireNonNull(D);
		
		if (D instanceof SyDeclMethodLit(SyType t, String m, SyDeclVariable v, SyExpression e)) {
			return typeToString(t) + " " + m + "(" + declVariableToString(false, v) + ") := " + expressionToString(e) + ";";
		} else {
			throw new AssertionError("Unexpected method declaration");
		}
	}
	
	public String declClassToString(SyDeclClass C) {
		Objects.requireNonNull(C);
		
		if (C instanceof SyDeclClassLit(String c, String cSup, List<SyDeclVariable> Fs, List<SyDeclMethod> Ds)) {
			return "class " + c + ("".equals(cSup) ? "" : (" extends " + cSup)) + " { " + Fs.stream().map(F -> { return declVariableToString(true, F); }).collect(Collectors.joining(" ")) + " " +
			       Ds.stream().map(D -> { return declMethodToString(D); }).collect(Collectors.joining(" ")) + "}";
		} else {
			throw new AssertionError("Unexpected class declaration");
		}
	}

	public String programToString(SyProgram P) {
		Objects.requireNonNull(P);
		
		if (P instanceof SyProgramLit(List<SyDeclClass> Cs, SyExpression e)) {
			return Cs.stream().map(C -> { return declClassToString(C); }).collect(Collectors.joining(" ")) + " " + expressionToString(e);
		} else {
			throw new AssertionError("Unexpected program");
		}
	}
	
	private String objectToStringAux(SequencedMap<String, SyValue> memory) {
		final StringBuilder b = new StringBuilder();
		for (Entry<String, SyValue> elt : memory.entrySet()) {
			var f = elt.getKey();
			var sigma = elt.getValue();
			b.append(f);
			b.append(':');
			b.append(valueToString(sigma));
			b.append(", ");
		}
		return b.toString();
	}
	
	public String objectToString(SemObject o) {
		Objects.requireNonNull(o);
		
		return "{class " + o.className() + ", " + objectToStringAux(o.memory()) + "}";
	}
	
	private String heapToString(SequencedMap<SyReferenceConstant, SemObject> heap) {
		Objects.requireNonNull(heap);
		
		return "<" + heap.entrySet().stream().map(elt -> {
			var u = elt.getKey();
			var o = elt.getValue();
			return referenceConstantToString(u) + " -> " + objectToString(o);
		}).collect(Collectors.joining(", ")) + ">";
	}
	
	private String pathConditionToString(List<SyValue> pathCondition) {
		Objects.requireNonNull(pathCondition);
		
		if (pathCondition.isEmpty()) {
			return "true";
		} else {
			return valueToString(pathCondition.getFirst()) + " && " + pathConditionToString(pathCondition.subList(1, pathCondition.size()));
		}
	}
	
	public String configToString(SemConfiguration J) {
		Objects.requireNonNull(J);
		
		var P = J.syProgramLit();
		var H = J.heap();
		var sSigma = J.pathCondition();
		var e = J.syExpression();
		
		return "[@" + J.configurationId() + ": " + programToString(P) + ", " + heapToString(H) + ", " + pathConditionToString(sSigma) + ", " + expressionToString(e) + "]";
	}
}
