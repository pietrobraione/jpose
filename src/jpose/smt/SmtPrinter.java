package jpose.smt;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import jpose.prettyprinter.PrettyPrinter;
import jpose.semantics.types.SemConfiguration;
import jpose.syntax.SyDeclClass;
import jpose.syntax.SyDeclClassLit;
import jpose.syntax.SyDeclVariable;
import jpose.syntax.SyDeclVariableLit;
import jpose.syntax.SyLoc;
import jpose.syntax.SyPrimitiveConstant;
import jpose.syntax.SyPrimitiveConstantSymbol;
import jpose.syntax.SyProgram;
import jpose.syntax.SyProgramLit;
import jpose.syntax.SyReferenceConstant;
import jpose.syntax.SyReferenceConstantLoc;
import jpose.syntax.SyReferenceConstantNull;
import jpose.syntax.SyReferenceConstantSymbol;
import jpose.syntax.SySymbol;
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

public final class SmtPrinter {
	private List<Integer> classToList(SyProgram P, SyDeclClass C) {
		if (C instanceof SyDeclClassLit Clit) {
			var cSup = Clit.superclassName();
			if ("".equals(cSup)) {
				//object: it has no siblings
				return List.of(Integer.valueOf(0));
			} else if (P instanceof SyProgramLit Plit) {
				var maybeCsup = Plit.cdecl(cSup);
				ArrayList<Integer> retVal = new ArrayList<>();
				maybeCsup.ifPresentOrElse(Csup -> {
					//looks for the sibling-id
					boolean found = false;
					int id = 0;
					for (SyDeclClass Ccur : Plit.classes()) {
						if (Ccur.equals(C)) {
							found = true;
							break;
						} else if (((SyDeclClassLit) Ccur).superclassName().equals(cSup)) {
							++id;
						}
					}
					
					if (found) {
						retVal.addAll(classToList(P, Csup));
						retVal.add(id);
					} else {
						throw new AssertionError("Unexpected search of undeclared class");
					}
				}, () -> {
					throw new RuntimeException("Class " + cSup + " does not exist in the class hierarchy");
				});
				return retVal;
			} else {
				throw new AssertionError("Unexpected type");
			}
		} else {
			throw new AssertionError("Unexpected type");
		}
	}
	
	private String listIntToSmt(List<Integer> l) {
		if (l.size() == 0) {
			return "nil";
		} else {
			var n = l.getFirst();
			var ns = l.subList(1, l.size());
			return "(insert " + n + " " + listIntToSmt(ns) + ")";
		}
	}
	
	private String referenceConstantToSmt(SyReferenceConstant u) {
		var pp = new PrettyPrinter();
		
		if (u instanceof SyReferenceConstantNull) {
			return "_null";
		} else if (u instanceof SyReferenceConstantLoc(SyLoc l)) {
			return pp.locToString(l);
		} else if (u instanceof SyReferenceConstantSymbol(SySymbol s)) {
			return "Y" + pp.symbolToString(s);
		} else {
			throw new AssertionError("Unexpected type");
		}
	}
	
	private String typeToSmt(SyType t) {
		if (t instanceof SyTypeBool) {
			return "Bool";
		} else if (t instanceof SyTypeInt) {
			return "Int";
		} else if (t instanceof SyTypeClass) {
			return "Ref";
		} else {
			throw new AssertionError("Unexpected type");
		}
	}
	
	private String fieldToSmt(SyDeclVariable F) {
		var Flit = (SyDeclVariableLit) F;
		return "(declare-fun " + Flit.variableName() + " (Ref) " + typeToSmt(Flit.syType()) + ")\n" +
		       "(assert (= " + (Flit.syType().isPrimitive() ? "0" : "_null") + " (" + Flit.variableName() + " _null)))\n";
	}
	
	private String classToSmt(SyProgram P, SyDeclClass C) {
		var Clit = (SyDeclClassLit) C;
		return "(define-fun " + Clit.className() + " () SCl " + listIntToSmt(classToList(P, C)) + ")\n" +
		       Clit.fields().stream().map(this::fieldToSmt).collect(Collectors.joining());
	}
	
	private String smtDecls(SyProgram P) {
		return "(define-sort SCl () (List Int)) ;the sort of classes\n" +
		       "(define-fun-rec subclass ((x SCl) (y SCl)) Bool\n" +
		       "(ite (= y nil) true (ite (= x nil) false (ite (= (head x) (head y)) (subclass (tail x) (tail y)) false))))\n" +
		       "(declare-sort Ref) ;the sort of references\n" +
		       "(declare-fun classOf (Ref) SCl)\n" +
		       "(declare-fun _null () Ref)\n" +
		       ((SyProgramLit) P).classes().stream().map(C -> { return classToSmt(P, C); }).collect(Collectors.joining());
	}
	
	private String valueToSmt(SyProgram P, SyValue sigma) {
		var pp = new PrettyPrinter();
		if (sigma instanceof SyValuePrimitiveConstant(SyPrimitiveConstant p)) {
			return pp.primitiveConstantToString(p);
		} else if (sigma instanceof SyValueReferenceConstant(SyReferenceConstant u)) {
			return referenceConstantToSmt(u);
		} else if (sigma instanceof SyValueAdd(SyValue sigma1, SyValue sigma2)) {
			return "(+ " + valueToSmt(P, sigma1) + " " + valueToSmt(P, sigma2) + ")";
		} else if (sigma instanceof SyValueSub(SyValue sigma1, SyValue sigma2)) {
			return "(- " + valueToSmt(P, sigma1) + " " + valueToSmt(P, sigma2) + ")";
		} else if (sigma instanceof SyValueLt(SyValue sigma1, SyValue sigma2)) {
			return "(< " + valueToSmt(P, sigma1) + " " + valueToSmt(P, sigma2) + ")";
		} else if (sigma instanceof SyValueAnd(SyValue sigma1, SyValue sigma2)) {
			return "(and " + valueToSmt(P, sigma1) + " " + valueToSmt(P, sigma2) + ")";
		} else if (sigma instanceof SyValueOr(SyValue sigma1, SyValue sigma2)) {
			return "(or " + valueToSmt(P, sigma1) + " " + valueToSmt(P, sigma2) + ")";
		} else if (sigma instanceof SyValueNot(SyValue sigma1)) {
			return "(not " + valueToSmt(P, sigma1) + ")";
		} else if (sigma instanceof SyValueEq(SyValue sigma1, SyValue sigma2)) {
			return "(= " + valueToSmt(P, sigma1) + " " + valueToSmt(P, sigma2) + ")";
		} else if (sigma instanceof SyValueSubtypeRel(SyValue sigma1, SyType t)) {
			if (t instanceof SyTypeClass(String c)) {
				return "(subclass (classOf " + valueToSmt(P, sigma1) + ") " + c + ")";
			} else {
				throw new RuntimeException("Ill-formed subtype relation term");
			}
		} else if (sigma instanceof SyValueFieldRel(SySymbol s1, String f, SySymbol s2)) {
			final String[] s2ToString = new String[1];
			((SyProgramLit) P).classWithField(f).ifPresentOrElse(C -> {
				((SyDeclClassLit) C).fdecl(f).ifPresentOrElse(F -> {
					var t = ((SyDeclVariableLit) F).syType();
					if (t.isPrimitive()) {
						s2ToString[0] = pp.primitiveConstantToString(new SyPrimitiveConstantSymbol(s2));
					} else {
						s2ToString[0] = referenceConstantToSmt(new SyReferenceConstantSymbol(s2));
					}
				}, () ->{
					throw new AssertionError("Unexpected missing field " + f); 
				});
			}, () -> {
				throw new RuntimeException("Field " + f + " does not exist in any class");
			});
			return "(= (" + f + " " + referenceConstantToSmt(new SyReferenceConstantSymbol(s1)) + ") " + s2ToString[0] + ")"; 
		} else if (sigma instanceof SyValueIte(SyValue sigma1, SyValue sigma2, SyValue sigma3)) {
			return "(ite " + valueToSmt(P, sigma1) + " " + valueToSmt(P, sigma2) + " " + valueToSmt(P, sigma3) + ")";
		} else {
			throw new AssertionError("Unexpected type");
		}
	}
	
	private String clauseToSmt(SyProgram P, SyValue sigma) {
		return "(assert " + valueToSmt(P, sigma) + ")\n";
	}
	
	private String clausesToSmt(SyProgram P, List<SyValue> pathCondition) {
		final StringBuilder retVal = new StringBuilder();
		for (SyValue sigma : pathCondition) {
			retVal.append(clauseToSmt(P, sigma));
		}
		return retVal.toString();
	}
	
	private String declareVarsClause(SyProgram P, SyValue sigma, Set<SySymbol> symbolsPrimitive, Set<SySymbol> symbolsReference, Set<SyLoc> symbolsLoc) {
		var pp = new PrettyPrinter();
		
		if (sigma instanceof SyValuePrimitiveConstant(SyPrimitiveConstant p)) {
			if (p instanceof SyPrimitiveConstantSymbol(SySymbol s)) {
				if (symbolsPrimitive.contains(s)) {
					return "";
				} else {
					symbolsPrimitive.add(s);
					return "(declare-fun " + pp.primitiveConstantToString(p) + " () Int)\n";
				}
			} else {
				return "";
			}
		} else if (sigma instanceof SyValueReferenceConstant(SyReferenceConstant u)) {
			if (u instanceof SyReferenceConstantSymbol(SySymbol s)) {
				if (symbolsReference.contains(s)) {
					return "";
				} else {
					symbolsReference.add(s);
					return "(declare-fun " + referenceConstantToSmt(u) + " () Ref)\n";
				}
			} else if (u instanceof SyReferenceConstantLoc(SyLoc l)) {
				if (symbolsLoc.contains(l)) {
					return "";
				} else {
					symbolsLoc.add(l);
					return "(declare-fun " + referenceConstantToSmt(u) + " () Ref)\n";
				}
			} else {
				return "";
			}
		} else if (sigma instanceof SyValueAdd(SyValue sigma1, SyValue sigma2)) {
			final StringBuilder retVal = new StringBuilder();
			retVal.append(declareVarsClause(P, sigma1, symbolsPrimitive, symbolsReference, symbolsLoc));
			retVal.append(declareVarsClause(P, sigma2, symbolsPrimitive, symbolsReference, symbolsLoc));
			return retVal.toString();
		} else if (sigma instanceof SyValueSub(SyValue sigma1, SyValue sigma2)) {
			final StringBuilder retVal = new StringBuilder();
			retVal.append(declareVarsClause(P, sigma1, symbolsPrimitive, symbolsReference, symbolsLoc));
			retVal.append(declareVarsClause(P, sigma2, symbolsPrimitive, symbolsReference, symbolsLoc));
			return retVal.toString();
		} else if (sigma instanceof SyValueLt(SyValue sigma1, SyValue sigma2)) {
			final StringBuilder retVal = new StringBuilder();
			retVal.append(declareVarsClause(P, sigma1, symbolsPrimitive, symbolsReference, symbolsLoc));
			retVal.append(declareVarsClause(P, sigma2, symbolsPrimitive, symbolsReference, symbolsLoc));
			return retVal.toString();
		} else if (sigma instanceof SyValueAnd(SyValue sigma1, SyValue sigma2)) {
			final StringBuilder retVal = new StringBuilder();
			retVal.append(declareVarsClause(P, sigma1, symbolsPrimitive, symbolsReference, symbolsLoc));
			retVal.append(declareVarsClause(P, sigma2, symbolsPrimitive, symbolsReference, symbolsLoc));
			return retVal.toString();
		} else if (sigma instanceof SyValueOr(SyValue sigma1, SyValue sigma2)) {
			final StringBuilder retVal = new StringBuilder();
			retVal.append(declareVarsClause(P, sigma1, symbolsPrimitive, symbolsReference, symbolsLoc));
			retVal.append(declareVarsClause(P, sigma2, symbolsPrimitive, symbolsReference, symbolsLoc));
			return retVal.toString();
		} else if (sigma instanceof SyValueNot(SyValue sigma1)) {
			return declareVarsClause(P, sigma1, symbolsPrimitive, symbolsReference, symbolsLoc);
		} else if (sigma instanceof SyValueEq(SyValue sigma1, SyValue sigma2)) {
			final StringBuilder retVal = new StringBuilder();
			retVal.append(declareVarsClause(P, sigma1, symbolsPrimitive, symbolsReference, symbolsLoc));
			retVal.append(declareVarsClause(P, sigma2, symbolsPrimitive, symbolsReference, symbolsLoc));
			return retVal.toString();
		} else if (sigma instanceof SyValueSubtypeRel(SyValue sigma1, SyType t)) {
			return declareVarsClause(P, sigma1, symbolsPrimitive, symbolsReference, symbolsLoc);
		} else if (sigma instanceof SyValueFieldRel(SySymbol s1, String f, SySymbol s2)) {
			final StringBuilder retVal = new StringBuilder();
			if (!symbolsReference.contains(s1)) {
				symbolsReference.add(s1);
				retVal.append("(declare-fun ");
				retVal.append(referenceConstantToSmt(new SyReferenceConstantSymbol(s1)));
				retVal.append(" () Ref)\n");
			}
			((SyProgramLit) P).classWithField(f).ifPresentOrElse(C -> {
				((SyDeclClassLit) C).fdecl(f).ifPresentOrElse(F -> {
					var t = ((SyDeclVariableLit) F).syType();
					if (t.isPrimitive() && !symbolsPrimitive.contains(s2)) {
						symbolsPrimitive.add(s2);
						retVal.append("(declare-fun ");
						retVal.append(pp.primitiveConstantToString(new SyPrimitiveConstantSymbol(s2)));
						retVal.append(" () Int)\n");
					} else if (t.isReference() && !symbolsReference.contains(s2)) {
						symbolsReference.add(s2);
						retVal.append("(declare-fun ");
						retVal.append(referenceConstantToSmt(new SyReferenceConstantSymbol(s2)));
						retVal.append(" () Ref)\n");
					} //else do nothing
				}, () -> {
					throw new AssertionError("Unexpected missing field " + f);
				});
			}, () -> {
				throw new RuntimeException("Field " + f + "does not exist in any class");
			});
			return retVal.toString();
		} else if (sigma instanceof SyValueIte(SyValue sigma1, SyValue sigma2, SyValue sigma3)) {
			final StringBuilder retVal = new StringBuilder();
			retVal.append(declareVarsClause(P, sigma1, symbolsPrimitive, symbolsReference, symbolsLoc));
			retVal.append(declareVarsClause(P, sigma2, symbolsPrimitive, symbolsReference, symbolsLoc));
			retVal.append(declareVarsClause(P, sigma3, symbolsPrimitive, symbolsReference, symbolsLoc));
			return retVal.toString();
		} else {
			return "";
		}
	}
	
	private String declareVarsReferenceConstraints(SyProgram P, Set<SySymbol> symbolsReference) {
		final StringBuilder retVal = new StringBuilder();
		for (SySymbol s : symbolsReference) {
			retVal.append("(assert (or ");
			for (SyDeclClass C : ((SyProgramLit) P).classes()) {
				retVal.append("(= (classOf ");
				retVal.append(referenceConstantToSmt(new SyReferenceConstantSymbol(s)));
				retVal.append(") ");
				retVal.append(((SyDeclClassLit) C).className());
				retVal.append(") ");
			}
			retVal.append("))\n");
		}
		return retVal.toString();
	}
	
	private String declareVars(SyProgram P, List<SyValue> pathCondition) {
		var symbolsPrimitive = new LinkedHashSet<SySymbol>(); 
		var symbolsReference = new LinkedHashSet<SySymbol>();
		var symbolsLoc = new LinkedHashSet<SyLoc>();
		
		final StringBuilder retVal = new StringBuilder();
		for (SyValue sigma : pathCondition) {
			retVal.append(declareVarsClause(P, sigma, symbolsPrimitive, symbolsReference, symbolsLoc));
		}
		retVal.append(declareVarsReferenceConstraints(P, symbolsReference));
		return retVal.toString();
	}
	
	public String pathConditionToSmt(SyProgram P, List<SyValue> pathCondition) {
		Objects.requireNonNull(P);
		Objects.requireNonNull(pathCondition);
		
		return smtDecls(P) + declareVars(P, pathCondition) + clausesToSmt(P, pathCondition);
	}
	
	public String configToSmt(SemConfiguration J) {
		Objects.requireNonNull(J);
		
		var P = J.syProgramLit();
		var sSigma = J.pathCondition();
		return pathConditionToSmt(P, sSigma);
	}
}
