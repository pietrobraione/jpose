package jpose.semantics.interpreter;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.ListIterator;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.SequencedMap;
import java.util.stream.Collectors;

import jpose.semantics.types.SemConfiguration;
import jpose.semantics.types.SemObject;
import jpose.smt.SmtSolver;
import jpose.syntax.SyBool;
import jpose.syntax.SyBoolFalse;
import jpose.syntax.SyBoolTrue;
import jpose.syntax.SyDeclClass;
import jpose.syntax.SyDeclClassLit;
import jpose.syntax.SyDeclMethodLit;
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
import jpose.syntax.SyIntLit;
import jpose.syntax.SyLoc;
import jpose.syntax.SyLocLit;
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
import jpose.syntax.SyTypeClass;
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

public final class Interpreter { 
	public void stepRefinement(SemConfiguration J) {
		Objects.requireNonNull(J);
		
		var e = J.syExpression();
		if (e instanceof SyExpressionGetfield syExpressionGetfield) {
			stepRefinementHandleGetfield(J, syExpressionGetfield);
		} else if (e instanceof SyExpressionPutfield syExpressionPutfield) {
			stepRefinementHandlePutfield(J, syExpressionPutfield);
		} else if (e instanceof SyExpressionLet(String x, SyExpression e1, SyExpression e2)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionAdd(SyExpressionValue e2, SyExpression e1)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionAdd(SyExpression e1, SyExpression e2)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionSub(SyExpressionValue e2, SyExpression e1)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionSub(SyExpression e1, SyExpression e2)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionLt(SyExpressionValue e2, SyExpression e1)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionLt(SyExpression e1, SyExpression e2)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionAnd(SyExpressionValue e2, SyExpression e1)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionAnd(SyExpression e1, SyExpression e2)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionOr(SyExpressionValue e2, SyExpression e1)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionOr(SyExpression e1, SyExpression e2)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionNot(SyExpression e1)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionEq(SyExpressionValue e2, SyExpression e1)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionEq(SyExpression e1, SyExpression e2)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionInstanceof(SyExpression e1, String c)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionIf(SyExpression e1, SyExpression e2, SyExpression e3)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionInvoke(SyExpressionValue e2, String m, SyExpression e1)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else if (e instanceof SyExpressionInvoke(SyExpressionValue e1, String m, SyExpression e2)) {
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException exc) {
				throw exc;
			} finally {
				J.setSyExpression(e);
			}
		} else {
			throw new StuckException("Cannot step-refine an expression");
		}
	}
	
	private void stepRefinementHandleGetfield(SemConfiguration J, SyExpressionGetfield syExpressionGetfield) {
		if (syExpressionGetfield instanceof SyExpressionGetfield(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantSymbol Y)), String f)) {
			var YY = new SyValueReferenceConstant(Y);
			if (J.unresolved(Y.sySymbol())) {
				var maybeC = J.syProgramLit().classWithField(f);
				maybeC.ifPresentOrElse(syDeclClass -> {
					switch (syDeclClass) {
					case SyDeclClassLit C:
						var c = C.className();
						var o = new SemObject(J.syProgramLit(), c, true);
						J.addObjectSymbolic(Y.sySymbol(), o);
						var cl1 = new SyValueNot(new SyValueEq(YY, new SyValueReferenceConstant(new SyReferenceConstantNull())));
						var cl2 = new SyValueSubtypeRel(YY, new SyTypeClass(c));
						J.addPathConditionClause(cl1);
						J.addPathConditionClause(cl2);
					}
				}, () -> {
					throw new RuntimeException("No class has field " + f);
				});
			} else {
				var maybeo = J.objectAt(Y);
				maybeo.ifPresentOrElse(o -> {
					var maybev = o.get(f);
					maybev.ifPresentOrElse(v -> {
						if (v instanceof SyValueUnassumed) {
							var maybeC = J.syProgramLit().classWithField(f);
							maybeC.ifPresentOrElse(syDeclClass -> {
								switch (syDeclClass) {
								case SyDeclClassLit C1:
									var maybef = C1.fdecl(f);
									maybef.ifPresentOrElse(F -> {
										switch (F) {
										case SyDeclVariableLit syDeclVariableLit:
											var t = syDeclVariableLit.syType();
											var s1 = freshSymbol(Y.sySymbol(), f);
											var sigma1 = t.isPrimitive() ? new SyValuePrimitiveConstant(new SyPrimitiveConstantSymbol(s1)) : 
												new SyValueReferenceConstant(new SyReferenceConstantSymbol(s1));
											var sigma = J.assume(Y, f, sigma1);
											o.upd(f, sigma);
											var cl = new SyValueFieldRel(Y.sySymbol(), f, s1);
											J.addPathConditionClause(cl);
										}
									}, () -> {
										throw new AssertionError("Unexpected field " + f + " missing from class " + C1.className());
									});
								}
							}, () -> {
								throw new RuntimeException("No class has field " + f);
							});
						} else {
							throw new StuckException("Field " + f + " of object " + Y + " was already refined");
						}
					}, () -> {
						var maybeC = J.syProgramLit().classWithField(f);
						maybeC.ifPresentOrElse(syDeclClass -> {
							switch (syDeclClass) {
							case SyDeclClassLit C1:
								var c1 = C1.className();
								o.refine(c1);
								var cl = new SyValueSubtypeRel(YY, new SyTypeClass(c1));
								J.addPathConditionClause(cl);
							}
						}, () -> {
							throw new RuntimeException("No class has field " + f);
						});
					});
				}, () -> {
					throw new AssertionError("Symbolic reference is resolved but not associated with a symbolic object");
				});
			}
		} else { 
			var syExpressionSaved = syExpressionGetfield;
			J.setSyExpression(syExpressionGetfield.syExpression());
			try {
				stepRefinement(J);
			} catch (StuckException e) {
				throw e;
			} finally {
				J.setSyExpression(syExpressionSaved);
			}
		}
	}
	
	private SySymbolField freshSymbol(SySymbol sySymbol, String fieldName) {
		final SySymbolField s1;
		switch (sySymbol) {
		case SySymbolExpression sySymbolExpression:
			s1 = new SySymbolField(sySymbolExpression.id(), List.of(fieldName));
			break;
		case SySymbolField sySymbolField:
			var l = new ArrayList<>(sySymbolField.fieldNames());
			l.add(fieldName);
			s1 = new SySymbolField(sySymbolField.id(), Collections.unmodifiableList(l));
			break;			
		}
		return s1;
	}
	
	private void stepRefinementHandlePutfield(SemConfiguration J, SyExpressionPutfield syExpressionPutfield) {
		if (syExpressionPutfield instanceof SyExpressionPutfield(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantSymbol(SySymbol s))), String f, SyExpressionValue sigma)) {
			if (J.unresolved(s)) {
				var maybeC = J.syProgramLit().classWithField(f);
				maybeC.ifPresentOrElse(syDeclClass -> {
					switch (syDeclClass) {
					case SyDeclClassLit C:
						var c = C.className();
						var o = new SemObject(J.syProgramLit(), c, true);
						J.addObjectSymbolic(s, o);
						var YY = new SyValueReferenceConstant(new SyReferenceConstantSymbol(s));
						var cl1 = new SyValueNot(new SyValueEq(YY, new SyValueReferenceConstant(new SyReferenceConstantNull())));
						var cl2 = new SyValueSubtypeRel(YY, new SyTypeClass(c));
						J.addPathConditionClause(cl1);
						J.addPathConditionClause(cl2);
					}
				}, () -> {
					throw new RuntimeException("No class has field " + f);
				});
			} else {
				var Y = new SyReferenceConstantSymbol(s);
				var maybeo = J.objectAt(Y);
				maybeo.ifPresentOrElse(o -> {
					o.get(f).ifPresentOrElse(v -> {
						throw new StuckException("Field " + f + " of object " + Y + " was already refined");
					}, () -> {
						var maybeC = J.syProgramLit().classWithField(f);
						maybeC.ifPresentOrElse(syDeclClass -> {
							switch (syDeclClass) {
							case SyDeclClassLit C1:
								var c1 = C1.className();
								o.refine(c1);
								var cl = new SyValueSubtypeRel(new SyValueReferenceConstant(Y), new SyTypeClass(c1));
								J.addPathConditionClause(cl);
							}
						}, () -> {
							throw new RuntimeException("No class has field " + f);
						});
					});
				}, () -> {
					throw new AssertionError("Symbolic reference is resolved but not associated with a symbolic object");
				});
			}
		} else if (syExpressionPutfield instanceof SyExpressionPutfield(SyExpressionValue v, String f, SyExpression e1)) {
			var syExpressionSaved = syExpressionPutfield;
			J.setSyExpression(e1);
			try {
				stepRefinement(J);
			} catch (StuckException e) {
				throw e;
			} finally {
				J.setSyExpression(syExpressionSaved);
			}
		} else {
			var syExpressionSaved = syExpressionPutfield;
			J.setSyExpression(syExpressionPutfield.syExpressionFirst());
			try {
				stepRefinement(J);
			} catch (StuckException e) {
				throw e;
			} finally {
				J.setSyExpression(syExpressionSaved);
			}
		}
	}
	
	public void stepRefinementStar(SemConfiguration J) {
		while (true) {
			try {
				stepRefinement(J);
			} catch (StuckException e) {
				return;
			}
		}
	}
	
	public List<SemConfiguration> stepComputation(SemConfiguration J) {
		Objects.requireNonNull(J);

		var e = J.syExpression();
		if (e instanceof SyExpressionNew syExpressionNew) {
			return stepComputationHandleNew(J, syExpressionNew);
		} else if (e instanceof SyExpressionGetfield syExpressionGetfield) {
			return stepComputationHandleGetfield(J, syExpressionGetfield);
		} else if (e instanceof SyExpressionPutfield syExpressionPutfield) {
			return stepComputationHandlePutfield(J, syExpressionPutfield);
		} else if (e instanceof SyExpressionLet(String x, SyExpressionValue(SyValue sigma), SyExpression e1)) {
			var eNew = e1.replace(x, new SyExpressionValue(sigma));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (e instanceof SyExpressionLet(String x, SyExpression e1, SyExpression e2)) {
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionLet(x, e1New, e2));
			}
			return Js;
		} else if (e instanceof SyExpressionAdd(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantInt(SyIntLit(int n1)))),SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantInt(SyIntLit(int n2)))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantInt(new SyIntLit(n1 + n2))));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (e instanceof SyExpressionAdd(SyExpressionValue(SyValue sigma1), SyExpressionValue(SyValue sigma2))) {
			var eNew = new SyExpressionValue(new SyValueAdd(sigma1, sigma2));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (e instanceof SyExpressionAdd(SyExpressionValue(SyValue sigma), SyExpression e1)) {
			var e2 = new SyExpressionValue(sigma);
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionAdd(e2, e1New));
			}
			return Js;
		} else if (e instanceof SyExpressionAdd(SyExpression e1, SyExpression e2)) {
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionAdd(e1New, e2));
			}
			return Js;
		} else if (e instanceof SyExpressionSub(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantInt(SyIntLit(int n1)))),SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantInt(SyIntLit(int n2)))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantInt(new SyIntLit(n1 - n2))));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (e instanceof SyExpressionSub(SyExpressionValue(SyValue sigma1), SyExpressionValue(SyValue sigma2))) {
			var eNew = new SyExpressionValue(new SyValueSub(sigma1, sigma2));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (e instanceof SyExpressionSub(SyExpressionValue(SyValue sigma), SyExpression e1)) {
			var e2 = new SyExpressionValue(sigma);
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionSub(e2, e1New));
			}
			return Js;
		} else if (e instanceof SyExpressionSub(SyExpression e1, SyExpression e2)) {
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionSub(e1New, e2));
			}
			return Js;
		} else if (e instanceof SyExpressionLt(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantInt(SyIntLit(int n1)))),SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantInt(SyIntLit(int n2)))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(n1 < n2 ? new SyBoolTrue() : new SyBoolFalse())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (e instanceof SyExpressionLt(SyExpressionValue(SyValue sigma1), SyExpressionValue(SyValue sigma2))) {
			var eNew = new SyExpressionValue(new SyValueLt(sigma1, sigma2));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (e instanceof SyExpressionLt(SyExpressionValue(SyValue sigma), SyExpression e1)) {
			var e2 = new SyExpressionValue(sigma);
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionLt(e2, e1New));
			}
			return Js;
		} else if (e instanceof SyExpressionLt(SyExpression e1, SyExpression e2)) {
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionLt(e1New, e2));
			}
			return Js;
		} else if (e instanceof SyExpressionAnd syExpressionAnd) {
			return stepComputationHandleAnd(J, syExpressionAnd);
		} else if (e instanceof SyExpressionOr syExpressionOr) {
			return stepComputationHandleOr(J, syExpressionOr);
		} else if (e instanceof SyExpressionNot syExpressionNot) {
			return stepComputationHandleNot(J, syExpressionNot);
		} else if (e instanceof SyExpressionEq syExpressionEq) {
			return stepComputationHandleEq(J, syExpressionEq);
		} else if (e instanceof SyExpressionInstanceof(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantNull n)), String c)) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolFalse())));			
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (e instanceof SyExpressionInstanceof(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantLoc(SyLocLit(int p)))), String c)) {
			var l = new SyReferenceConstantLoc(new SyLocLit(p));
			var maybeo = J.objectAt(l);
			maybeo.ifPresentOrElse(o -> {
				var cNew = o.className();
				var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(J.syProgramLit().isSubclass(cNew, c) ? new SyBoolTrue() : new SyBoolFalse())));			
				J.setSyExpression(eNew);
			}, () -> {
				throw new RuntimeException("No concrete object is present at location " + p);
			});
			return List.of(J);
		} else if (e instanceof SyExpressionInstanceof(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantSymbol(SySymbol s))), String c)) {
			var Y = new SyReferenceConstantSymbol(s);
			var eNew = new SyExpressionValue(new SyValueSubtypeRel(new SyValueReferenceConstant(Y), new SyTypeClass(c)));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (e instanceof SyExpressionInstanceof syExpressionInstanceof) {
			var e1 = syExpressionInstanceof.syExpression();
			var c = syExpressionInstanceof.className();
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionInstanceof(e1New, c));
			}
			return Js;
		} else if (e instanceof SyExpressionIf(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolTrue t))), SyExpression e1, SyExpression e2)) {
			J.setSyExpression(e1);
			return List.of(J);
		} else if (e instanceof SyExpressionIf(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolFalse f))), SyExpression e1, SyExpression e2)) {
			J.setSyExpression(e2);
			return List.of(J);
		} else if (e instanceof SyExpressionIf(SyExpressionValue(SyValue sigma), SyExpression e1, SyExpression e2)) {
			var J2 = new SemConfiguration(J);
			J.setSyExpression(e1);
			J2.setSyExpression(e2);
			J.addPathConditionClause(sigma);
			J2.addPathConditionClause(new SyValueNot(sigma));
			return List.of(J, J2);
		} else if (e instanceof SyExpressionIf syExpressionIf) {
			var e1 = syExpressionIf.syExpressionCond();
			var e2 = syExpressionIf.syExpressionThen();
			var e3 = syExpressionIf.syExpressionElse();
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionIf(e1New, e2, e3));
			}
			return Js;
		} else if (e instanceof SyExpressionInvoke(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantLoc(SyLocLit(int p)))), String m, SyExpressionValue(SyValue sigma))) {
			var l = new SyReferenceConstantLoc(new SyLocLit(p));
			var maybeo = J.objectAt(l);
			maybeo.ifPresentOrElse(o -> {
				var c = o.className();
				var maybeCProvider = J.syProgramLit().methodProvider(m, c);
				maybeCProvider.ifPresentOrElse(CProvider -> {
					if (CProvider instanceof SyDeclClassLit CProviderLit) {
						var maybeM = CProviderLit.mdecl(m);
						maybeM.ifPresentOrElse(M -> {
							if (M instanceof SyDeclMethodLit(SyType t1, String m2, SyDeclVariableLit(SyType t2, String xM), SyExpression eM)) {
								var eNew = eM.replace("this", new SyExpressionValue(new SyValueReferenceConstant(l)))
								           .replace(xM, new SyExpressionValue(sigma));
								J.setSyExpression(eNew);
							} else {
								throw new AssertionError("Unexpected ill-formed declaration of method " + m);
							}
						}, () -> {
							throw new AssertionError("Unexpected declaration of method " + m + " missing from provider class " + CProviderLit.className());
						});
					} else {
						throw new AssertionError("Unexpected type");
					}
				}, () -> {
					throw new RuntimeException("No method with name " + m + " is present in the class hierarchy");
				});
			}, () -> {
				throw new RuntimeException("No concrete object is present at location " + p);
			});
			return List.of(J);
		} else if (e instanceof SyExpressionInvoke(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantSymbol(SySymbol s))), String m, SyExpressionValue(SyValue sigma))) {
			var Y = new SyReferenceConstantSymbol(s);
			var CsImpls = J.syProgramLit().implementors(m);
			final ArrayList<SemConfiguration> retVal = new ArrayList<>();
			for (SyDeclClass CImpl : CsImpls) {
				if (CImpl instanceof SyDeclClassLit CImplLit) {
					var maybeM = CImplLit.mdecl(m);
					maybeM.ifPresentOrElse(M -> {
						if (M instanceof SyDeclMethodLit(SyType t1, String m2, SyDeclVariableLit(SyType t2, String xM), SyExpression eM)) {
							var O = J.syProgramLit().overriders(m, CImplLit.className());
							var cl1 = new SyValueNot(new SyValueEq(new SyValueReferenceConstant(Y), new SyValueReferenceConstant(new SyReferenceConstantNull())));
							var cl2 = new SyValueSubtypeRel(new SyValueReferenceConstant(Y), new SyTypeClass(CImplLit.className()));
							var clOthers = O.stream().map(C -> {
								return new SyValueNot(new SyValueSubtypeRel(new SyValueReferenceConstant(Y), new SyTypeClass(((SyDeclClassLit) C).className())));
							}).collect(Collectors.toList());
							var eNew = eM.replace("this", new SyExpressionValue(new SyValueReferenceConstant(Y)))
							           .replace(xM, new SyExpressionValue(sigma));
							var JNew = new SemConfiguration(J);
							JNew.addPathConditionClause(cl1);
							JNew.addPathConditionClause(cl2);
							for (var cl : clOthers) {
								JNew.addPathConditionClause(cl);
							}
							JNew.setSyExpression(eNew);
							retVal.add(JNew);
						} else {
							throw new AssertionError("Unexpected ill-formed declaration of method " + m);							
						}
					}, () -> {
						throw new AssertionError("Unexpected declaration of method " + m + " missing from implementor class " + CImplLit.className());
					});
				} else {
					throw new AssertionError("Unexpected type");
				}
			}
			return retVal;
		} else if (e instanceof SyExpressionInvoke(SyExpressionValue(SyValueIte(SyValue sigma, SyValue sigma1, SyValue sigma2)), String m, SyExpressionValue(SyValue sigmaNew))) {
			var e1 = new SyExpressionInvoke(new SyExpressionValue(sigma1), m, new SyExpressionValue(sigmaNew));
			var e2 = new SyExpressionInvoke(new SyExpressionValue(sigma2), m, new SyExpressionValue(sigmaNew));
			var J2 = new SemConfiguration(J);
			J.setSyExpression(e1);
			J2.setSyExpression(e2);
			var J1s = stepComputation(J);
			var J2s = stepComputation(J2);
			for (SemConfiguration JCurr : J1s) {
				JCurr.addPathConditionClause(sigma);
			}
			for (SemConfiguration JCurr : J2s) {
				JCurr.addPathConditionClause(new SyValueNot(sigma));
			}
			final ArrayList<SemConfiguration> retVal = new ArrayList<>();
			retVal.addAll(J1s);
			retVal.addAll(J2s);
			return retVal;
		} else if (e instanceof SyExpressionInvoke(SyExpressionValue(SyValue sigma), String m, SyExpression e1)) {
			var e2 = new SyExpressionValue(sigma);
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionInvoke(e2, m, e1New));
			}
			return Js;
		} else if (e instanceof SyExpressionInvoke syExpressionInvoke) {
			var e1 = syExpressionInvoke.syExpressionFirst();
			var m = syExpressionInvoke.methodName();
			var e2 = syExpressionInvoke.syExpressionSecond();
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionInvoke(e1New, m, e2));
			}
			return Js;
		} else if (e instanceof SyExpressionId(String idName)) {
			J.addConfigurationId(idName);
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolFalse())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else { //SyExpressionVariable, SyExpressionValue
			throw new StuckException("Cannot step-compute an expression");
		}
	}
	
	private List<SemConfiguration> stepComputationHandleNew(SemConfiguration J, SyExpressionNew syExpressionNew) {
		var maybeC = J.syProgramLit().cdecl(syExpressionNew.className());
		maybeC.ifPresentOrElse(C -> {
			var o = new SemObject(J.syProgramLit(), syExpressionNew.className(), false);
			var u = J.addObjectConcrete(o);
			var e1 = new SyExpressionValue(new SyValueReferenceConstant(u));
			J.setSyExpression(e1);
		}, () -> {
			throw new RuntimeException("Class " + syExpressionNew.className() + " does not exist");
		});
		return List.of(J);
	}
	
	private List<SemConfiguration> stepComputationHandleGetfield(SemConfiguration J, SyExpressionGetfield syExpressionGetfield) {
		if (syExpressionGetfield instanceof SyExpressionGetfield(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantLoc(SyLocLit(int p)))), String f)) {
			var l = new SyReferenceConstantLoc(new SyLocLit(p));
			J.objectAt(l).ifPresentOrElse(o -> {
				o.get(f).ifPresentOrElse(sigma -> {
					var e1 = new SyExpressionValue(sigma);
					J.setSyExpression(e1);
				}, () -> {
					throw new RuntimeException("Object does not have field " + f);
				});
			}, () -> {
				throw new RuntimeException("No concrete object is present at location " + p);
			});
			return List.of(J);
		} else if (syExpressionGetfield instanceof SyExpressionGetfield(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantSymbol(SySymbol s))), String f)) {
			var Y = new SyReferenceConstantSymbol(s);
			J.objectAt(Y).ifPresentOrElse(o -> {
				o.get(f).ifPresentOrElse(sigma -> {
					if (sigma instanceof SyValueUnassumed) {
						throw new RuntimeException("Attempted to read unassumed value from symbolic object");
					} else {
						var e1 = new SyExpressionValue(sigma);
						J.setSyExpression(e1);
					}
				}, () -> {
					throw new RuntimeException("Object does not have field " + f);
				});				
			}, () -> {
				throw new RuntimeException("No symbolic object is associated to symbol " + Y);
			});
			return List.of(J);
		} else if (syExpressionGetfield instanceof SyExpressionGetfield(SyExpressionValue(SyValueIte(SyValue sigma, SyValue sigma1, SyValue sigma2)), String f)) {
			var e1 = new SyExpressionGetfield(new SyExpressionValue(sigma1), f);
			var e2 = new SyExpressionGetfield(new SyExpressionValue(sigma2), f);
			var sSigma = J.pathCondition();
			J.setSyExpression(e1);
			stepRefinementStar(J);
			List<SemConfiguration> J1s;
			try {
				J1s = stepComputation(J);
			} catch (StuckException e) {
				J1s = List.of();
			}
			if (J1s.size() > 1) {
				throw new AssertionError("Unexpected branching while evaluating getfield");
			} else if (J1s.size() == 1) {
				var H1New = J.heap();
				var sSigma1New = J.pathCondition();
				var e1New = J.syExpression();
				if (e1New instanceof SyExpressionValue(SyValue sigma1New)) {
					J.setPathCondition(sSigma);
					J.setSyExpression(e2);
					stepRefinementStar(J);
					List<SemConfiguration> J2s;
					try {
						J2s = stepComputation(J);
					} catch (StuckException e) {
						J2s = List.of();
					}
					if (J2s.size() > 1) {
						throw new AssertionError("Unexpected branching while evaluating getfield");
					} else if (J2s.size() == 1) {
						var sSigma2New = J.pathCondition();
						var e2New = J.syExpression();
						if (e2New instanceof SyExpressionValue(SyValue sigma2New)) {
							var sSigmaNew = mergePathConditions(sSigma1New, sSigma2New, sigma);
							var eNew = new SyExpressionValue(new SyValueIte(sigma, sigma1New, sigma2New));
							J.setPathCondition(sSigmaNew);
							J.setSyExpression(eNew);
							return List.of(J);
						} else {
							throw new AssertionError("Unexpected expression " + e2New + " not reduced to value after a => step");
						}
					} else {
						J.setHeap(H1New);
						J.setPathCondition(sSigma1New);
						J.addPathConditionClause(sigma);
						J.setSyExpression(e1New);
						return List.of(J);
					}
				} else {
					throw new AssertionError("Unexpected expression " + e1New + " not reduced to value after a => step");
				}
			} else {
				J.setSyExpression(e2);
				stepRefinementStar(J);
				List<SemConfiguration> J2s;
				try {
					J2s = stepComputation(J);
				} catch (StuckException e) {
					J2s = List.of();
				}
				if (J2s.size() > 1) {
					throw new AssertionError("Unexpected branching while evaluating getfield");
				} else if (J2s.size() == 1) {
					J.addPathConditionClause(new SyValueNot(sigma));
					return List.of(J);
				} else {
					throw new AssertionError("Unexpected stuck state while evaluating getfield");
				}
			}
		} else {
			var e1 = syExpressionGetfield.syExpression();
			var f = syExpressionGetfield.fieldName();
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionGetfield(e1New, f));
			}
			return Js;
		}
	}
	
	private List<SyValue> mergePathConditions(List<SyValue> sSigma1New, List<SyValue> sSigma2New, SyValue sigma) {
		final ListIterator<SyValue> it1 = sSigma1New.listIterator();
		final ListIterator<SyValue> it2 = sSigma2New.listIterator();
		final ArrayList<SyValue> retVal = new ArrayList<>();
		
		while (it1.hasNext() && it2.hasNext()) {
			final SyValue sigma1 = it1.next();
			final SyValue sigma2 = it2.next();
			if (sigma1.equals(sigma2)) {
				retVal.add(sigma1);
			} else {
				it1.previous();
				it2.previous();
				break;
			}
		}
		while (it1.hasNext()) {
			final SyValue sigma1 = it1.next();
			retVal.add(new SyValueOr(new SyValueNot(sigma), sigma1));
		}
		while (it2.hasNext()) {
			final SyValue sigma2 = it2.next();
			retVal.add(new SyValueOr(sigma, sigma2));
		}
		
		return retVal;
	}
	
	private List<SemConfiguration> stepComputationHandlePutfield(SemConfiguration J, SyExpressionPutfield syExpressionPutfield) {
		if (syExpressionPutfield instanceof SyExpressionPutfield(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantLoc(SyLocLit(int n)))), String f, SyExpressionValue(SyValue sigma))) {
			var l = new SyReferenceConstantLoc(new SyLocLit(n));
			var eNew = new SyExpressionValue(sigma);
			var maybeo = J.objectAt(l);
			maybeo.ifPresentOrElse(o -> {
				o.upd(f, sigma);
				J.setSyExpression(eNew);
			}, () -> {
				throw new RuntimeException("No concrete object is present at location " + n);
			});
			return List.of(J);
		} else if (syExpressionPutfield instanceof SyExpressionPutfield(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantSymbol(SySymbol s))), String f, SyExpressionValue(SyValue sigma))) {
			var Y = new SyReferenceConstantSymbol(s);
			var eNew = new SyExpressionValue(sigma);
			var maybeo = J.objectAt(Y);
			maybeo.ifPresentOrElse(o -> {
				J.update(Y, f, sigma);
				o.upd(f, sigma);
				J.setSyExpression(eNew);
			}, () -> {
				throw new RuntimeException("No symbolic object is associated to symbol " + Y);
			});
			return List.of(J);
		} else if (syExpressionPutfield instanceof SyExpressionPutfield(SyExpressionValue(SyValueIte(SyValue sigma, SyValue sigma1, SyValue sigma2)), String f, SyExpressionValue(SyValue sigmaNew))) {
			var eNew = new SyExpressionValue(sigmaNew);
			var e1 = new SyExpressionPutfield(new SyExpressionValue(sigma1), f, eNew);
			var e2 = new SyExpressionPutfield(new SyExpressionValue(sigma2), f, eNew);
			var J1 = new SemConfiguration(J);
			var J2 = new SemConfiguration(J);
			J1.setSyExpression(e1);
			J2.setSyExpression(e2);
			stepRefinementStar(J1);
			List<SemConfiguration> J1s;
			try {
				J1s = stepComputation(J1);
			} catch (StuckException e) {
				J1s = List.of();
			}
			stepRefinementStar(J2);
			List<SemConfiguration> J2s;
			try {
				J2s = stepComputation(J2);
			} catch (StuckException e) {
				J2s = List.of();
			}
			if (J1s.size() > 1 || J2s.size() > 1) {
				throw new AssertionError("Unexpected branching while evaluating putfield");
			} else if (J1s.size() == 1 && J2s.size() == 1) {
				var HNew = mergeHeaps(J1.heap(), J2.heap(), sigma, f, J.syProgramLit());
				var sSigmaNew = mergePathConditions(J1.pathCondition(), J2.pathCondition(), sigma);
				var sSigmaEtc = mergeClauses(J1.heap(), J2.heap(), f);
				sSigmaNew.addAll(sSigmaEtc);
				J.setHeap(HNew);
				J.setPathCondition(sSigmaNew);
				J.setSyExpression(eNew);
				return List.of(J);
			} else if (J1s.size() == 1 && J2s.size() == 0) {
				J.setHeap(J1.heap());
				J.setPathCondition(J1.pathCondition());
				J.addPathConditionClause(sigma);
				J.setSyExpression(eNew);
				return List.of(J);
			} else if (J1s.size() == 0 && J2s.size() == 1) {
				J.setHeap(J2.heap());
				J.setPathCondition(J2.pathCondition());
				J.addPathConditionClause(new SyValueNot(sigma));
				J.setSyExpression(eNew);
				return List.of(J);
			} else {
				throw new AssertionError("Unexpected stuck state while evaluating putfield");
			}
		} else if (syExpressionPutfield instanceof SyExpressionPutfield(SyExpressionValue(SyValue sigma), String f, SyExpression e1)) {
			var e2 = new SyExpressionValue(sigma);
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionPutfield(e2, f, e1New));
			}
			return Js;
		} else {
			var e1 = syExpressionPutfield.syExpressionFirst();
			var f = syExpressionPutfield.fieldName();
			var e2 = syExpressionPutfield.syExpressionSecond();
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionPutfield(e1New, f, e2));
			}
			return Js;
		}	
	}
	
	private SequencedMap<SyReferenceConstant, SemObject> mergeHeaps(SequencedMap<SyReferenceConstant, SemObject> H1New, SequencedMap<SyReferenceConstant, SemObject> H2New, SyValue sigma, String f, SyProgramLit P) {
		final SyType[] t = new SyType[1];
		((SyProgramLit) P).classWithField(f).ifPresentOrElse(C -> {
			((SyDeclClassLit) C).fdecl(f).ifPresentOrElse(F -> {
				t[0] = ((SyDeclVariableLit) F).syType();
			}, () ->{
				throw new AssertionError("Unexpected missing field " + f); 
			});
		}, () -> {
			throw new RuntimeException("Field " + f + " does not exist in any class");
		});
		
		final Iterator<Entry<SyReferenceConstant, SemObject>> it1 = H1New.sequencedEntrySet().iterator();
		final Iterator<Entry<SyReferenceConstant, SemObject>> it2 = H2New.sequencedEntrySet().iterator();
		final LinkedHashMap<SyReferenceConstant, SemObject> retVal = new LinkedHashMap<>();
		
		Entry<SyReferenceConstant, SemObject> e1Saved = null, e2Saved = null;
		while (it1.hasNext() && it2.hasNext()) {
			var e1 = it1.next();
			var e2 = it2.next();
			var u1 = e1.getKey();
			var u2 = e2.getKey();
			var o1 = e1.getValue();
			var o2 = e2.getValue();
			if (u1.equals(u2) && o1.equivalent(o2)) {
				retVal.put(u1, new SemObject(o1));
			} else if (u1.equals(u2) && o1.equivalentExcept(o2, f)) {
				if (!(o1.get(f).get() instanceof SyValueUnassumed) &&
				    !(o2.get(f).get() instanceof SyValueUnassumed)) {
					var oNew = new SemObject(o1);
					oNew.upd(f, new SyValueIte(sigma, o1.get(f).get(), o2.get(f).get()));
					retVal.put(u1, oNew);
				} else if (o2.get(f).get() instanceof SyValueUnassumed) {
					var Y1 = (SyReferenceConstantSymbol) u1;
					var s = freshSymbol(Y1.sySymbol(), f);
					var Z = t[0].isPrimitive() ? 
							(new SyValuePrimitiveConstant(new SyPrimitiveConstantSymbol(s))) :
							(new SyValueReferenceConstant(new SyReferenceConstantSymbol(s)));
					var oNew = new SemObject(o1);
					oNew.upd(f, new SyValueIte(sigma, o1.get(f).get(), Z));
					retVal.put(u1, oNew);
				} else { //o1.get(f).get() instanceof SyValueUnassumed
					var Y1 = (SyReferenceConstantSymbol) u1;
					var s = freshSymbol(Y1.sySymbol(), f);
					var Z = t[0].isPrimitive() ? 
							(new SyValuePrimitiveConstant(new SyPrimitiveConstantSymbol(s))) :
							(new SyValueReferenceConstant(new SyReferenceConstantSymbol(s)));
					var oNew = new SemObject(o1);
					oNew.upd(f, new SyValueIte(sigma, Z, o2.get(f).get()));
					retVal.put(u1, oNew);
				}
			} else {
				e1Saved = e1;
				e2Saved = e2;
			}
		}
		
		while (it1.hasNext() || e1Saved != null) {
			var e1 = (e1Saved == null ? it1.next() : e1Saved);
			e1Saved = null;
			var u1 = e1.getKey();
			var o1 = e1.getValue();
			if (u1 instanceof SyReferenceConstantSymbol Y1 &&
			    o1.get(f).isPresent() && !(o1.get(f).get() instanceof SyValueUnassumed)) {
				var s = freshSymbol(Y1.sySymbol(), f);
				var Z = t[0].isPrimitive() ?
						(new SyValuePrimitiveConstant(new SyPrimitiveConstantSymbol(s))) :
						(new SyValueReferenceConstant(new SyReferenceConstantSymbol(s)));
				var oNew = new SemObject(o1);
				oNew.upd(f, new SyValueIte(sigma, o1.get(f).get(), Z));
				retVal.put(u1, oNew);
			} else {
				throw new AssertionError("Unexpected object while merging heaps");
			}
		}
		
		while (it2.hasNext() || e2Saved != null) {
			var e2 = (e2Saved == null ? it2.next() : e2Saved);
			e2Saved = null;
			var u2 = e2.getKey();
			var o2 = e2.getValue();
			if (u2 instanceof SyReferenceConstantSymbol Y2 &&
			    o2.get(f).isPresent() && !(o2.get(f).get() instanceof SyValueUnassumed)) {
				var Z = new SyValueReferenceConstant(new SyReferenceConstantSymbol(freshSymbol(Y2.sySymbol(), f)));
				var oNew = new SemObject(o2);
				oNew.upd(f, new SyValueIte(sigma, Z, o2.get(f).get()));
				retVal.put(u2, oNew);
			} else {
				throw new AssertionError("Unexpected object while merging heaps");
			}
		}
		
		return retVal;
	}
	
	private List<SyValue> mergeClauses(SequencedMap<SyReferenceConstant, SemObject> H1New, SequencedMap<SyReferenceConstant, SemObject> H2New, String f) {
		final Iterator<Entry<SyReferenceConstant, SemObject>> it1 = H1New.sequencedEntrySet().iterator();
		final Iterator<Entry<SyReferenceConstant, SemObject>> it2 = H2New.sequencedEntrySet().iterator();
		final ArrayList<SyValue> retVal = new ArrayList<>();
		
		Entry<SyReferenceConstant, SemObject> e1Saved = null, e2Saved = null;
		while (it1.hasNext() && it2.hasNext()) {
			var e1 = it1.next();
			var e2 = it2.next();
			var u1 = e1.getKey();
			var u2 = e2.getKey();
			var o1 = e1.getValue();
			var o2 = e2.getValue();
			if (u1.equals(u2) && o1.equivalent(o2)) {
				//do nothing
			} else if (u1.equals(u2) && o1.equivalentExcept(o2, f)) {
				//do nothing
			} else {
				e1Saved = e1;
				e2Saved = e2;
			}
		}
		
		while (it1.hasNext() || e1Saved != null) {
			var e1 = (e1Saved == null ? it1.next() : e1Saved);
			e1Saved = null;
			var u1 = e1.getKey();
			var o1 = e1.getValue();
			if (u1 instanceof SyReferenceConstantSymbol Y1 &&
			    o1.get(f).isPresent() && !(o1.get(f).get() instanceof SyValueUnassumed)) {
				var sNew = freshSymbol(Y1.sySymbol(), f);
				var sigma = new SyValueFieldRel(Y1.sySymbol(), f, sNew);
				retVal.add(sigma);
			} else {
				throw new AssertionError("Unexpected object while merging heaps");
			}
		}
		
		while (it2.hasNext() || e2Saved != null) {
			var e2 = (e2Saved == null ? it2.next() : e2Saved);
			e2Saved = null;
			var u2 = e2.getKey();
			var o2 = e2.getValue();
			if (u2 instanceof SyReferenceConstantSymbol Y2 &&
			    o2.get(f).isPresent() && !(o2.get(f).get() instanceof SyValueUnassumed)) {
				var sNew = freshSymbol(Y2.sySymbol(), f);
				var sigma = new SyValueFieldRel(Y2.sySymbol(), f, sNew);
				retVal.add(sigma);
			} else {
				throw new AssertionError("Unexpected object while merging heaps");
			}
		}
		
		return retVal;
	}
	
	private List<SemConfiguration> stepComputationHandleAnd(SemConfiguration J, SyExpressionAnd syExpressionAnd) {
		if (syExpressionAnd instanceof SyExpressionAnd(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolTrue t1))), SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolTrue t2))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolTrue())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionAnd instanceof SyExpressionAnd(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolTrue t1))), SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolFalse t2))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolFalse())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionAnd instanceof SyExpressionAnd(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolFalse t1))), SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolTrue t2))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolFalse())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionAnd instanceof SyExpressionAnd(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolFalse t1))), SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolFalse t2))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolFalse())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionAnd instanceof SyExpressionAnd(SyExpressionValue(SyValue sigma1), SyExpressionValue(SyValue sigma2))) {
			var eNew = new SyExpressionValue(new SyValueAnd(sigma1, sigma2));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionAnd instanceof SyExpressionAnd(SyExpressionValue(SyValue sigma), SyExpression e1)) {
			var e2 = new SyExpressionValue(sigma);
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionAnd(e2, e1New));
			}
			return Js;
		} else {
			var e1 = syExpressionAnd.syExpressionFirst();
			var e2 = syExpressionAnd.syExpressionSecond();
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionAnd(e1New, e2));
			}
			return Js;
		}
	}
	
	private List<SemConfiguration> stepComputationHandleOr(SemConfiguration J, SyExpressionOr syExpressionOr) {
		if (syExpressionOr instanceof SyExpressionOr(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolTrue t1))), SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolTrue t2))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolTrue())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionOr instanceof SyExpressionOr(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolTrue t1))), SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolFalse t2))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolTrue())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionOr instanceof SyExpressionOr(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolFalse t1))), SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolTrue t2))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolTrue())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionOr instanceof SyExpressionOr(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolFalse t1))), SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolFalse t2))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolFalse())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionOr instanceof SyExpressionOr(SyExpressionValue(SyValue sigma1), SyExpressionValue(SyValue sigma2))) {
			var eNew = new SyExpressionValue(new SyValueOr(sigma1, sigma2));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionOr instanceof SyExpressionOr(SyExpressionValue(SyValue sigma), SyExpression e1)) {
			var e2 = new SyExpressionValue(sigma);
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionOr(e2, e1New));
			}
			return Js;
		} else {
			var e1 = syExpressionOr.syExpressionFirst();
			var e2 = syExpressionOr.syExpressionSecond();
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionOr(e1New, e2));
			}
			return Js;
		}
	}
	
	private List<SemConfiguration> stepComputationHandleNot(SemConfiguration J, SyExpressionNot syExpressionNot) {
		if (syExpressionNot instanceof SyExpressionNot(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolTrue t1))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolFalse())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionNot instanceof SyExpressionNot(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBoolFalse t1))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolTrue())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionNot instanceof SyExpressionNot(SyExpressionValue(SyValue sigma1))) {
			var eNew = new SyExpressionValue(new SyValueNot(sigma1));
			J.setSyExpression(eNew);
			return List.of(J);
		} else {
			var e1 = syExpressionNot.syExpression();
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionNot(e1New));
			}
			return Js;
		}
	}

	private List<SemConfiguration> stepComputationHandleEq(SemConfiguration J, SyExpressionEq syExpressionEq) {
		if (syExpressionEq instanceof SyExpressionEq(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantInt(SyIntLit(int n1)))), SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantInt(SyIntLit(int n2)))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(n1 == n2 ? new SyBoolTrue() :  new SyBoolFalse())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionEq instanceof SyExpressionEq(SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBool b1))), SyExpressionValue(SyValuePrimitiveConstant(SyPrimitiveConstantBool(SyBool b2))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(b1.equals(b2) ? new SyBoolTrue() :  new SyBoolFalse())));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionEq instanceof SyExpressionEq(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantNull())), SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantNull())))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolTrue())));			
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionEq instanceof SyExpressionEq(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantLoc(SyLoc l))), SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantNull())))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolFalse())));			
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionEq instanceof SyExpressionEq(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantNull())), SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantLoc(SyLoc l))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolFalse())));			
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionEq instanceof SyExpressionEq(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantLoc(SyLocLit(int p1)))), SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantLoc(SyLocLit(int p2)))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(p1 == p2 ? new SyBoolTrue() : new SyBoolFalse())));			
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionEq instanceof SyExpressionEq(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantLoc(SyLoc l))), SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantSymbol(SySymbol s))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolFalse())));			
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionEq instanceof SyExpressionEq(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantSymbol(SySymbol s))), SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantLoc(SyLoc l))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolFalse())));			
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionEq instanceof SyExpressionEq(SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantLoc(SyLoc l))), SyExpressionValue(SyValueIte(SyValue sigma1, SyValue sigma2, SyValue sigma3)))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolFalse())));			
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionEq instanceof SyExpressionEq(SyExpressionValue(SyValueIte(SyValue sigma1, SyValue sigma2, SyValue sigma3)), SyExpressionValue(SyValueReferenceConstant(SyReferenceConstantLoc(SyLoc l))))) {
			var eNew = new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantBool(new SyBoolFalse())));			
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionEq instanceof SyExpressionEq(SyExpressionValue(SyValue sigma1), SyExpressionValue(SyValue sigma2))) {
			var eNew = new SyExpressionValue(new SyValueEq(sigma1, sigma2));
			J.setSyExpression(eNew);
			return List.of(J);
		} else if (syExpressionEq instanceof SyExpressionEq(SyExpressionValue(SyValue sigma), SyExpression e1)) {
			var e2 = new SyExpressionValue(sigma);
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionEq(e2, e1New));
			}
			return Js;
		} else {
			var e1 = syExpressionEq.syExpressionFirst();
			var e2 = syExpressionEq.syExpressionSecond();
			J.setSyExpression(e1);
			var Js = stepComputation(J);
			for (SemConfiguration JCurr : Js) {
				var e1New = JCurr.syExpression();
				JCurr.setSyExpression(new SyExpressionEq(e1New, e2));
			}
			return Js;
		}
	}
	
	public List<SemConfiguration> step(SemConfiguration J) {
		Objects.requireNonNull(J);

		J.resetAtBranch();
		J.resetCompanion();
		var prePathConditionSize = J.pathCondition().size();
		stepRefinementStar(J);
		var Js = stepComputation(J);
		for (var Jnext : Js) {
			if (Jnext.pathCondition().size() > prePathConditionSize) {
				Jnext.setAtBranch();
			}
		}
		if (Js.size() == 2) {
			var Jnext0 = Js.get(0);
			var Jnext1 = Js.get(1);
			Jnext0.setCompanion(Jnext1);
			Jnext1.setCompanion(Jnext0);
		}
		return Js;
	}
	
	public boolean isLeaf(SemConfiguration J) {
		Objects.requireNonNull(J);
		
		var e = J.syExpression();
		return ((e instanceof SyExpressionVariable) || (e instanceof SyExpressionValue));		
	}
	
	public List<SemConfiguration> stepAt(SyProgram p, int n) {
		return stepAtPrune(p, n, null);
	}
	
	public List<SemConfiguration> stepAtPrune(SyProgram p, int n, SmtSolver solver) {
		Objects.requireNonNull(p);
		if (n < 0) {
			throw new RuntimeException("Invalid depth " + n);
		}
		
		var J0 = new SemConfiguration(p);
		var Js = List.of(J0);
		for (int i = 0; i < n; ++i) {
			//System.out.println(i);
			Js = Js.stream().filter(J -> { return !isLeaf(J); }).map(J -> { return step(J); }).flatMap(Collection::stream).collect(Collectors.toList());
			if (solver != null) {
				Js = Js.stream().filter(solver::filter).collect(Collectors.toList());
			}
		}
		
		return Js;
	}
	
	public List<SemConfiguration> leavesAt(SyProgram p, int n) {
		return leavesAtPrune(p, n, null);
	}
	
	public List<SemConfiguration> leavesAtPrune(SyProgram p, int n, SmtSolver solver) {
		Objects.requireNonNull(p);
		if (n < 0) {
			throw new RuntimeException("Invalid depth " + n);
		}
		
		var J0 = new SemConfiguration(p);
		var Js = List.of(J0);
		var retVal = new ArrayList<SemConfiguration>();
		for (int i = 0; i < n; ++i) {
			//System.out.println(i);
			Js = Js.stream().filter(J -> { return !isLeaf(J); }).map(J -> { return step(J); }).flatMap(Collection::stream).collect(Collectors.toList());
			if (solver != null) {
				Js = Js.stream().filter(solver::filter).collect(Collectors.toList());
			}
			retVal.addAll(Js.stream().filter(J -> { return isLeaf(J); }).collect(Collectors.toList()));
		}
		
		return retVal;
	}
}