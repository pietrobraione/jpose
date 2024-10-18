package jpose.smt;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

import jdd.bdd.BDD;
import jpose.semantics.types.SemConfiguration;
import jpose.syntax.SyReferenceConstantSymbol;
import jpose.syntax.SyValue;
import jpose.syntax.SyValueAdd;
import jpose.syntax.SyValueAnd;
import jpose.syntax.SyValueEq;
import jpose.syntax.SyValueIte;
import jpose.syntax.SyValueLt;
import jpose.syntax.SyValueNot;
import jpose.syntax.SyValueOr;
import jpose.syntax.SyValueReferenceConstant;
import jpose.syntax.SyValueSub;

public final class SmtSolverUnwind implements SmtSolver {
	private final SmtSolverPlain smtSolverPlain;
	private final TrieClause cacheUnsat;
	private final boolean doNotUseOptimizations;
	private final boolean doNotUnwind;
	
	public SmtSolverUnwind(Path solverPath, boolean doNotUseOptimizations, boolean doNotUnwind) {
		this.smtSolverPlain = new SmtSolverPlain(solverPath);
		this.cacheUnsat = new TrieClause();
		this.doNotUseOptimizations = doNotUseOptimizations;
		this.doNotUnwind = doNotUnwind;
	}
	
	@Override
	public boolean querySat(SemConfiguration J) {
		var P = J.syProgramLit();
		var pcs = possiblyUnwindPathCondition(J.pathCondition());
		for (var pc : pcs) {
			var sat = surelyUnsat(pc) ? false : this.smtSolverPlain.querySat(P, pc);
			if (sat) {
				return true;
			} else {
				cache(pc);
			}
		}
		
		return false;
	}
	
	@Override
	public String getModel(SemConfiguration J) {
		return this.smtSolverPlain.getModel(J);
	}
	
	@Override
	public long totalSolverTimeMillis() {
		return this.smtSolverPlain.totalSolverTimeMillis();
	}
	
	@Override
	public long totalNumberOfQueries() {
		return this.smtSolverPlain.totalNumberOfQueries();
	}

	@Override
	public long totalNumberOfQueriesSat() {
		return this.smtSolverPlain.totalNumberOfQueriesSat();
	}
	
	@Override
	public long totalModelTimeMillis() {
		return this.smtSolverPlain.totalModelTimeMillis();
	}
	
	@Override
	public void quit() {
		this.smtSolverPlain.quit();
	}
	
	private Iterable<List<SyValue>> possiblyUnwindPathCondition(List<SyValue> pathCondition) {
		final Iterable<List<SyValue>> retVal = possiblyUnwindPathConditionBDD(pathCondition);
		return retVal;
	}
	
	private static class PathConditionScanner {
		private final BDD bdd;
		private final ArrayList<SyValue> atomicPredicates;
		private final ArrayList<SyValue> atomicPredicatesNegated;
		private final HashMap<SyValue, Integer> atomicPredicatesInverse;
		private int p;
		
		PathConditionScanner() {
			this.bdd = new BDD(1000, 1000);
			this.atomicPredicates = new ArrayList<>();
			this.atomicPredicatesNegated = new ArrayList<>();
			this.atomicPredicatesInverse = new HashMap<>();
			this.p = this.bdd.getOne();
		}
		
		void conjoinPredicate(SyValue sigma) {
			final int pSigma = convertPredicate(sigma);
			if (this.p != this.bdd.getOne()) {
				this.bdd.deref(this.p);
			}
			this.bdd.deref(pSigma);
			this.p = this.bdd.and(this.p, pSigma);
			this.bdd.ref(this.p);
		}
		
		int convertPredicate(SyValue sigma) {
			if (sigma instanceof SyValueIte sigmaIte) {
				var argCond = sigmaIte.syValueCond();
				var argThen = sigmaIte.syValueThen();
				var argElse = sigmaIte.syValueElse();
				int pCond = convertPredicate(argCond);
				int pThen = convertPredicate(argThen);
				int pElse = convertPredicate(argElse);
				this.bdd.deref(pCond);
				this.bdd.deref(pThen);
				this.bdd.deref(pElse);
				int p = this.bdd.ite(pCond, pThen, pElse);
				this.bdd.ref(p);
				return p;
			} else if (sigma instanceof SyValueNot sigmaNot) {
				var arg1 = sigmaNot.syValue();
				int p1 = convertPredicate(arg1);
				this.bdd.deref(p1);
				int p = this.bdd.not(p1);
				this.bdd.ref(p);
				return p;
			} else if (sigma instanceof SyValueAnd sigmaAnd) {
				var arg1 = sigmaAnd.syValueFirst();
				var arg2 = sigmaAnd.syValueSecond();
				int p1 = convertPredicate(arg1);
				int p2 = convertPredicate(arg2);
				this.bdd.deref(p1);
				this.bdd.deref(p2);
				int p = this.bdd.and(p1, p2);
				this.bdd.ref(p);
				return p;
			} else if (sigma instanceof SyValueOr sigmaOr) {
				var arg1 = sigmaOr.syValueFirst();
				var arg2 = sigmaOr.syValueSecond();
				int p1 = convertPredicate(arg1);
				int p2 = convertPredicate(arg2);
				this.bdd.deref(p1);
				this.bdd.deref(p2);
				int p = this.bdd.or(p1, p2);
				this.bdd.ref(p);
				return p;
			} else {
				final int v;
				if (this.atomicPredicatesInverse.containsKey(sigma)) {
					v = this.atomicPredicatesInverse.get(sigma);
				} else {
					v = this.bdd.createVar();
					this.atomicPredicates.add(sigma);
					this.atomicPredicatesNegated.add(new SyValueNot(sigma));
					this.atomicPredicatesInverse.put(sigma, v);
				}
				return v;
			}
		}
		
		/**
		 * Converts a JDD solution to a DIMACS-compatible
		 * format which is more suitable for querying Z3. 
		 * 
		 * @param solJDD a solution as returned by JDD,
		 *        i.e., a {@code int[]} where the i-th member
		 *        represents the three-valued truth value (1 = true, 0 = 
		 *        false, other = don't care) of the i-th variable
		 *        in the bdd.
		 * @return a solution in DIMACS format, i.e., a {@code int[]} 
		 *         whose members have value either k or -k if 
		 *         the k-th variable has, respectively, true or 
		 *         false value. Variables whose truth value 
		 *         is don't care are not added to the solution.
		 *         Variable count starts from 1.
		 */
		private int[] toDIMACS(int[] solJDD) {
			int size = solJDD.length;
			for (int i : solJDD) {
				if (i != 0 && i != 1) {
					--size;
				}
			}
			int[] retVal = new int[size];
			int var = 1;
			int pos = 0;
			for (int i = 0; i < solJDD.length; ++i) {
				if (solJDD[i] == 1) {
					retVal[pos] = var;
					++pos;
				} else if (solJDD[i] == 0) {
					retVal[pos] = -var;
					++pos;
				} //ignore DONTCARE
				++var;
			}
			return retVal;
		}

		Iterable<List<SyValue>> iterable() {
			return new Iterable<List<SyValue>>() {	
				
				@Override
				public Iterator<List<SyValue>> iterator() {
					return new Iterator<List<SyValue>>() {
						private final int bddFalse;
						private final int bddTrue;
						private int q;
						private int sol;
						{
							this.bddFalse = bdd.getZero();
							this.bddTrue = bdd.getOne();
							this.q = p;
							this.sol = bdd.oneSat(this.q);
							bdd.ref(this.sol);
						}
						
						@Override
						public boolean hasNext() {
							return (this.sol != this.bddFalse && this.sol != this.bddTrue);
						}
						
						@Override
						public List<SyValue> next() {
							final int[] solDIMACS = toDIMACS(bdd.oneSat(this.q, null));
							final List<SyValue> retVal = new ArrayList<>();
							for (int x : solDIMACS) {
								if (x > 0) {
									retVal.add(atomicPredicates.get(x - 1));
								} else {
									retVal.add(atomicPredicatesNegated.get((-x) - 1));
								}
							}
							final int qNew = bdd.and(this.q, bdd.not(this.sol));
							bdd.ref(qNew);
							bdd.deref(this.q);
							bdd.deref(this.sol);
							this.q = qNew;
							this.sol = bdd.oneSat(this.q);
							bdd.ref(this.sol);
							return retVal;
						}
					};
				}
			};
		}
	}
	
	private Iterable<List<SyValue>> possiblyUnwindPathConditionBDD(List<SyValue> pathCondition) {
		var pcConverted = convertItes(pathCondition);		
		var pcs = new PathConditionScanner();
		for (var c : pcConverted) {
			pcs.conjoinPredicate(c);
		}
		if (this.doNotUnwind) {
			if (pcs.iterable().iterator().hasNext()) {
				return List.of(pathCondition);
			} else {
				return Collections.emptyList();
			}
		} else {
			return pcs.iterable();
		}
	}
	
	private List<SyValue> convertItes(List<SyValue> pc) {
		final ArrayList<SyValue> retVal = new ArrayList<>();
		for (var sigma : pc) {
			var sigmaNew = convertItes(sigma);
			retVal.add(sigmaNew);
		}
		return retVal;
	}
	
	private SyValue convertItes(SyValue sigma) {
		if (sigma instanceof SyValueIte sigmaIte) {
			var argCond = sigmaIte.syValueCond();
			var argThen = sigmaIte.syValueThen();
			var argElse = sigmaIte.syValueElse();
			var argCondNew = convertItes(argCond);
			var argThenNew = convertItes(argThen);
			var argElseNew = convertItes(argElse);
			return new SyValueIte(argCondNew, argThenNew, argElseNew);
		} else if (sigma instanceof SyValueNot sigmaNot) {
			var arg = sigmaNot.syValue();
			var argNew = convertItes(arg);
			return new SyValueNot(argNew);
		} else if (sigma instanceof SyValueAnd sigmaAnd) {
			var arg1 = sigmaAnd.syValueFirst();
			var arg2 = sigmaAnd.syValueSecond();
			var arg1New = convertItes(arg1);
			var arg2New = convertItes(arg2);
			return new SyValueAnd(arg1New, arg2New);
		} else if (sigma instanceof SyValueOr sigmaOr) {
			var arg1 = sigmaOr.syValueFirst();
			var arg2 = sigmaOr.syValueSecond();
			var arg1New = convertItes(arg1);
			var arg2New = convertItes(arg2);
			return new SyValueOr(arg1New, arg2New);
		} else if (sigma instanceof SyValueLt sigmaLt) {
			var arg1 = sigmaLt.syValueFirst();
			var arg2 = sigmaLt.syValueSecond();
			var arg1New = convertItes(arg1);
			var arg2New = convertItes(arg2);
			if (arg1New instanceof SyValueIte arg1NewIte) {
				var arg1NewCond = arg1NewIte.syValueCond();
				var arg1NewThen = arg1NewIte.syValueThen();
				var arg1NewElse = arg1NewIte.syValueElse();
				if (arg2New instanceof SyValueIte arg2NewIte) {
					//both are ite
					var arg2NewCond = arg2NewIte.syValueCond();
					var arg2NewThen = arg2NewIte.syValueThen();
					var arg2NewElse = arg2NewIte.syValueElse();
					var subIteThen = new SyValueIte(arg2NewCond, new SyValueLt(arg1NewThen, arg2NewThen),  new SyValueLt(arg1NewThen, arg2NewElse));
					var subIteElse = new SyValueIte(arg2NewCond, new SyValueLt(arg1NewElse, arg2NewThen),  new SyValueLt(arg1NewElse, arg2NewElse));
					return new SyValueIte(arg1NewCond, subIteThen, subIteElse);
				} else {
					//arg1New is an ite, arg2New is not
					return new SyValueIte(arg1NewCond, new SyValueLt(arg1NewThen, arg2New), new SyValueLt(arg1NewElse, arg2New));
				}
			} else if (arg2New instanceof SyValueIte arg2NewIte) {
				//arg2New is an ite, arg1New is not
				var arg2NewCond = arg2NewIte.syValueCond();
				var arg2NewThen = arg2NewIte.syValueThen();
				var arg2NewElse = arg2NewIte.syValueElse();
				return new SyValueIte(arg2NewCond, new SyValueLt(arg1New, arg2NewThen), new SyValueLt(arg1New, arg2NewElse));
			} else {
				//neither is an ite
				return new SyValueLt(arg1New, arg2New);
			}
		} else if (sigma instanceof SyValueEq sigmaEq) {
			var arg1 = sigmaEq.syValueFirst();
			var arg2 = sigmaEq.syValueSecond();
			var arg1New = convertItes(arg1);
			var arg2New = convertItes(arg2);
			if (arg1New instanceof SyValueIte arg1NewIte) {
				var arg1NewCond = arg1NewIte.syValueCond();
				var arg1NewThen = arg1NewIte.syValueThen();
				var arg1NewElse = arg1NewIte.syValueElse();
				if (arg2New instanceof SyValueIte arg2NewIte) {
					//both are ite
					var arg2NewCond = arg2NewIte.syValueCond();
					var arg2NewThen = arg2NewIte.syValueThen();
					var arg2NewElse = arg2NewIte.syValueElse();
					var subIteThen = new SyValueIte(arg2NewCond, new SyValueEq(arg1NewThen, arg2NewThen),  new SyValueEq(arg1NewThen, arg2NewElse));
					var subIteElse = new SyValueIte(arg2NewCond, new SyValueEq(arg1NewElse, arg2NewThen),  new SyValueEq(arg1NewElse, arg2NewElse));
					return new SyValueIte(arg1NewCond, subIteThen, subIteElse);
				} else {
					//arg1New is an ite, arg2New is not
					return new SyValueIte(arg1NewCond, new SyValueEq(arg1NewThen, arg2New), new SyValueEq(arg1NewElse, arg2New));
				}
			} else if (arg2New instanceof SyValueIte arg2NewIte) {
				//arg2New is an ite, arg1New is not
				var arg2NewCond = arg2NewIte.syValueCond();
				var arg2NewThen = arg2NewIte.syValueThen();
				var arg2NewElse = arg2NewIte.syValueElse();
				return new SyValueIte(arg2NewCond, new SyValueEq(arg1New, arg2NewThen), new SyValueEq(arg1New, arg2NewElse));
			} else {
				//neither is an ite
				return new SyValueEq(arg1New, arg2New);
			}
		} else if (sigma instanceof SyValueAdd sigmaAdd) {
			var arg1 = sigmaAdd.syValueFirst();
			var arg2 = sigmaAdd.syValueSecond();
			var arg1New = convertItes(arg1);
			var arg2New = convertItes(arg2);
			if (arg1New instanceof SyValueIte arg1NewIte) {
				var arg1NewCond = arg1NewIte.syValueCond();
				var arg1NewThen = arg1NewIte.syValueThen();
				var arg1NewElse = arg1NewIte.syValueElse();
				if (arg2New instanceof SyValueIte arg2NewIte) {
					//both are ite
					var arg2NewCond = arg2NewIte.syValueCond();
					var arg2NewThen = arg2NewIte.syValueThen();
					var arg2NewElse = arg2NewIte.syValueElse();
					var subIteThen = new SyValueIte(arg2NewCond, new SyValueAdd(arg1NewThen, arg2NewThen),  new SyValueAdd(arg1NewThen, arg2NewElse));
					var subIteElse = new SyValueIte(arg2NewCond, new SyValueAdd(arg1NewElse, arg2NewThen),  new SyValueAdd(arg1NewElse, arg2NewElse));
					return new SyValueIte(arg1NewCond, subIteThen, subIteElse);
				} else {
					//arg1New is an ite, arg2New is not
					return new SyValueIte(arg1NewCond, new SyValueAdd(arg1NewThen, arg2New), new SyValueAdd(arg1NewElse, arg2New));
				}
			} else if (arg2New instanceof SyValueIte arg2NewIte) {
				//arg2New is an ite, arg1New is not
				var arg2NewCond = arg2NewIte.syValueCond();
				var arg2NewThen = arg2NewIte.syValueThen();
				var arg2NewElse = arg2NewIte.syValueElse();
				return new SyValueIte(arg2NewCond, new SyValueAdd(arg1New, arg2NewThen), new SyValueAdd(arg1New, arg2NewElse));
			} else {
				//neither is an ite
				return new SyValueAdd(arg1New, arg2New);
			}
		} else if (sigma instanceof SyValueSub sigmaSub) {
			var arg1 = sigmaSub.syValueFirst();
			var arg2 = sigmaSub.syValueSecond();
			var arg1New = convertItes(arg1);
			var arg2New = convertItes(arg2);
			if (arg1New instanceof SyValueIte arg1NewIte) {
				var arg1NewCond = arg1NewIte.syValueCond();
				var arg1NewThen = arg1NewIte.syValueThen();
				var arg1NewElse = arg1NewIte.syValueElse();
				if (arg2New instanceof SyValueIte arg2NewIte) {
					//both are ite
					var arg2NewCond = arg2NewIte.syValueCond();
					var arg2NewThen = arg2NewIte.syValueThen();
					var arg2NewElse = arg2NewIte.syValueElse();
					var subIteThen = new SyValueIte(arg2NewCond, new SyValueSub(arg1NewThen, arg2NewThen),  new SyValueSub(arg1NewThen, arg2NewElse));
					var subIteElse = new SyValueIte(arg2NewCond, new SyValueSub(arg1NewElse, arg2NewThen),  new SyValueSub(arg1NewElse, arg2NewElse));
					return new SyValueIte(arg1NewCond, subIteThen, subIteElse);
				} else {
					//arg1New is an ite, arg2New is not
					return new SyValueIte(arg1NewCond, new SyValueSub(arg1NewThen, arg2New), new SyValueSub(arg1NewElse, arg2New));
				}
			} else if (arg2New instanceof SyValueIte arg2NewIte) {
				//arg2New is an ite, arg1New is not
				var arg2NewCond = arg2NewIte.syValueCond();
				var arg2NewThen = arg2NewIte.syValueThen();
				var arg2NewElse = arg2NewIte.syValueElse();
				return new SyValueIte(arg2NewCond, new SyValueSub(arg1New, arg2NewThen), new SyValueSub(arg1New, arg2NewElse));
			} else {
				//neither is an ite
				return new SyValueSub(arg1New, arg2New);
			}
		} else {
			return sigma;
		}
	}
	
	private boolean surelyUnsat(List<SyValue> pc) {
		if (this.doNotUseOptimizations) {
			return false;
		}
		if (cachedPrefix(pc)) {
			return true;
		}
		if (hasContradictoryAliasCondition(pc)) {
			return true;
		}
		return false;
	}
	
	private boolean cachedPrefix(List<SyValue> pc) {
		return this.cacheUnsat.containsPrefix(pc);
	}
	
	private void cache(List<SyValue> pc) {
		this.cacheUnsat.insert(pc);
	}
	
	private static record SymbolPair(SyReferenceConstantSymbol s1, SyReferenceConstantSymbol s2) { }
	
	private boolean hasContradictoryAliasCondition(List<SyValue> pc) {
		final Partition<SyReferenceConstantSymbol> equalities = new Partition<>();
		final HashSet<SymbolPair> inequalities = new HashSet<>();
		for (var sigma : pc) {
			if (hasContradictoryAliasCondition(sigma, equalities, inequalities)) {
				return true;
			}
		}
		return false;
	}
	
	private boolean hasContradictoryAliasCondition(SyValue sigma, Partition<SyReferenceConstantSymbol> equalities, HashSet<SymbolPair> inequalities) {
		if (sigma instanceof SyValueEq(SyValueReferenceConstant(SyReferenceConstantSymbol s1), SyValueReferenceConstant(SyReferenceConstantSymbol s2))) {
			if (inequalities.contains(new SymbolPair(s1, s2)) || inequalities.contains(new SymbolPair(s2, s1))) {
				return true;
			}
			equalities.union(s1, s2);
		} else if (sigma instanceof SyValueNot(SyValueEq(SyValueReferenceConstant(SyReferenceConstantSymbol s1), SyValueReferenceConstant(SyReferenceConstantSymbol s2)))) {
			if (equalities.find(s1).equals(equalities.find(s2))) {
				return true;
			}
			inequalities.add(new SymbolPair(s1, s2));
		} else if (sigma instanceof SyValueAnd(SyValue sigma1, SyValue sigma2)) {
			if (hasContradictoryAliasCondition(sigma1, equalities, inequalities) ||
				hasContradictoryAliasCondition(sigma2, equalities, inequalities)) {
				return true;
			}
		}
		return false;
	}
}
