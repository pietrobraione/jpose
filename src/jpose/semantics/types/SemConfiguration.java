package jpose.semantics.types;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.SequencedMap;

import jpose.syntax.SyExpression;
import jpose.syntax.SyLocLit;
import jpose.syntax.SyProgram;
import jpose.syntax.SyProgramLit;
import jpose.syntax.SyReferenceConstant;
import jpose.syntax.SyReferenceConstantLoc;
import jpose.syntax.SyReferenceConstantSymbol;
import jpose.syntax.SySymbol;
import jpose.syntax.SyValue;
import jpose.syntax.SyValueEq;
import jpose.syntax.SyValueIte;
import jpose.syntax.SyValueReferenceConstant;
import jpose.syntax.SyValueUnassumed;

public final class SemConfiguration {
	private final SyProgramLit syProgramLit;
	private LinkedHashMap<SyReferenceConstant, SemObject> heap;
	private ArrayList<SyValue> pathCondition;
	private boolean isPathConditionSurelySatisfiable;
	private boolean isAtBranch;
	private Optional<SemConfiguration> companion;
	private SyExpression syExpression;
	private int nextLocId;
	private String configurationId;
	
	public SemConfiguration(SyProgram syProgram) {
		switch (syProgram) {
			case SyProgramLit syProgramLit:
				this.syProgramLit = syProgramLit;
				break;
			default: throw new AssertionError();
		}
		this.heap = new LinkedHashMap<>();
		this.pathCondition = new ArrayList<>();
		this.isPathConditionSurelySatisfiable = true;
		this.isAtBranch = false;
		this.companion = Optional.empty();
		this.syExpression = this.syProgramLit.syExpression();
		this.nextLocId = 0;
		this.configurationId = "";
	}
	
	public SemConfiguration(SemConfiguration other) {
		this.syProgramLit = other.syProgramLit;
		this.heap = new LinkedHashMap<>();
		for (var e : other.heap.sequencedEntrySet()) {
			this.heap.put(e.getKey(), new SemObject(e.getValue()));
		}
		this.pathCondition = new ArrayList<>(other.pathCondition);
		this.isPathConditionSurelySatisfiable = other.isPathConditionSurelySatisfiable;
		this.isAtBranch = other.isAtBranch;
		this.companion = other.companion;
		this.syExpression = other.syExpression;
		this.nextLocId = other.nextLocId;
		this.configurationId = other.configurationId;
	}
	
	public SyProgramLit syProgramLit() {
		return this.syProgramLit;
	}
	
	public Optional<SemObject> objectAt(SyReferenceConstant syReferenceConstant) {
		Objects.requireNonNull(syReferenceConstant);
		
		return Optional.ofNullable(this.heap.get(syReferenceConstant));
	}
	
	public SyReferenceConstantLoc addObjectConcrete(SemObject semObject) {
		Objects.requireNonNull(semObject);
		
		var nextLoc = new SyReferenceConstantLoc(new SyLocLit(this.nextLocId++));
		this.heap.put(nextLoc, semObject);
		return nextLoc;
	}
	
	public void addObjectSymbolic(SySymbol sySymbol, SemObject semObject) {
		Objects.requireNonNull(sySymbol);
		Objects.requireNonNull(semObject);

		this.heap.put(new SyReferenceConstantSymbol(sySymbol), semObject);
	}
	
	public SequencedMap<SyReferenceConstant, SemObject> heap() {
		final LinkedHashMap<SyReferenceConstant, SemObject> heapNew = new LinkedHashMap<>();
		for (var e : this.heap.sequencedEntrySet()) {
			heapNew.put(e.getKey(), new SemObject(e.getValue()));
		}
		return Collections.unmodifiableSequencedMap(heapNew);
	}
	
	public void setHeap(SequencedMap<SyReferenceConstant, SemObject> heap) {
		Objects.requireNonNull(heap);
		
		this.heap = new LinkedHashMap<>();
		for (var e : heap.sequencedEntrySet()) {
			this.heap.put(e.getKey(), new SemObject(e.getValue()));
		}
	}
	
	public List<SyValue> pathCondition() {
		return Collections.unmodifiableList(new ArrayList<>(this.pathCondition));
	}
	
	public void setPathCondition(List<SyValue> pathCondition) {
		Objects.requireNonNull(pathCondition);
		this.pathCondition = new ArrayList<>(pathCondition);
		this.isPathConditionSurelySatisfiable = false;
	}
	
	public void addPathConditionClause(SyValue syValue) {
		Objects.requireNonNull(syValue);
		
		this.pathCondition.add(syValue);
		this.isPathConditionSurelySatisfiable = false;
	}
	
	public boolean isPathConditionSurelySatisfiable() {
		return this.isPathConditionSurelySatisfiable;
	}
	
	public void setPathConditionSurelySatisfiable() {
		this.isPathConditionSurelySatisfiable = true;
	}
	
	public boolean isAtBranch() {
		return this.isAtBranch;
	}
	
	public void setAtBranch() {
		this.isAtBranch = true;
	}
	
	public void resetAtBranch() {
		this.isAtBranch = false;
	}
	
	public Optional<SemConfiguration> companion() {
		return this.companion;
	}
	
	public void setCompanion(SemConfiguration companion) {
		Objects.requireNonNull(companion);
		this.companion = Optional.of(companion);
	}
	
	public void resetCompanion() {
		this.companion = Optional.empty();
	}
	
	public SyExpression syExpression() {
		return this.syExpression;
	}

	public void setSyExpression(SyExpression syExpression) {
		Objects.requireNonNull(syExpression);
		
		this.syExpression = syExpression;
	}
	
	public boolean unresolved(SySymbol sySymbol) {
		Objects.requireNonNull(sySymbol);
		
		return !this.heap.containsKey(new SyReferenceConstantSymbol(sySymbol));
	}

	public SyValue assume(SyReferenceConstantSymbol accessor, String fieldName, SyValue syValueFresh) {
		Objects.requireNonNull(accessor);
		Objects.requireNonNull(fieldName);
		Objects.requireNonNull(syValueFresh);
		
		SyValue retVal = syValueFresh;
		for (var e : this.heap.sequencedEntrySet()) {
			if (e.getKey() instanceof SyReferenceConstantSymbol syReferenceConstantSymbol &&
			    !accessor.sySymbol().equals(syReferenceConstantSymbol.sySymbol())) {
				var o = e.getValue();
				var v = o.get(fieldName);
				if (v.isPresent() && !(v.get() instanceof SyValueUnassumed)) {
					retVal = new SyValueIte(new SyValueEq(new SyValueReferenceConstant(new SyReferenceConstantSymbol(accessor.sySymbol())), new SyValueReferenceConstant(syReferenceConstantSymbol)), v.get(), retVal);
				}
			}
		}
		return retVal;
	}
	
	public void update(SyReferenceConstantSymbol accessor, String fieldName, SyValue syValueNew) {
		Objects.requireNonNull(accessor);
		Objects.requireNonNull(fieldName);
		Objects.requireNonNull(syValueNew);
		
		for (var e : this.heap.sequencedEntrySet()) {
			if (e.getKey() instanceof SyReferenceConstantSymbol syReferenceConstantSymbol &&
			    !accessor.sySymbol().equals(syReferenceConstantSymbol.sySymbol())) {
				var o = e.getValue();
				var v = o.get(fieldName);
				if (v.isPresent() && !(v.get() instanceof SyValueUnassumed)) {
					var syValueUpdate = new SyValueIte(new SyValueEq(new SyValueReferenceConstant(new SyReferenceConstantSymbol(accessor.sySymbol())), new SyValueReferenceConstant(syReferenceConstantSymbol)), syValueNew, v.get());
					o.upd(fieldName, syValueUpdate);
				}
			}
		}
	}
	
	public String configurationId() {
		return this.configurationId;
	}
	
	public void addConfigurationId(String toAdd) {
		Objects.requireNonNull(toAdd);
		
		this.configurationId += toAdd;
	}
}
