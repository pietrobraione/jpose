package jpose.smt;

import jpose.semantics.types.SemConfiguration;

public interface SmtSolver {
	default boolean filter(SemConfiguration J) {
		if (J.isPathConditionSurelySatisfiable() || !J.isAtBranch()) {
			return true;
		}
		var retVal = querySat(J);
		//System.out.print("'");
		if (retVal == true) {
			J.setPathConditionSurelySatisfiable();
		} else if (J.companion().isPresent()) {
			J.companion().get().setPathConditionSurelySatisfiable();
		}
		return retVal;
	}
	boolean querySat(SemConfiguration J);
	String getModel(SemConfiguration J);
	long totalSolverTimeMillis();
	long totalNumberOfQueries();
	long totalNumberOfQueriesSat();
	long totalModelTimeMillis();
	void quit();
}
