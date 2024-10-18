package jpose.smt;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import jpose.semantics.types.SemConfiguration;
import jpose.syntax.SyProgram;
import jpose.syntax.SyValue;

public final class SmtSolverPlain implements SmtSolver {
	private final Path solverPath;
	private final SmtPrinter smtPrinter;
	private Process solver;
	private BufferedReader solverReader;
	private BufferedWriter solverWriter;
	private long totalSolverTimeMillis;
	private long totalNumberOfQueries;
	private long totalNumberOfQueriesSat;
	private long totalModelTimeMillis;
	
	public SmtSolverPlain(Path solverPath) {
		this.solverPath = solverPath;
		this.smtPrinter = new SmtPrinter();
		runSolver();
		this.totalSolverTimeMillis = 0L;
		this.totalNumberOfQueries = 0L;
		this.totalNumberOfQueriesSat = 0L;
		this.totalModelTimeMillis = 0L;
	}
	
	@Override
	public boolean querySat(SemConfiguration J) {
		++this.totalNumberOfQueries;
		//System.out.print("*");
		var smtQuery = this.smtPrinter.configToSmt(J);
		sendToSolver(smtQuery);
		final long startMillis = System.currentTimeMillis();
		checkSat();
		var sat = readResultCheckSat();
		this.totalSolverTimeMillis += System.currentTimeMillis() - startMillis;
		if (sat) {
			++this.totalNumberOfQueriesSat;
		}
		return sat;
	}
	
	boolean querySat(SyProgram P, List<SyValue> pathCondition) {
		++this.totalNumberOfQueries;
		//System.out.print("*");
		var smtQuery = this.smtPrinter.pathConditionToSmt(P, pathCondition);
		sendToSolver(smtQuery);
		final long startMillis = System.currentTimeMillis();
		checkSat();
		var sat = readResultCheckSat();
		this.totalSolverTimeMillis += System.currentTimeMillis() - startMillis;
		if (sat) {
			++this.totalNumberOfQueriesSat;
		}
		return sat;
	}
	
	@Override
	public String getModel(SemConfiguration J) {
		var smtQuery = this.smtPrinter.configToSmt(J);
		sendToSolver(smtQuery);
		final long startMillis = System.currentTimeMillis();
		checkSat();
		var sat = readResultCheckSat();
		if (sat) {
			getModel();
			final String retVal = readResultGetModel();
			this.totalModelTimeMillis += System.currentTimeMillis() - startMillis;
			return retVal;
		} else {
			return null;
		}
	}
	
	@Override
	public long totalSolverTimeMillis() {
		return this.totalSolverTimeMillis;
	}
	
	@Override
	public long totalNumberOfQueries() {
		return this.totalNumberOfQueries;
	}
	
	@Override
	public long totalNumberOfQueriesSat() {
		return this.totalNumberOfQueriesSat;
	}
	
	@Override
	public long totalModelTimeMillis() {
		return this.totalModelTimeMillis;
	}
	
	private void runSolver() {
		final ArrayList<String> commandLine = new ArrayList<>();
		commandLine.add(this.solverPath.toString());
		commandLine.add("-smt2");
		commandLine.add("-in");
		final ProcessBuilder pb = new ProcessBuilder(commandLine).redirectErrorStream(true);
		try {
			this.solver = pb.start();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
		this.solverReader = new BufferedReader(new InputStreamReader(this.solver.getInputStream()));
		this.solverWriter = new BufferedWriter(new OutputStreamWriter(this.solver.getOutputStream()));
	}
	
	private void sendToSolver(String smtQuery) {
		try {
			this.solverWriter.write("(reset)\n");
			this.solverWriter.write(smtQuery);
			this.solverWriter.flush();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}
	
	private void checkSat() {
		try {
			this.solverWriter.write("(check-sat)\n");
			this.solverWriter.flush();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}
	
	private void getModel() {
		try {
			this.solverWriter.write("(get-model)\n");
			this.solverWriter.flush();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}
	
	private boolean readResultCheckSat() {
		final String answer;
		try {
			answer = this.solverReader.readLine().trim();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
		if ("unsat".equals(answer)) {
			return false;
		} else if ("sat".equals(answer)) {
			return true;
		} else {
			throw new RuntimeException("Unrecognized answer from smt solver: " + answer);
		}
	}
	
	private String readResultGetModel() {
        //answer can be multiline, we count parentheses to
        //determine when the answer is over
        final StringBuilder retVal = new StringBuilder();
        int nestingLevel = 0;
        do {
        	final String answer;
    		try {
    			answer = this.solverReader.readLine();
    		} catch (IOException e) {
    			throw new RuntimeException(e);
    		}
            retVal.append(answer);
            retVal.append('\n');
            for (char c : answer.toCharArray()) {
                if (c == '(') {
                    ++nestingLevel;
                } else if (c == ')') {
                    --nestingLevel;
                }
            }
        } while (nestingLevel > 0);
        return retVal.toString();
	}
	
	@Override
	public void quit() {
		try {
			this.solverWriter.write("(exit)\n");
			this.solverWriter.flush();
			while (this.solverReader.readLine() != null) {
				//do nothing
			}
			this.solverReader.close();
			this.solverWriter.close();
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
		
		try {
			this.solver.waitFor();
		} catch (InterruptedException e) {
			//do nothing
		}
	}
}
