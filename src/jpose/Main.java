package jpose;

import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;

import jpose.parser.ParseResult;
import jpose.parser.ParserProgram;
import jpose.prettyprinter.PrettyPrinter;
import jpose.semantics.interpreter.Interpreter;
import jpose.semantics.types.SemConfiguration;
import jpose.smt.SmtPrinter;
import jpose.smt.SmtSolver;
import jpose.smt.SmtSolverUnwind;
import jpose.syntax.SyProgram;

public final class Main {
	private static enum ToPrint { CONFIGS, COUNT, MODELS, SMT, STATS }
	
	private static String filenameSrc = "";
	private static String z3 = "/usr/local/bin/z3";
	private static SmtSolver z3Solver = null;

	public static void main(String[] args) {
		int depth = 0;
		boolean prune = false;
		boolean leaves = false;
		ToPrint toPrint = ToPrint.CONFIGS;
		boolean nextZ3 = false;
		boolean nextDepth = false;
		boolean help = false;
		boolean unwind = false;
		
		for (int i = 0; i < args.length; ++i) {
			if (nextZ3) {
				z3 = args[i];
				nextZ3 = false;
			} else if (nextDepth) {
				depth = Integer.parseInt(args[i]);
				nextDepth = false;
			} else if ("-z3".equals(args[i])) {
				nextZ3 = true;
			} else if ("-c".equals(args[i])) {
				toPrint = ToPrint.COUNT;
			} else if ("-m".equals(args[i])) {
				toPrint = ToPrint.MODELS;
			} else if ("-s".equals(args[i])) {
				toPrint = ToPrint.SMT;
			} else if ("-t".equals(args[i])) {
				toPrint = ToPrint.STATS;
			} else if ("-p".equals(args[i])) {
				prune = true;
			} else if ("-l".equals(args[i])) {
				leaves = true;
			} else if ("-u".equals(args[i])) {
				unwind = true;
			} else if ("-h".equals(args[i])) {
				help = true;
			} else {
				filenameSrc = args[i];
				nextDepth = true;
			}
		}
		
		if (help) {
			System.out.println("Usage: java -jar <pose_jar> [-c|-s|-m|-t] [-l] [-p] [-z <z3_path>] [-u] source depth");
			System.out.println("  -c: prints count of configs");
			System.out.println("  -s: prints smtlib of path condition");
			System.out.println("  -m: prints model of (satisfiable) path condition");
			System.out.println("  -t: prints time statistics of Z3 queries; if -l is active");
			System.out.println("      prints time statistics of model generation");
			System.out.println("  -l: considers leaves instead of configs at depth");
			System.out.println("  -p: prunes infeasible with Z3");
			System.out.println("  -z <z3_path>: specifies the path of the Z3 executable (default: /usr/local/bin/z3)");		
			System.out.println("  -u: unwinds ites");
		} else {
			if (prune) {
				z3Solver = new SmtSolverUnwind(Paths.get(z3), true, !unwind);
			}
			if (leaves) {
				switch (toPrint) {
				case CONFIGS: 
					leavesConfigsAt(depth);
					break;
				case COUNT:
					leavesCountAt(depth);
					break;
				case MODELS:
					leavesModelsAt(depth);
					break;
				case SMT:
					leavesSmtAt(depth);
					break;
				case STATS:
					leavesStatsAt(depth);
					break;
				}
			} else {
				switch (toPrint) {
				case CONFIGS: 
					configsAt(depth);
					break;
				case COUNT:
					countAt(depth);
					break;
				case MODELS:
					modelsAt(depth);
					break;
				case SMT:
					smtAt(depth);
					break;
				case STATS:
					statsAt(depth);
					break;
				}
			}
			if (prune) {
				z3Solver.quit();
			}
		}
	}

	private static ParseResult<SyProgram> readAndParseFile() {
		String src;
		try {
			src = Files.readString(Path.of(filenameSrc));
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
		if (src.startsWith("include")) {
			final String filenameInclude = src.substring(8, src.indexOf('\n'));
			try {
				src = Files.readString(Path.of(filenameInclude)) + src.substring(src.indexOf('\n') + 1);
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		}
		final ParserProgram p = new ParserProgram();
		return p.parse(src);
	}
	
	private static void leavesConfigsAt(int depth) {
		final ParseResult<SyProgram> r = readAndParseFile();
		if (r.parsed().isPresent()) {
			final SyProgram prg = r.parsed().get();
			final Interpreter intp = new Interpreter();
			final List<SemConfiguration> Js;
			Js = intp.leavesAtPrune(prg, depth, z3Solver);
			final PrettyPrinter pp = new PrettyPrinter();
			for (var J : Js) {
				System.out.println(pp.configToString(J));
				System.out.println("\n=========\n");
			}
		} else {
			System.out.println("parsing error");
		}
	}
	
	private static void leavesCountAt(int depth) {
		final ParseResult<SyProgram> r = readAndParseFile();
		if (r.parsed().isPresent()) {
			final SyProgram prg = r.parsed().get();
			final Interpreter intp = new Interpreter();
			final List<SemConfiguration> Js;
			Js = intp.leavesAtPrune(prg, depth, z3Solver);
			System.out.println(Js.size());
		} else {
			System.out.println("parsing error");
		}
	}
	
	private static void leavesModelsAt(int depth) {
		final ParseResult<SyProgram> r = readAndParseFile();
		if (r.parsed().isPresent()) {
			final SyProgram prg = r.parsed().get();
			final Interpreter intp = new Interpreter();
			final List<SemConfiguration> Js;
			Js = intp.leavesAtPrune(prg, depth, z3Solver);
			for (var J : Js) {
				System.out.println(z3Solver.getModel(J));
				System.out.println("\n=========\n");
			}
		} else {
			System.out.println("parsing error");
		}
	}
	
	private static void leavesSmtAt(int depth) {
		final ParseResult<SyProgram> r = readAndParseFile();
		if (r.parsed().isPresent()) {
			final SyProgram prg = r.parsed().get();
			final Interpreter intp = new Interpreter();
			final List<SemConfiguration> Js;
			Js = intp.leavesAtPrune(prg, depth, z3Solver);
			final SmtPrinter smtp = new SmtPrinter();
			for (var J : Js) {
				System.out.println(smtp.configToSmt(J));
				System.out.println("\n=========\n");
			}
		} else {
			System.out.println("parsing error");
		}
	}
	
	private static void leavesStatsAt(int depth) {
		final ParseResult<SyProgram> r = readAndParseFile();
		if (r.parsed().isPresent()) {
			final SyProgram prg = r.parsed().get();
			final Interpreter intp = new Interpreter();
			final List<SemConfiguration> Js;
			Js = intp.leavesAtPrune(prg, depth, z3Solver);
			long emitTimeMillisFile = 0L;
            final Path filePath;
			try {
				filePath = Files.createTempFile("dummy", ".txt");
			} catch (IOException e) {
                throw new RuntimeException(e);
			}
            try (final BufferedWriter w = Files.newBufferedWriter(filePath)) {
				for (var J : Js) {
					String model = z3Solver.getModel(J);
					long startMillis = System.currentTimeMillis();
		            w.write(model); w.flush();
					emitTimeMillisFile += System.currentTimeMillis() - startMillis;
				}
				printLeavesStats(emitTimeMillisFile);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
		} else {
			System.out.println("parsing error");
		}
	}
	
	private static void configsAt(int depth) {
		final ParseResult<SyProgram> r = readAndParseFile();
		if (r.parsed().isPresent()) {
			final SyProgram prg = r.parsed().get();
			final Interpreter intp = new Interpreter();
			final List<SemConfiguration> Js;
			Js = intp.stepAtPrune(prg, depth, z3Solver);
			final PrettyPrinter pp = new PrettyPrinter();
			for (var J : Js) {
				System.out.println(pp.configToString(J));
				System.out.println("\n=========\n");
			}
		} else {
			System.out.println("parsing error");
		}
	}
	
	private static void countAt(int depth) {
		final ParseResult<SyProgram> r = readAndParseFile();
		if (r.parsed().isPresent()) {
			final SyProgram prg = r.parsed().get();
			final Interpreter intp = new Interpreter();
			final List<SemConfiguration> Js;
			Js = intp.stepAtPrune(prg, depth, z3Solver);
			System.out.println(Js.size());
		} else {
			System.out.println("parsing error");
		}
	}
	
	private static void modelsAt(int depth) {
		final ParseResult<SyProgram> r = readAndParseFile();
		if (r.parsed().isPresent()) {
			final SyProgram prg = r.parsed().get();
			final Interpreter intp = new Interpreter();
			final List<SemConfiguration> Js;
			Js = intp.stepAtPrune(prg, depth, z3Solver);
			for (var J : Js) {
				System.out.println(z3Solver.getModel(J));
				System.out.println("\n=========\n");
			}
		} else {
			System.out.println("parsing error");
		}
	}
	
	private static void smtAt(int depth) {
		final ParseResult<SyProgram> r = readAndParseFile();
		if (r.parsed().isPresent()) {
			final SyProgram prg = r.parsed().get();
			final Interpreter intp = new Interpreter();
			final List<SemConfiguration> Js;
			Js = intp.stepAtPrune(prg, depth, z3Solver);
			final SmtPrinter smtp = new SmtPrinter();
			for (var J : Js) {
				System.out.println(smtp.configToSmt(J));
				System.out.println("\n=========\n");
			}
		} else {
			System.out.println("parsing error");
		}
	}
	
	private static void statsAt(int depth) {
		final ParseResult<SyProgram> r = readAndParseFile();
		if (r.parsed().isPresent()) {
			final SyProgram prg = r.parsed().get();
			final Interpreter intp = new Interpreter();
			intp.stepAtPrune(prg, depth, z3Solver);
			printStats();
		} else {
			System.out.println("parsing error");
		}
	}
	
	private static void printStats() {
		System.out.println("Spent " + (z3Solver == null ? 0L : z3Solver.totalSolverTimeMillis()) + " msec in " + (z3Solver == null ? 0L : z3Solver.totalNumberOfQueries()) + " Z3 queries, " + (z3Solver == null ? 0L : z3Solver.totalNumberOfQueriesSat()) + " Z3 sat queries");
	}
	
	private static void printLeavesStats(long emitTimeMillisFile) {
		System.out.println("Spent " + (z3Solver == null ? 0L : z3Solver.totalModelTimeMillis()) + " msec solving and " + emitTimeMillisFile + " emitting on file Z3 models");
	}
}
