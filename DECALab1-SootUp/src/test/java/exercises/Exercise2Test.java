package exercises;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import analysis.FileStateFact;
import analysis.VulnerabilityReporter;
import analysis.exercise2.TypeStateAnalysis;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import base.TestSetup;
import org.junit.Test;
import sootup.core.jimple.common.stmt.JReturnVoidStmt;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootMethod;
import sootup.core.types.ClassType;
import sootup.java.core.JavaSootClass;
import sootup.java.core.JavaSootMethod;
import target.exercise2.FileClosed;
import target.exercise2.FileClosedAliasing;
import target.exercise2.FileNotClosed;
import target.exercise2.FileNotClosedAliasing;

public class Exercise2Test extends TestSetup {

	@Test
	public void testFileClosed() {
		reporter = new VulnerabilityReporter();
    Map<SootMethod, Map<Stmt, Set<FileStateFact>>> outFacts =
        executeTypestateAnalysis(FileClosed.class);
		assertEquals(0, reporter.getReportedVulnerabilities().size());
		// test selected out facts
		for (SootMethod method : outFacts.keySet()) {
			if (method.getSignature().toString().equals("<target.exercise2.FileClosed: void test1()>")) {
				Map<Stmt, Set<FileStateFact>> result = outFacts.get(method);
				for (Stmt stmt : result.keySet()) {
					if (stmt.toString().equals("specialinvoke $r0.<target.exercise2.File: void <init>()>()")) {
						assertEquals("[([$r0], Init)]", result.get(stmt).toString());
					}
					if (stmt instanceof JReturnVoidStmt) {
						assertEquals("[([$stack2, file], Close)]", result.get(stmt).toString());
					}
				}
			}
			if (method.getSignature().toString().equals("<target.exercise2.FileClosed: void test2()>")) {
				Map<Stmt, Set<FileStateFact>> result = outFacts.get(method);
				for (Stmt stmt : result.keySet()) {
					if (stmt.toString().equals("virtualinvoke $r0.<target.exercise2.File: void open()>()")) {
						assertEquals("[([$r0], Open)]", result.get(stmt).toString());
					}
					if (stmt instanceof JReturnVoidStmt) {
						assertEquals("[([$stack2, file], Close)]", result.get(stmt).toString());
					}
				}
			}
		}
	}

	@Test
	public void testFileClosedAliasing() {
		reporter = new VulnerabilityReporter();
		Map<SootMethod, Map<Stmt, Set<FileStateFact>>> outFacts =
		executeTypestateAnalysis(FileClosedAliasing.class);
		assertEquals(0, reporter.getReportedVulnerabilities().size());
		int conditionalAssertionCases = 0;
		// test selected out facts
		for (SootMethod method : outFacts.keySet()) {
			if (method.getSignature().toString().equals("<target.exercise2.FileClosedAliasing: void test1()>")) {
				Map<Stmt, Set<FileStateFact>> result = outFacts.get(method);
				for (Stmt stmt : result.keySet()) {
					if (stmt.toString().equals("virtualinvoke $stack3.<target.exercise2.File: void open()>()")) {
						assertEquals("[([$stack3, file, alias], Open)]", result.get(stmt).toString());
						conditionalAssertionCases++;
					}
					if (stmt instanceof JReturnVoidStmt) {
						assertEquals("[([$stack3, file, alias], Close)]", result.get(stmt).toString());
						conditionalAssertionCases++;
					}
				}
			}
			if (method.getSignature().toString().equals("<target.exercise2.FileClosedAliasing: void test2()>")) {
				Map<Stmt, Set<FileStateFact>> result = outFacts.get(method);
				for (Stmt stmt : result.keySet()) {
					if (stmt.toString().equals("virtualinvoke $stack3.<target.exercise2.File: void open()>()")) {
						assertEquals(result.get(stmt).iterator().next().getState(), FileStateFact.FileState.Open);
						conditionalAssertionCases++;
					}
					if (stmt instanceof JReturnVoidStmt) {
						FileStateFact fact = result.get(stmt).iterator().next();
						assertEquals(fact.getState(), FileStateFact.FileState.Close);
						// assertTrue(fact.containsAlias("$r2"));
						conditionalAssertionCases++;
					}
				}
			}
		}
		assertEquals(4, conditionalAssertionCases);
	}

	@Test
	public void testFileNotClosed() {
		reporter = new VulnerabilityReporter();
		Map<SootMethod, Map<Stmt, Set<FileStateFact>>> outFacts =
		executeTypestateAnalysis(FileNotClosed.class);

		assertEquals(3, reporter.getReportedVulnerabilities().size());
		// test selected out facts
		for (SootMethod method : outFacts.keySet()) {
			if (method.getSignature().toString().equals("<target.exercise2.FileNotClosed: void test1()>")) {
				Map<Stmt, Set<FileStateFact>> result = outFacts.get(method);
				for (Stmt stmt : result.keySet()) {
					if (stmt instanceof JReturnVoidStmt) {
						assertEquals("[([$stack2, file], Open)]", result.get(stmt).toString());
					}
				}
			}
			if (method.getSignature().toString().equals("<target.exercise2.FileNotClosed: void test2()>")) {
				Map<Stmt, Set<FileStateFact>> result = outFacts.get(method);
				for (Stmt stmt : result.keySet()) {
					if (stmt instanceof JReturnVoidStmt) {
						boolean containsOpen = false;
						for (FileStateFact f : result.get(stmt)) {
							if (f.getState().equals(FileStateFact.FileState.Open)) {
                                containsOpen = true;
                                break;
                            }
						}
						assertTrue(containsOpen);
					}
				}
			}
			if (method.getSignature().toString().equals("<target.exercise2.FileNotClosed: void test3()>")) {
				Map<Stmt, Set<FileStateFact>> result = outFacts.get(method);
				for (Stmt stmt : result.keySet()) {
					if (stmt instanceof JReturnVoidStmt) {
						boolean containsOpen = false;
						for (FileStateFact f : result.get(stmt)) {
							if (f.getState().equals(FileStateFact.FileState.Open)) {
                                containsOpen = true;
								break;
                            }
						}
						assertTrue(containsOpen);
					}
				}
			}
		}
	}

	@Test
	public void testFileNotClosedAliasing() {
		reporter = new VulnerabilityReporter();
		Map<SootMethod, Map<Stmt, Set<FileStateFact>>> outFacts =
		executeTypestateAnalysis(FileNotClosedAliasing.class);
		assertEquals(4, reporter.getReportedVulnerabilities().size());
		// test selected out facts
		for (SootMethod method : outFacts.keySet()) {
			if (method.getSignature().toString().equals("<target.exercise2.FileNotClosedAliasing: void test2()>")) {
				Map<Stmt, Set<FileStateFact>> result = outFacts.get(method);
				for (Stmt stmt : result.keySet()) {
					if (stmt instanceof JReturnVoidStmt) {
						FileStateFact fact = result.get(stmt).iterator().next();
						assertTrue(fact.containsAlias("<target.exercise2.FileNotClosedAliasing: target.exercise2.File staticFile>"));
						assertEquals(fact.getState(), FileStateFact.FileState.Open);
					}
				}
			}
		}
	}

}
