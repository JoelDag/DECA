package exercises;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import analysis.VulnerabilityReporter;
import base.TestSetup;
import target.exercise3.BreakTypeStateAnalysis;

public class Exercise3bTest extends TestSetup {
	@Test
	public void testTypeStateAnalysis() {
		reporter = new VulnerabilityReporter();
		executeTypestateAnalysis(BreakTypeStateAnalysis.class);
		assertEquals(0, reporter.getReportedVulnerabilities().size());
	}
}
