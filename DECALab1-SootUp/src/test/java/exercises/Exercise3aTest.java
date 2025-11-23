package exercises;

import static org.junit.Assert.assertEquals;


import org.junit.Test;

import analysis.VulnerabilityReporter;
import base.TestSetup;
import target.exercise3.BreakMisuseAnalysis;

public class Exercise3aTest extends TestSetup {


	@Test
	public void testBreakMisuseAnalysis() {
		reporter = new VulnerabilityReporter();
		executeMisuseAnalysis(BreakMisuseAnalysis.class);
		assertEquals(0, reporter.getReportedVulnerabilities().size());
	}
}
