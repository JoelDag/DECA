package exercises;

import static org.junit.Assert.assertEquals;

import analysis.VulnerabilityReporter;

import base.TestSetup;
import org.junit.Test;
import target.exercise1.Misuse;
import target.exercise1.NoMisuse;

public class Exercise1Test extends TestSetup {


	@Test
	public void testMisuse() {
		reporter = new VulnerabilityReporter();
		executeMisuseAnalysis(Misuse.class);
		assertEquals(1, reporter.getReportedVulnerabilities().size());
    assertEquals(
        "<target.exercise1.Misuse: void test()> - aesCipher = staticinvoke <javax.crypto.Cipher: javax.crypto.Cipher getInstance(java.lang.String)>(\"AES\")",
        reporter.getReportedVulnerabilities().get(0));
	}

	@Test
	public void testNoMisuse() {
		reporter = new VulnerabilityReporter();
		executeMisuseAnalysis(NoMisuse.class);
		assertEquals(0, reporter.getReportedVulnerabilities().size());
	}
	
}
