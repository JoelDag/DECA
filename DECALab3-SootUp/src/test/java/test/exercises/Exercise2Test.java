package test.exercises;

import analysis.VulnerabilityReporter;
import analysis.exercise.Exercise2FlowFunctions;
import org.junit.Before;
import org.junit.Test;
import target.exercise1.AssignmentSQLInjection;
import target.exercise1.DirectSQLInjection;
import target.exercise1.InterproceduralSQLInjection;
import target.exercise1.NoSQLInjection;
import target.exercise2and3.FieldNoSQLInjection;
import target.exercise2and3.FieldSQLInjection1;
import target.exercise2and3.FieldSQLInjection2;
import test.base.TestSetup;

import static org.junit.Assert.assertEquals;

public class Exercise2Test extends TestSetup {

    @Before
    public void setup() {
        reporter = new VulnerabilityReporter();
        flowFunctions = new Exercise2FlowFunctions(reporter);
    }

    @Test
    public void fieldSQLInjection1() {
        executeStaticAnalysis(FieldSQLInjection1.class.getName());

        //FIELDBASED represents a
        assertContainsDataFlowFactAtStmt("FIELDBASED <target.exercise2and3.FieldSQLInjection1$ObjectWithTaint: java.lang.String userInput>", "conn#0 = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");
        assertContainsDataFlowFactAtStmt("loaded", "conn#0 = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");
        assertEquals(1, reporter.getReportedVulnerabilities());
    }

    @Test
    public void fieldSQLInjection2() {
        executeStaticAnalysis(FieldSQLInjection2.class.getName());

        assertContainsDataFlowFactAtStmt("FIELDBASED <target.exercise2and3.FieldSQLInjection2$ObjectWithTaint: java.lang.String userInput>", "conn#0 = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");
        assertContainsDataFlowFactAtStmt("loaded", "conn#0 = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");
        assertEquals(1, reporter.getReportedVulnerabilities());
    }

    @Test
    public void fieldBasedImpreciseTest() {
        executeStaticAnalysis(FieldNoSQLInjection.class.getName());

        assertContainsDataFlowFactAtStmt("FIELDBASED <target.exercise2and3.FieldNoSQLInjection$ObjectWithTaint: java.lang.String userInput>", "specialinvoke this.<target.exercise2and3.FieldNoSQLInjection: void createQuery(target.exercise2and3.FieldNoSQLInjection$ObjectWithTaint)>($stack6)");
        assertContainsDataFlowFactAtStmt("FIELDBASED <target.exercise2and3.FieldNoSQLInjection$ObjectWithTaint: java.lang.String userInput>", "conn#0 = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");

        //This is an imprecise propagation
        assertContainsDataFlowFactAtStmt("loaded", "conn#0 = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");
        assertEquals(1, reporter.getReportedVulnerabilities());
    }


    // The analysis must still correctly detect the data flows from Exercise 1.
    @Test
    public void directSQLInjection() {
        executeStaticAnalysis(DirectSQLInjection.class.getName());

        //Checks that the return variable "userId" of the call to getParameter is tainted.
        assertContainsDataFlowFactAtStmt("userId#0", "conn = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");

        assertContainsDataFlowFactAtStmt("query", "interfaceinvoke st.<java.sql.Statement: java.sql.ResultSet executeQuery(java.lang.String)>(query)");
        assertEquals(1, reporter.getReportedVulnerabilities());
    }

    @Test
    public void assignmentSQLInjection() {
        executeStaticAnalysis(AssignmentSQLInjection.class.getName());

        //Checks that the variable "alias" receives the taint as of the statement String alias = userId;
        assertContainsDataFlowFactAtStmt("alias", "conn#0 = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");

        assertContainsDataFlowFactAtStmt("query", "interfaceinvoke st.<java.sql.Statement: java.sql.ResultSet executeQuery(java.lang.String)>(query)");
        assertEquals(1, reporter.getReportedVulnerabilities());
    }

    @Test
    public void noSQLInjection() {
        executeStaticAnalysis(NoSQLInjection.class.getName());
        assertEquals(0, reporter.getReportedVulnerabilities());
    }

    @Test
    public void interproceduralSQLInjection() {
        executeStaticAnalysis(InterproceduralSQLInjection.class.getName());

        assertContainsDataFlowFactAtStmt("userId", "specialinvoke this.<target.exercise1.InterproceduralSQLInjection: void createQuery(java.lang.String)>(userId)");
        assertContainsDataFlowFactAtStmt("parameter", "conn#0 = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");

        assertEquals(1, reporter.getReportedVulnerabilities());
    }
}
