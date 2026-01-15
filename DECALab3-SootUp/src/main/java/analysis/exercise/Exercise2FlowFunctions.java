package analysis.exercise;

import analysis.TaintAnalysisFlowFunctions;
import analysis.VulnerabilityReporter;
import analysis.fact.DataFlowFact;
import com.google.common.collect.Sets;
import heros.FlowFunction;
import sootup.core.jimple.basic.Local;
import sootup.core.jimple.basic.Value;
import sootup.core.jimple.common.expr.AbstractInstanceInvokeExpr;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootMethod;

import java.util.Collections;
import java.util.Set;

public class Exercise2FlowFunctions extends TaintAnalysisFlowFunctions {

    private final VulnerabilityReporter reporter;

    public Exercise2FlowFunctions(VulnerabilityReporter reporter) {
        this.reporter = reporter;
    }

    @Override
    public FlowFunction<DataFlowFact> getCallFlowFunction(Stmt callSite, SootMethod callee) {
        return fact -> {
            if (fact == DataFlowFact.getZeroInstance()) {
                return Collections.emptySet();
            }

            prettyPrint(callSite, fact);
            Set<DataFlowFact> out = Sets.newHashSet();

            //TODO: Implement Exercise 1c) here
            //TODO: Implement interprocedural part of Exercise 2 here


            return out;
        };
    }

    public FlowFunction<DataFlowFact> getCallToReturnFlowFunction(final Stmt callSiteStmt, Stmt returnSite) {
        return val -> {

            Set<DataFlowFact> out = Sets.newHashSet();
            out.add(val);
            modelStringOperations(val, out, callSiteStmt);

            if (val == DataFlowFact.getZeroInstance()) {

                //TODO: Implement Exercise 1a) here

            }

            if (callSiteStmt.toString().contains("executeQuery")) {
                Value arg = callSiteStmt.getInvokeExpr().getArg(0);
                if (val.getVariable().equals(arg)) {
                    reporter.reportVulnerability();
                }
            }

            return out;
        };
    }

    private void modelStringOperations(DataFlowFact fact, Set<DataFlowFact> out,
                                       Stmt callSiteStmt) {
        Exercise3FlowFunctions.handleCallSite(fact, out, callSiteStmt);

        /*For any call x = var.toString(), if the base variable var is tainted, then x is tainted.*/
        if (callSiteStmt instanceof JAssignStmt && callSiteStmt.toString().contains("toString()")) {
            if (callSiteStmt.getInvokeExpr() instanceof AbstractInstanceInvokeExpr) {
                AbstractInstanceInvokeExpr instanceInvokeExpr = (AbstractInstanceInvokeExpr) callSiteStmt.getInvokeExpr();

                if (fact.getVariable().equals(instanceInvokeExpr.getBase())) {
                    Value leftOp = ((JAssignStmt) callSiteStmt).getLeftOp();
                    if (leftOp instanceof Local) {
                        out.add(new DataFlowFact((Local) leftOp));
                    }
                }

            }
        }
    }

    @Override
    public FlowFunction<DataFlowFact> getNormalFlowFunction(final Stmt curr, Stmt succ) {
        return fact -> {
            prettyPrint(curr, fact);
            Set<DataFlowFact> out = Sets.newHashSet();
            out.add(fact);

            //TODO: Implement Exercise 1b) here
            //TODO: Implement cases for field load and field store statement of Exercise 2) here

            return out;
        };
    }

    @Override
    public FlowFunction<DataFlowFact> getReturnFlowFunction(Stmt callSite, SootMethod callee, Stmt exitStmt, Stmt retSite) {
        return fact -> {
            prettyPrint(callSite, fact);
            return Collections.emptySet();
        };
    }

}
