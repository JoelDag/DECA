package analysis;

import analysis.fact.DataFlowFact;
import heros.FlowFunctions;
import heros.InterproceduralCFG;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootMethod;

public abstract class TaintAnalysisFlowFunctions implements FlowFunctions<Stmt, DataFlowFact, SootMethod> {
    protected InterproceduralCFG<Stmt, SootMethod> icfg;

    public void setICFG(InterproceduralCFG<Stmt, SootMethod> icfg) {
        this.icfg = icfg;
    }

    protected void prettyPrint(Stmt stmt, DataFlowFact fact) {
        // if(icfg.getMethodOf(stmt).toString().contains("doGet"))
        System.out.println("Method :" + icfg.getMethodOf(stmt) + ", Stmt(line:" + stmt.getPositionInfo().getStmtPosition().getFirstLine() + ") " + stmt + ", Fact: " + fact);
    }
}
