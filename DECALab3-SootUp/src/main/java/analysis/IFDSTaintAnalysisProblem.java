package analysis;

import analysis.fact.DataFlowFact;
import com.google.common.collect.Maps;
import heros.InterproceduralCFG;
import sootup.analysis.interprocedural.ifds.DefaultJimpleIFDSTabulationProblem;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootMethod;
import sootup.core.signatures.MethodSignature;
import sootup.core.views.View;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class IFDSTaintAnalysisProblem extends DefaultJimpleIFDSTabulationProblem<DataFlowFact, InterproceduralCFG<Stmt, SootMethod>> {

    private final TaintAnalysisFlowFunctions flowFunctions;

    private final List<MethodSignature> entryPoints;

    protected final View view;

    public IFDSTaintAnalysisProblem(InterproceduralCFG<Stmt, SootMethod> icfg, TaintAnalysisFlowFunctions flowFunctions, List<MethodSignature> entryPoints, View view) {
        super(icfg);
        this.flowFunctions = flowFunctions;
        this.entryPoints = entryPoints;
        this.view = view;
    }

    @Override
    public Map<Stmt, Set<DataFlowFact>> initialSeeds() {
        Map<Stmt, Set<DataFlowFact>> res = Maps.newHashMap();

        for (MethodSignature methodSignature : entryPoints) {
            SootMethod m = view.getMethod(methodSignature).get();
            if (!m.hasBody()) {
                continue;
            }
            if (m.getName().equals("doGet")) {
                res.put(m.getBody().getStmtGraph().getStartingStmt(), Collections.singleton(zeroValue()));
            }
        }
        return res;
    }

    @Override
    protected TaintAnalysisFlowFunctions createFlowFunctionsFactory() {
        return flowFunctions;
    }

    @Override
    protected DataFlowFact createZeroValue() {
        return DataFlowFact.getZeroInstance();
    }

    @Override
    public boolean autoAddZero() {
        return true;
    }
}
