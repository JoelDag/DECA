package test.base;

import analysis.IFDSTaintAnalysisProblem;
import analysis.TaintAnalysisFlowFunctions;
import analysis.VulnerabilityReporter;
import analysis.fact.DataFlowFact;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import heros.EdgeFunction;
import heros.InterproceduralCFG;
import sootup.analysis.interprocedural.icfg.JimpleBasedInterproceduralCFG;
import sootup.analysis.interprocedural.ifds.JimpleIFDSSolver;
import sootup.core.inputlocation.AnalysisInputLocation;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootClass;
import sootup.core.model.SootMethod;
import sootup.core.signatures.MethodSignature;
import sootup.core.types.ClassType;
import sootup.core.views.View;
import sootup.java.bytecode.inputlocation.JavaClassPathAnalysisInputLocation;
import sootup.java.core.views.JavaView;

import java.io.File;
import java.util.Collections;
import java.util.List;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Optional;

public abstract class TestSetup {

    protected final View view;
    protected VulnerabilityReporter reporter;
    protected TaintAnalysisFlowFunctions flowFunctions;
    protected final Multimap<Stmt, DataFlowFact> dataFlowFactsAtStmt = HashMultimap.create();

    protected TestSetup() {

        String classPath = System.getProperty("user.dir") + File.separator + "target" + File.separator + "test-classes";
        AnalysisInputLocation inputLocation = new JavaClassPathAnalysisInputLocation(classPath);
        view = new JavaView(inputLocation);

    }

    /*
     * Checks that the IFDS solver generates the dataflow fact "fact" at the statement "stmt".
     * For simplification, we test based on toString() representations of the objects.
     */
    protected void assertContainsDataFlowFactAtStmt(String fact, String stmt) {
        boolean foundStmt = false;
        for (Entry<Stmt, DataFlowFact> e : dataFlowFactsAtStmt.entries()) {
            final String stmtStr = e.getKey().toString();
            final String factStr = e.getValue().toString();
            if (stmtStr.equals(stmt)) {
                foundStmt = true;
                if (factStr.equals(fact)) {
                    return;
                }
            }
        }
        throw new NoSuchElementException("Analysis does not contain the fact '" + fact + "'.");
    }


    protected void executeStaticAnalysis(String targetTestClassName) {
        // We want to perform a whole program, i.e. an interprocedural analysis.
        // We construct a basic CHA call graph for the program
        final ClassType classType = view.getIdentifierFactory().getClassType(targetTestClassName);
        final Optional<?> aClass = view.getClass(classType);
        if (!aClass.isPresent()) {
            throw new IllegalArgumentException("Entrypoint class '" + classType + "' is not in the View.");
        }
        SootClass javaSootClass = (SootClass) aClass.get();

        final SootMethod entryPoint = javaSootClass.getMethods().stream().filter(SootMethod::hasBody).filter(ms -> ms.getSignature().getName().equals("doGet")).findAny().get();
        final List<MethodSignature> entryPoints = Collections.singletonList(entryPoint.getSignature());

        JimpleBasedInterproceduralCFG icfg = new JimpleBasedInterproceduralCFG(view, entryPoint.getSignature(), false, false);
        flowFunctions.setICFG(icfg);
        IFDSTaintAnalysisProblem problem = new IFDSTaintAnalysisProblem(icfg, flowFunctions, entryPoints, view);
        JimpleIFDSSolver<DataFlowFact, InterproceduralCFG<Stmt, SootMethod>> solver = new JimpleIFDSSolver<DataFlowFact, InterproceduralCFG<Stmt, SootMethod>>(problem) {
            @Override
            protected void propagate(DataFlowFact sourceFact, Stmt targetStmt, DataFlowFact targetFact,
                                     EdgeFunction<BinaryDomain> edgeFunc, Stmt relatedCallSite, boolean isUnbalancedReturn) {
                synchronized (dataFlowFactsAtStmt) {
                    dataFlowFactsAtStmt.put(targetStmt, targetFact);
                }
                super.propagate(sourceFact, targetStmt, targetFact, edgeFunc, targetStmt, isUnbalancedReturn);
            }
        };
        solver.solve();
    }

}
