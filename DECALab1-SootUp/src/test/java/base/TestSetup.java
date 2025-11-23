package base;

import analysis.FileStateFact;
import analysis.VulnerabilityReporter;
import java.io.File;
import java.util.*;

import analysis.exercise1.MisuseAnalysis;
import analysis.exercise2.TypeStateAnalysis;
import org.junit.Before;
import sootup.core.inputlocation.AnalysisInputLocation;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootMethod;
import sootup.core.transform.BodyInterceptor;
import sootup.core.types.ClassType;
import sootup.java.bytecode.inputlocation.JavaClassPathAnalysisInputLocation;
import sootup.java.core.JavaSootClass;
import sootup.java.core.JavaSootMethod;
import sootup.java.core.language.JavaLanguage;
import sootup.java.core.views.JavaView;

import javax.annotation.Nonnull;

public abstract class TestSetup {

    protected JavaView view;
    protected static VulnerabilityReporter reporter;

    @Before
    final public void setUp() {

        String classPath = System.getProperty("user.dir") + File.separator + "target" + File.separator + "test-classes";
        AnalysisInputLocation inputLocation = new JavaClassPathAnalysisInputLocation(classPath);
        view = new JavaView(inputLocation);

    }

    public final void executeMisuseAnalysis(Class<?> clazz) {

        final ClassType classType = view.getIdentifierFactory().getClassType(clazz.getName());

        final Optional<JavaSootClass> classOpt = view.getClass(classType);
        if(!classOpt.isPresent()){
            throw new IllegalArgumentException( classType + " not found.");
        }

        // iterate over all methods in that class
        for (JavaSootMethod method : classOpt.get().getMethods()) {
            // System.out.println(method.getBody());
            MisuseAnalysis analysis = new MisuseAnalysis( method, reporter);
            analysis.execute();
        }

    }

    final protected Map<SootMethod, Map<Stmt, Set<FileStateFact>>> executeTypestateAnalysis(Class<?> clazz) {

        Map<SootMethod, Map<Stmt, Set<FileStateFact>>> outFacts = new HashMap<>();
        final ClassType classType = view.getIdentifierFactory().getClassType(clazz.getName());

        final Optional<JavaSootClass> classOpt = view.getClass(classType);
        if(!classOpt.isPresent()){
            throw new IllegalArgumentException( classType + " not found.");
        }

        // iterate over all methods in that class
        for (JavaSootMethod method : classOpt.get().getMethods()) {
            // System.out.println(method.getBody());
            TypeStateAnalysis analysis = new TypeStateAnalysis(method, reporter);
            analysis.execute();
            outFacts.put( method, analysis.getStmtToAfterFlow());
        }

        return outFacts;
    }


}

