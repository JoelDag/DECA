package analysis.exercise1;

import analysis.AbstractAnalysis;
import analysis.VulnerabilityReporter;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import sootup.core.jimple.basic.Value;
import sootup.core.jimple.common.constant.StringConstant;
import sootup.core.jimple.common.expr.AbstractInvokeExpr;
import sootup.core.jimple.common.expr.JStaticInvokeExpr;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootClass;
import sootup.core.model.SootMethod;
import sootup.core.signatures.MethodSignature;
import sootup.core.types.ClassType;
import sootup.java.core.JavaSootMethod;

public class MisuseAnalysis extends AbstractAnalysis{
	public MisuseAnalysis(@Nonnull JavaSootMethod method, @Nonnull VulnerabilityReporter reporter) {
		super(method, reporter);
	}

	@Override
	protected void flowThrough(@Nonnull Stmt stmt) {
		// TODO: Implement your analysis here.
	}


}
