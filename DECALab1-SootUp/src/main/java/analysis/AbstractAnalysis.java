package analysis;


import javax.annotation.Nonnull;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.model.SootMethod;
import sootup.java.core.JavaSootMethod;

public abstract class AbstractAnalysis {

	@Nonnull protected VulnerabilityReporter reporter;
	@Nonnull protected SootMethod method;

	protected AbstractAnalysis(@Nonnull JavaSootMethod method, @Nonnull VulnerabilityReporter reporter) {
		this.reporter = reporter;
		this.method = method;
	}

	protected abstract void flowThrough(@Nonnull Stmt stmt);

	public void execute() {
		for (Stmt stmt : method.getBody().getStmts()) {
			flowThrough(stmt);
		}
	}
}
