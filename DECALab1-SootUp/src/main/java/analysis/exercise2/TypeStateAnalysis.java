package analysis.exercise2;

import analysis.FileStateFact;
import analysis.ForwardAnalysis;
import analysis.VulnerabilityReporter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import sootup.core.jimple.basic.Local;
import sootup.core.jimple.basic.Value;
import sootup.core.jimple.common.expr.AbstractInvokeExpr;
import sootup.core.jimple.common.expr.JSpecialInvokeExpr;
import sootup.core.jimple.common.expr.JVirtualInvokeExpr;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.jimple.common.stmt.JInvokeStmt;
import sootup.core.jimple.common.stmt.JReturnVoidStmt;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.signatures.MethodSignature;
import sootup.java.core.JavaSootMethod;

import javax.annotation.Nonnull;

public class TypeStateAnalysis extends ForwardAnalysis<Set<FileStateFact>> {

	public TypeStateAnalysis(@Nonnull JavaSootMethod method, @Nonnull VulnerabilityReporter reporter) {
		super(method, reporter);
	    // System.out.println(method.getBody());
	}

	@Override
	protected void flowThrough(@Nonnull Set<FileStateFact> in, @Nonnull Stmt stmt, @Nonnull Set<FileStateFact> out) {
		copy(in, out);
		// TODO: Implement your flow function here.
		// MethodSignature currentMethodSig = method.getSignature();
		// this.reporter.reportVulnerability(currentMethodSig, stmt);
		prettyPrint(in, stmt, out);

	}

	@Nonnull
	@Override
	protected Set<FileStateFact> newInitialFlow() {
		// TODO: Implement your initialization here.
		// The following line may be just a place holder, check for yourself if
		// it needs some adjustments.
		return new HashSet<>();
	}

	@Override
	protected void copy(@Nonnull Set<FileStateFact> source, @Nonnull Set<FileStateFact> dest) {
		// TODO: Implement the copy function here.
		for (FileStateFact fsf : source) {
			dest.add(new FileStateFact(fsf));
		}
	}

	@Override
	protected void merge(@Nonnull Set<FileStateFact> in1, @Nonnull Set<FileStateFact> in2, @Nonnull Set<FileStateFact> out) {
		// TODO: Implement the merge function here.
	}

}
