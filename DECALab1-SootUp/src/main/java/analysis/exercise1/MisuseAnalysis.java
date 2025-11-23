package analysis.exercise1;

import analysis.AbstractAnalysis;
import analysis.VulnerabilityReporter;
import javax.annotation.Nonnull;
import sootup.core.jimple.basic.Value;
import sootup.core.jimple.common.constant.StringConstant;
import sootup.core.jimple.common.expr.AbstractInvokeExpr;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.jimple.common.stmt.JInvokeStmt;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.signatures.MethodSignature;
import sootup.core.types.ClassType;
import sootup.java.core.JavaSootMethod;

public class MisuseAnalysis extends AbstractAnalysis{
	public MisuseAnalysis(@Nonnull JavaSootMethod method, @Nonnull VulnerabilityReporter reporter) {
		super(method, reporter);
	}

	/**
	 * Some notes for me:
	 * Goal is to calls to Cipher.getInstance() where transofrmation string is not secure, meaning no "AES/GCM/PKCS5Padding"
	 * 
	 * @param stmt - this is the statement we are currently analyzing
	 */
	@Override
	protected void flowThrough(@Nonnull Stmt stmt) {
		// first check if there is any valid invoke, we care about
		AbstractInvokeExpr invokeExpr = extractInvokeExpr(stmt);
		if (invokeExpr == null) return;

		MethodSignature signature = invokeExpr.getMethodSignature();
		if (!isCipherGetInstance(signature)) return;

		if (invokeExpr.getArgCount() == 0) {
			reporter.reportVulnerability(method.getSignature(), stmt);
			return;
		}

		Value firstArg = invokeExpr.getArg(0);
		if (firstArg instanceof StringConstant && 
		    !"AES/GCM/PKCS5Padding".equals(((StringConstant) firstArg).getValue())) {
		    reporter.reportVulnerability(method.getSignature(), stmt);
		}
	}

	private AbstractInvokeExpr extractInvokeExpr(@Nonnull Stmt stmt) {
		if (stmt instanceof JInvokeStmt) {
			// for invokes like "staticinvoke <Cipher: ...>"
			return ((JInvokeStmt) stmt).getInvokeExpr();
		}
		if (stmt instanceof JAssignStmt) {
			// for cases like "tmp = staticinvoke ..."
			Value rightOp = ((JAssignStmt) stmt).getRightOp();
			if (rightOp instanceof AbstractInvokeExpr) {
				return (AbstractInvokeExpr) rightOp;
			}
		}
		return null;
	}

	private boolean isCipherGetInstance(@Nonnull MethodSignature signature) {
		ClassType declType = signature.getDeclClassType();
		return declType != null
				&& "javax.crypto.Cipher".equals(declType.getFullyQualifiedName())
				&& "getInstance".equals(signature.getName());
	}
}
