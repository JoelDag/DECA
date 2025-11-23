package analysis;

import java.util.Map;
import javax.annotation.Nonnull;
import sootup.analysis.intraprocedural.ForwardFlowAnalysis;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.java.core.JavaSootMethod;

public abstract class ForwardAnalysis<F> extends ForwardFlowAnalysis<F> {
	@Nonnull
	protected final VulnerabilityReporter reporter;
	@Nonnull
	protected final JavaSootMethod method;
		
	public ForwardAnalysis(@Nonnull JavaSootMethod method, @Nonnull VulnerabilityReporter reporter) {
		super(method.getBody().getStmtGraph());
		this.method = method;
		this.reporter = reporter;
		System.out.println("Method: "+method.getSignature());
	}

	protected void prettyPrint(@Nonnull F in, @Nonnull Stmt stmt, @Nonnull F out)
	{
		String s=String.format("\t%10s%s\n\t%10s%s\n\t%10s%s\n","In Fact: ", in, "Stmt: ", stmt, "Out Fact: ", out);
		System.out.println(s); 
	}

	public Map<Stmt,F> getStmtToAfterFlow()
	{
		return this.stmtToAfterFlow;
	}

	@Override
	abstract protected void flowThrough(@Nonnull F in, @Nonnull Stmt d, @Nonnull F out);

	@Nonnull
	@Override
	abstract protected F newInitialFlow();

	@Override
	abstract protected void merge(@Nonnull F in1, @Nonnull F in2, @Nonnull F out);

	@Override
	abstract protected void copy(@Nonnull F source, @Nonnull F dest);

	/**
	 * exists as a hint for the students how to run the analysis
	 * */
	@Override
	public void execute() {
		super.execute();
	}
}
