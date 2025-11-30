package analysis.exercise2;

import analysis.FileStateFact;
import analysis.ForwardAnalysis;
import analysis.VulnerabilityReporter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import javax.annotation.Nonnull;
import sootup.core.jimple.basic.Value;
import sootup.core.jimple.common.expr.AbstractInvokeExpr;
import sootup.core.jimple.common.expr.JInterfaceInvokeExpr;
import sootup.core.jimple.common.expr.JNewExpr;
import sootup.core.jimple.common.expr.JSpecialInvokeExpr;
import sootup.core.jimple.common.expr.JVirtualInvokeExpr;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.jimple.common.stmt.JInvokeStmt;
import sootup.core.jimple.common.stmt.JReturnStmt;
import sootup.core.jimple.common.stmt.JReturnVoidStmt;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.java.core.JavaSootMethod;

public class TypeStateAnalysis extends ForwardAnalysis<Set<FileStateFact>> {

    public TypeStateAnalysis(@Nonnull JavaSootMethod method, @Nonnull VulnerabilityReporter reporter) {
        super(method, reporter);
    }

    @Override
    protected void flowThrough(@Nonnull Set<FileStateFact> in, @Nonnull Stmt stmt, @Nonnull Set<FileStateFact> out) {
        copy(in, out);
        Set<Value> allValues = getAllValuesInMethod();

        if (stmt instanceof JAssignStmt) {
            handlJAssign(out, (JAssignStmt) stmt, allValues);
        }

        AbstractInvokeExpr invokeExpr = extractInvokeExpr(stmt);
        if (invokeExpr != null) {
            handleInvocation(out, invokeExpr, allValues);   //update file state for all alisases of the base object
        }

        // report vulneraibilities when still open
        if (stmt instanceof JReturnStmt || stmt instanceof JReturnVoidStmt) {
            for (FileStateFact fact : out) {
                if (fact.getState() == FileStateFact.FileState.Open) {
                    reporter.reportVulnerability(method.getSignature(), stmt);
                }
            }
        }

        prettyPrint(in, stmt, out);
    }

    private void handlJAssign(Set<FileStateFact> facts, JAssignStmt stmt, Set<Value> allValues) {
        Value leftOp = stmt.getLeftOp();
        Value rightOp = stmt.getRightOp();
        removeAlias(leftOp, facts, stmt, allValues); // kill old aliases of left side operations

        if (rightOp instanceof JNewExpr && "target.exercise2.File".equals(((JNewExpr) rightOp).getType().toString())) {
            LinkedHashSet<Value> tmp = new LinkedHashSet<>();
            tmp.add(leftOp);
            Set<Value> aliases = orderAliases(tmp);
            facts.add(new FileStateFact(aliases, FileStateFact.FileState.Init));
            return;
        }

        if (rightOp instanceof AbstractInvokeExpr) return;

        //propaget the alias
        List<FileStateFact> updates = new ArrayList<>();
        Iterator<FileStateFact> it = facts.iterator();
        while (it.hasNext()) {
            FileStateFact fact = it.next();
            if (fact.containsAlias(rightOp)) {
                it.remove();
                updates.add(new FileStateFact(orderAliases(addAlias(collectAliases(fact, allValues), leftOp)), fact.getState()));
            }
        }
        facts.addAll(updates);
    }

    private void handleInvocation(Set<FileStateFact> facts, AbstractInvokeExpr expr, Set<Value> allValues) {
        if (!"target.exercise2.File".equals(expr.getMethodSignature().getDeclClassType().getFullyQualifiedName())) {
            return;
        }

        Value base = getBase(expr);
        if (base == null) return;

        String methodName = expr.getMethodSignature().getName();
        FileStateFact.FileState newState;
        if ("open".equals(methodName)) {
            newState = FileStateFact.FileState.Open;
        } else if ("close".equals(methodName)) {
            newState = FileStateFact.FileState.Close;
        } else {
            return;
        }

        List<FileStateFact> updates = new ArrayList<>();
        Iterator<FileStateFact> it = facts.iterator();
        while (it.hasNext()) {
            FileStateFact fact = it.next();
            if (fact.containsAlias(base)) {
                it.remove();
                updates.add(new FileStateFact(orderAliases(collectAliases(fact, allValues)), newState));
            }
        }
        facts.addAll(updates);
    }

    private void removeAlias(Value alias, Set<FileStateFact> facts, Stmt stmt, Set<Value> allValues) {
        List<FileStateFact> survivors = new ArrayList<>();
        Iterator<FileStateFact> it = facts.iterator();

        while (it.hasNext()) {
            FileStateFact fact = it.next();
            if (fact.containsAlias(alias)) {
                it.remove();

                LinkedHashSet<Value> remaining = new LinkedHashSet<>();
                for (Value v : collectAliases(fact, allValues)) {
                    if (!v.equivTo(alias)) {
                        remaining.add(v);
                    }
                }

                if (remaining.isEmpty()) {
                    if (fact.getState() == FileStateFact.FileState.Open) {
                        reporter.reportVulnerability(method.getSignature(), stmt);
                    }
                } else {
                    survivors.add(new FileStateFact(orderAliases(remaining), fact.getState()));
                }
            }
        }
        facts.addAll(survivors);
    }

    private AbstractInvokeExpr extractInvokeExpr(Stmt stmt) {
        if (stmt instanceof JInvokeStmt) {
            return ((JInvokeStmt) stmt).getInvokeExpr();
        }
        if (stmt instanceof JAssignStmt) {
            Value right = ((JAssignStmt) stmt).getRightOp();
            if (right instanceof AbstractInvokeExpr) {
                return (AbstractInvokeExpr) right;
            }
        }
        return null;
    }

    private LinkedHashSet<Value> orderAliases(Set<Value> aliases) {
        LinkedHashSet<Value> ordered = new LinkedHashSet<>();
        LinkedHashSet<Value> temps = new LinkedHashSet<>();
        LinkedHashSet<Value> locals = new LinkedHashSet<>();

        for (Value v : aliases) {
            String s = v.toString();
            if (s.startsWith("$") || s.startsWith("r")) temps.add(v);
            else locals.add(v);
        }

        ordered.addAll(temps);
        ordered.addAll(locals);
        return ordered;
    }


    private Value getBase(AbstractInvokeExpr expr) {
        if (expr instanceof JVirtualInvokeExpr) {
            return ((JVirtualInvokeExpr) expr).getBase();
        }
        if (expr instanceof JSpecialInvokeExpr) {
            return ((JSpecialInvokeExpr) expr).getBase();
        }
        if (expr instanceof JInterfaceInvokeExpr) {
            return ((JInterfaceInvokeExpr) expr).getBase();
        }
        return null;
    }

    private Set<Value> addAlias(Set<Value> existingAliases, Value alias) {
        LinkedHashSet<Value> updated = new LinkedHashSet<>();
        boolean alreadyPresent = false;
        for (Value value : existingAliases) {
            updated.add(value);
            if (value.equivTo(alias)) {
                alreadyPresent = true;
            }
        }
        if (!alreadyPresent) {
            updated.add(alias);
        }
        return updated;
    }

    // rebuild alias set using all values from the method
    private LinkedHashSet<Value> collectAliases(FileStateFact fact, Set<Value> allValues) {
        LinkedHashSet<Value> alises = new LinkedHashSet<>();
        for (Value candidate : allValues) {
            if (fact.containsAlias(candidate)) {
                alises.add(candidate);
            }
        }
        return alises;
    }

    // Helpr method to gather all potential aliases (Locals, StaticFieldRefs, etc.)
    private Set<Value> getAllValuesInMethod() {
        Set<Value> values = new LinkedHashSet<>();
        if (method.getBody().getLocals() != null) {
            values.addAll(method.getBody().getLocals());
        }

        for (Stmt s : method.getBody().getStmts()) {
            if (s instanceof JAssignStmt) {
                values.add(((JAssignStmt) s).getLeftOp());
                values.add(((JAssignStmt) s).getRightOp());
            }
            if (s instanceof JInvokeStmt) {
                AbstractInvokeExpr expr = ((JInvokeStmt) s).getInvokeExpr();
                if (expr instanceof JVirtualInvokeExpr) {
                    values.add(((JVirtualInvokeExpr) expr).getBase());
                } else if (expr instanceof JSpecialInvokeExpr) {
                    values.add(((JSpecialInvokeExpr) expr).getBase());
                } else if (expr instanceof JInterfaceInvokeExpr) {
                    values.add(((JInterfaceInvokeExpr) expr).getBase());
                }
            }
        }
        return values;
    }



    @Nonnull
    @Override
    protected Set<FileStateFact> newInitialFlow() {
        return new HashSet<>();
    }

    @Override
    protected void copy(@Nonnull Set<FileStateFact> source, @Nonnull Set<FileStateFact> dest) {
        dest.clear();
        for (FileStateFact f : source) {
            dest.add(new FileStateFact(f));
        }
    }

    @Override
    protected void merge(@Nonnull Set<FileStateFact> in1, @Nonnull Set<FileStateFact> in2, @Nonnull Set<FileStateFact> out) {
        out.clear();
        for (FileStateFact f : in1) {
            out.add(new FileStateFact(f));
        }
        for (FileStateFact f : in2) {
            out.add(new FileStateFact(f));
        }
    }
}
