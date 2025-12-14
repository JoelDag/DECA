package analysis.exercise2;

import analysis.CallGraph;
import analysis.exercise1.CHAAlgorithm;
import java.util.*;
import javax.annotation.Nonnull;
import sootup.java.core.views.JavaView;
import sootup.core.signatures.MethodSignature;
import sootup.java.core.JavaSootMethod;
import sootup.java.core.JavaSootClass;
import sootup.core.jimple.common.expr.AbstractInvokeExpr;
import sootup.core.jimple.common.expr.JNewExpr;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.jimple.common.stmt.JInvokeStmt;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.jimple.common.stmt.JReturnStmt;
import sootup.core.jimple.basic.Value;
import sootup.core.types.ClassType;
import sootup.core.types.Type;

public class RTAAlgorithm extends CHAAlgorithm {

  private Set<ClassType> instantiatedClasses = new HashSet<>();

  @Nonnull
  @Override
  protected String getAlgorithm() {
    return "RTA";
  }

  @Override
  protected void populateCallGraph(@Nonnull JavaView view, @Nonnull CallGraph cg) {
    Queue<MethodSignature> todolist = new LinkedList<>();
    Set<MethodSignature> processed = new HashSet<>();

    getEntryPoints(view).forEach(entry -> {
      cg.addNode(entry);
      todolist.add(entry);
    });

    // discover all reachable methods and track instantiated classes
    while (!todolist.isEmpty()) {
      MethodSignature current = todolist.poll();
      if (processed.contains(current)) continue;
      processed.add(current);

      Optional<JavaSootMethod> methodOpt = view.getMethod(current);
      if (!methodOpt.isPresent() || !methodOpt.get().hasBody()) continue;

      JavaSootMethod method = methodOpt.get();
      
      for (Stmt stmt : method.getBody().getStmts()) {
        trackInstantiations(stmt);
        
        AbstractInvokeExpr invokeExpr = extractInvokeExpression(stmt);
        if (invokeExpr != null) {
          Set<MethodSignature> targets = super.resolveCall(invokeExpr, view);
          for (MethodSignature target : targets) {
            if (!cg.hasNode(target)) {
              cg.addNode(target);
              todolist.add(target);
            }
          }
        }
      }
    }

    // build call graph edges using RTA (only instantiated classes)
    todolist.clear();
    processed.clear();
    getEntryPoints(view).forEach(entry -> todolist.add(entry));

    while (!todolist.isEmpty()) {
      MethodSignature current = todolist.poll();
      if (processed.contains(current)) continue;
      processed.add(current);

      Optional<JavaSootMethod> methodOpt = view.getMethod(current);
      if (!methodOpt.isPresent() || !methodOpt.get().hasBody()) continue;

      JavaSootMethod method = methodOpt.get();
      
      for (Stmt stmt : method.getBody().getStmts()) {
        AbstractInvokeExpr invokeExpr = extractInvokeExpression(stmt);
        if (invokeExpr == null) continue;

        Set<MethodSignature> targets = resolveCall(invokeExpr, view);
        for (MethodSignature target : targets) {
          if (!cg.hasNode(target)) {
            cg.addNode(target);
            todolist.add(target);
          }
          if (!cg.hasEdge(current, target)) {
            cg.addEdge(current, target);
          }
        }
      }
    }
  }

  // track new expressions to find instantiated classes
  private void trackInstantiations(Stmt stmt) {
    if (stmt instanceof JAssignStmt) {
      JAssignStmt assignStmt = (JAssignStmt) stmt;
      if (assignStmt.getRightOp() instanceof JNewExpr) {
        JNewExpr newExpr = (JNewExpr) assignStmt.getRightOp();
        Type type = newExpr.getType();
        if (type instanceof ClassType) {
          instantiatedClasses.add((ClassType) type);
        }
      }
    } else if (stmt instanceof JReturnStmt) {
      JReturnStmt returnStmt = (JReturnStmt) stmt;
      Value retVal = returnStmt.getOp();
      if (retVal instanceof JNewExpr) {
        JNewExpr newExpr = (JNewExpr) retVal;
        Type type = newExpr.getType();
        if (type instanceof ClassType) {
          instantiatedClasses.add((ClassType) type);
        }
      }
    }
  }

  // extract method call from statement
  private AbstractInvokeExpr extractInvokeExpression(Stmt stmt) {
    if (stmt instanceof JInvokeStmt) {
      return ((JInvokeStmt) stmt).getInvokeExpr();
    } else if (stmt instanceof JAssignStmt) {
      JAssignStmt assignStmt = (JAssignStmt) stmt;
      if (assignStmt.getRightOp() instanceof AbstractInvokeExpr) {
        return (AbstractInvokeExpr) assignStmt.getRightOp();
      }
    }
    return null;
  }

  // only include instantiated classes in hierarchy
  @Override
  protected Set<ClassType> collectHierarchyTypes(ClassType startType, JavaView view) {
    Set<ClassType> types = new HashSet<>();
    Queue<ClassType> queue = new LinkedList<>();
    Set<ClassType> visited = new HashSet<>();
    queue.add(startType);

    while (!queue.isEmpty()) {
      ClassType current = queue.poll();
      if (visited.contains(current)) continue;
      visited.add(current);

      Optional<JavaSootClass> classOpt = view.getClass(current);
      if (!classOpt.isPresent()) continue;
      JavaSootClass sootClass = classOpt.get();

      // only include if instantiated (and not an interface)
      if (!sootClass.isInterface() && instantiatedClasses.contains(current)) {
        types.add(current);
      }

      for (JavaSootClass c : view.getClasses()) {
        if (c.hasSuperclass()) {
          Optional<? extends ClassType> superTypeOpt = c.getSuperclass();
          if (superTypeOpt.isPresent() && superTypeOpt.get().equals(current)) {
            if (!visited.contains(c.getType())) queue.add(c.getType());
          }
        }
      }

      if (sootClass.isInterface()) {
        for (JavaSootClass c : view.getClasses()) {
          if (c.getInterfaces().contains(current)) {
            if (!visited.contains(c.getType())) queue.add(c.getType());
          }
        }
      }
    }

    return types;
  }
  
  // only concrete classes, skip interfaces
  @Override
  protected void findMethodsInTypeAndSuperclasses(ClassType type, String methodName, List<Type> paramTypes, JavaView view, Set<MethodSignature> targets) {
    ClassType current = type;
    Set<ClassType> visited = new HashSet<>();
    
    while (current != null && !visited.contains(current)) {
      visited.add(current);
      Optional<JavaSootClass> classOpt = view.getClass(current);
      if (!classOpt.isPresent()) break;
      
      JavaSootClass sootClass = classOpt.get();
      
      if (!sootClass.isInterface()) {
        for (JavaSootMethod m : sootClass.getMethods()) {
          if (m.getName().equals(methodName) && m.getParameterTypes().equals(paramTypes)) {
            targets.add(m.getSignature());
          }
        }
      }
      
      if (sootClass.hasSuperclass()) {
        current = sootClass.getSuperclass().orElse(null);
      } else {
        current = null;
      }
    }
  }
}
