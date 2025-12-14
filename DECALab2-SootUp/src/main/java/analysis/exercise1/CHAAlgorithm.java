package analysis.exercise1;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import java.util.*;
import javax.annotation.Nonnull;
import sootup.java.core.views.JavaView;
import sootup.core.signatures.MethodSignature;
import sootup.java.core.JavaSootMethod;
import sootup.java.core.JavaSootClass;
import sootup.core.jimple.common.expr.AbstractInvokeExpr;
import sootup.core.jimple.common.expr.JSpecialInvokeExpr;
import sootup.core.jimple.common.expr.JStaticInvokeExpr;
import sootup.core.jimple.common.expr.JVirtualInvokeExpr;
import sootup.core.jimple.common.expr.JInterfaceInvokeExpr;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.jimple.common.stmt.JInvokeStmt;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.types.ClassType;
import sootup.core.types.Type;

public class CHAAlgorithm extends CallGraphAlgorithm {

  @Nonnull
  @Override
  protected String getAlgorithm() {
    return "CHA";
  }

  @Override
  protected void populateCallGraph(@Nonnull JavaView view, @Nonnull CallGraph cg) {
    Queue<MethodSignature> todolist = new LinkedList<>();
    Set<MethodSignature> processed = new HashSet<>();

    getEntryPoints(view).forEach(entry -> {
      cg.addNode(entry);
      todolist.add(entry);
    });

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

  // get invoke expression from statement
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

  // resolve call based on type
  protected Set<MethodSignature> resolveCall(AbstractInvokeExpr invokeExpr, JavaView view) {
    if (invokeExpr instanceof JSpecialInvokeExpr) {
      return Collections.singleton(invokeExpr.getMethodSignature());
    }
    if (invokeExpr instanceof JStaticInvokeExpr) {
      return Collections.singleton(invokeExpr.getMethodSignature());
    }
    if (invokeExpr instanceof JVirtualInvokeExpr || invokeExpr instanceof JInterfaceInvokeExpr) {
      MethodSignature methodSig = invokeExpr.getMethodSignature();
      Type declType = methodSig.getDeclClassType();
      if (declType instanceof ClassType) {
        return resolveVirtualCall((ClassType) declType, methodSig, view);
      }
    }
    return Collections.emptySet();
  }

  // resolve virtual call using declared receiver type
  protected Set<MethodSignature> resolveVirtualCall(ClassType receiverType, MethodSignature methodSig, JavaView view) {
    Set<MethodSignature> targets = new HashSet<>();
    String methodName = methodSig.getName();
    List<Type> paramTypes = methodSig.getParameterTypes();

    Set<ClassType> hierarchyTypes = collectHierarchyTypes(receiverType, view);

    for (ClassType type : hierarchyTypes) {
      findMethodsInTypeAndSuperclasses(type, methodName, paramTypes, view, targets);
    }
    return targets;
  }

  // collect all types in hierarchy
  protected Set<ClassType> collectHierarchyTypes(ClassType startType, JavaView view) {
    Set<ClassType> types = new HashSet<>();
    Queue<ClassType> queue = new LinkedList<>();
    Set<ClassType> visited = new HashSet<>();

    queue.add(startType);

    while (!queue.isEmpty()) {
      ClassType current = queue.poll();
      if (visited.contains(current)) continue;
      visited.add(current);
      types.add(current);

      Optional<JavaSootClass> classOpt = view.getClass(current);
      if (!classOpt.isPresent()) continue;
      JavaSootClass sootClass = classOpt.get();

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

  // find methods in type and superclasses
  protected void findMethodsInTypeAndSuperclasses(ClassType type, String methodName, List<Type> paramTypes, JavaView view, Set<MethodSignature> targets) {
    ClassType current = type;
    Set<ClassType> visited = new HashSet<>();
    
    while (current != null && !visited.contains(current)) {
      visited.add(current);
      Optional<JavaSootClass> classOpt = view.getClass(current);
      if (!classOpt.isPresent()) break;
      
      JavaSootClass sootClass = classOpt.get();
      for (JavaSootMethod m : sootClass.getMethods()) {
        if (m.getName().equals(methodName) && m.getParameterTypes().equals(paramTypes)) {
          targets.add(m.getSignature());
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
