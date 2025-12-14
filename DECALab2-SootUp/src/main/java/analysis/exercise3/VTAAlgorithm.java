package analysis.exercise3;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import java.util.*;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import org.graphstream.algorithm.TarjanStronglyConnectedComponents;
import org.graphstream.graph.Graph;
import org.graphstream.graph.Node;
import org.graphstream.graph.implementations.MultiGraph;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import sootup.core.jimple.basic.Value;
import sootup.core.jimple.common.ref.JFieldRef;
import sootup.core.jimple.common.expr.JNewExpr;
import sootup.core.jimple.common.expr.AbstractInvokeExpr;
import sootup.core.jimple.common.expr.JSpecialInvokeExpr;
import sootup.core.jimple.common.expr.JStaticInvokeExpr;
import sootup.core.jimple.common.expr.JVirtualInvokeExpr;
import sootup.core.jimple.common.expr.JInterfaceInvokeExpr;
import sootup.core.jimple.common.expr.JCastExpr;
import sootup.core.jimple.common.stmt.Stmt;
import sootup.core.jimple.common.stmt.JAssignStmt;
import sootup.core.jimple.common.stmt.JInvokeStmt;
import sootup.core.jimple.common.stmt.JReturnStmt;
import sootup.core.signatures.MethodSignature;
import sootup.core.types.ClassType;
import sootup.core.types.Type;
import sootup.java.core.views.JavaView;
import sootup.java.core.JavaSootMethod;
import sootup.java.core.JavaSootClass;

public class VTAAlgorithm extends CallGraphAlgorithm {

  private final Logger log = LoggerFactory.getLogger("VTA");

  @Nonnull
  @Override
  protected String getAlgorithm() {
    return "VTA";
  }

  @Override
  protected void populateCallGraph(@Nonnull JavaView view, @Nonnull CallGraph cg) {
    TypePropagationGraph tpg = new TypePropagationGraph();
    Queue<MethodSignature> todolist = new LinkedList<>();
    Set<MethodSignature> processed = new HashSet<>();
    Map<MethodSignature, Set<ClassType>> methodReturnTypes = new HashMap<>();
    Map<MethodSignature, List<Stmt>> methodStatements = new HashMap<>();

    getEntryPoints(view).forEach(entry -> {
      cg.addNode(entry);
      todolist.add(entry);
    });

    // Build type assignment graph and track return types
    while (!todolist.isEmpty()) {
      MethodSignature current = todolist.poll();
      if (processed.contains(current)) continue;
      processed.add(current);

      Optional<JavaSootMethod> methodOpt = view.getMethod(current);
      if (!methodOpt.isPresent() || !methodOpt.get().hasBody()) continue;

      JavaSootMethod method = methodOpt.get();
      List<Stmt> stmts = new ArrayList<>();
      for (Stmt stmt : method.getBody().getStmts()) {
        stmts.add(stmt);
      }
      methodStatements.put(current, stmts);

      Set<ClassType> returnTypes = buildGraphAndGetReturnTypes(stmts, tpg);
      if (!returnTypes.isEmpty()) {
        methodReturnTypes.put(current, returnTypes);
      }

      for (Stmt stmt : stmts) {
        Set<MethodSignature> targets = discoverMethodCalls(stmt, view);
        for (MethodSignature target : targets) {
          if (!cg.hasNode(target)) {
            cg.addNode(target);
            todolist.add(target);
          }
        }
      }
    }

    // Connect method return types to call sites
    for (List<Stmt> stmts : methodStatements.values()) {
      for (Stmt stmt : stmts) {
        connectMethodReturns(stmt, methodReturnTypes, tpg);
      }
    }

    // Propagate types through assignment graph
    propagateTypes(tpg);

    // Resolve calls using propagated types
    todolist.clear();
    processed.clear();
    getEntryPoints(view).forEach(entry -> todolist.add(entry));

    while (!todolist.isEmpty()) {
      MethodSignature current = todolist.poll();
      if (processed.contains(current)) continue;
      processed.add(current);

      List<Stmt> stmts = methodStatements.get(current);
      if (stmts == null) continue;

      for (Stmt stmt : stmts) {
        Set<MethodSignature> targets = resolveCallUsingTypes(stmt, tpg, view);
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
  
  // build graph and get return types
  private Set<ClassType> buildGraphAndGetReturnTypes(List<Stmt> statements, TypePropagationGraph tpg) {
    Set<ClassType> returnTypes = new HashSet<>();
    
    for (Stmt stmt : statements) {
      buildGraphForStatement(stmt, tpg);
      
      if (stmt instanceof JReturnStmt) {
        JReturnStmt returnStmt = (JReturnStmt) stmt;
        Value returnValue = returnStmt.getOp();
        
        if (returnValue instanceof JNewExpr) {
          Type t = ((JNewExpr) returnValue).getType();
          if (t instanceof ClassType) {
            returnTypes.add((ClassType) t);
          }
        } else {
          tpg.addNode(returnValue);
          returnTypes.addAll(tpg.getNodeTags(returnValue));
        }
      }
    }
    
    return returnTypes;
  }
  
  // build graph for one statement
  private void buildGraphForStatement(Stmt stmt, TypePropagationGraph tpg) {
    if (stmt instanceof JAssignStmt) {
      JAssignStmt assignStmt = (JAssignStmt) stmt;
      Value left = assignStmt.getLeftOp();
      Value right = assignStmt.getRightOp();

      tpg.addNode(left);
      tpg.addNode(right);
      tpg.addEdge(right, left);
      
      // handle new expressions
      if (right instanceof JNewExpr) {
        Type type = ((JNewExpr) right).getType();
        if (type instanceof ClassType) {
          tpg.tagNode(left, (ClassType) type);
        }
      }
      
      // handle casts
      if (right instanceof JCastExpr) {
        JCastExpr castExpr = (JCastExpr) right;
        Value castedValue = castExpr.getOp();
        tpg.addNode(castedValue);
        tpg.addEdge(castedValue, left);
      }
    }
  }
  
  // connect return types to call sites
  private void connectMethodReturns(Stmt stmt, Map<MethodSignature, Set<ClassType>> methodReturnTypes, TypePropagationGraph tpg) {
    if (stmt instanceof JAssignStmt) {
      JAssignStmt assignStmt = (JAssignStmt) stmt;
      Value left = assignStmt.getLeftOp();
      Value right = assignStmt.getRightOp();
      
      if (right instanceof AbstractInvokeExpr) {
        AbstractInvokeExpr invoke = (AbstractInvokeExpr) right;
        MethodSignature calledMethod = invoke.getMethodSignature();
        
        Set<ClassType> returnTypes = methodReturnTypes.get(calledMethod);
        if (returnTypes != null && !returnTypes.isEmpty()) {
          tpg.addNode(left);
          for (ClassType returnType : returnTypes) {
            tpg.tagNode(left, returnType);
          }
        }
      }
    }
  }

  // propagate types until fixpoint
  private void propagateTypes(TypePropagationGraph tpg) {
    boolean changed = true;
    while (changed) {
      changed = false;
      Set<Pair<Value, Set<ClassType>>> taggedNodes = tpg.getTaggedNodes();
      for (Pair<Value, Set<ClassType>> pair : taggedNodes) {
        Value source = pair.first;
        Set<ClassType> sourceTags = pair.second;
        Set<Value> targets = tpg.getTargetsFor(source);
        for (Value target : targets) {
          tpg.addNode(target);
          for (ClassType tagType : sourceTags) {
            Set<ClassType> targetTags = tpg.getNodeTags(target);
            if (!targetTags.contains(tagType)) {
              tpg.tagNode(target, tagType);
              changed = true;
            }
          }
        }
      }
    }
  }

  // discover method calls for todolist
  private Set<MethodSignature> discoverMethodCalls(Stmt stmt, JavaView view) {
    AbstractInvokeExpr invokeExpr = extractInvokeExpression(stmt);
    if (invokeExpr == null) return Collections.emptySet();
    
    if (invokeExpr instanceof JSpecialInvokeExpr || invokeExpr instanceof JStaticInvokeExpr) {
      return Collections.singleton(invokeExpr.getMethodSignature());
    }
    if (invokeExpr instanceof JVirtualInvokeExpr || invokeExpr instanceof JInterfaceInvokeExpr) {
      MethodSignature methodSig = invokeExpr.getMethodSignature();
      Type declType = methodSig.getDeclClassType();
      if (declType instanceof ClassType) {
        return resolveUsingCHA((ClassType) declType, methodSig, view);
      }
    }
    return Collections.emptySet();
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

  // resolve call using types from graph
  private Set<MethodSignature> resolveCallUsingTypes(Stmt stmt, TypePropagationGraph tpg, JavaView view) {
    AbstractInvokeExpr invokeExpr = extractInvokeExpression(stmt);
    if (invokeExpr == null) return Collections.emptySet();
    
    if (invokeExpr instanceof JSpecialInvokeExpr || invokeExpr instanceof JStaticInvokeExpr) {
      return Collections.singleton(invokeExpr.getMethodSignature());
    }
    
    if (invokeExpr instanceof JVirtualInvokeExpr || invokeExpr instanceof JInterfaceInvokeExpr) {
      Value base = (invokeExpr instanceof JVirtualInvokeExpr) 
          ? ((JVirtualInvokeExpr) invokeExpr).getBase()
          : ((JInterfaceInvokeExpr) invokeExpr).getBase();
      
      MethodSignature methodSig = invokeExpr.getMethodSignature();

      tpg.addNode(base);
      Set<ClassType> receiverTypes = tpg.getNodeTags(base);
      
      // fallback to CHA if there is no type information
      if (receiverTypes.isEmpty()) {
        Type declType = methodSig.getDeclClassType();
        if (declType instanceof ClassType) {
          return resolveUsingCHA((ClassType) declType, methodSig, view);
        }
        return Collections.emptySet();
      }
      
      Set<MethodSignature> targets = new HashSet<>();
      String methodName = methodSig.getName();
      List<Type> paramTypes = methodSig.getParameterTypes();
      
      for (ClassType receiverType : receiverTypes) {
        Set<ClassType> hierarchyTypes = collectSubtypes(receiverType, view);
        for (ClassType type : hierarchyTypes) {
          findMostSpecificMethod(type, methodName, paramTypes, view, targets);
        }
      }
      return targets;
    }
    
    return Collections.emptySet();
  }
  
  // use CHA for discovery
  private Set<MethodSignature> resolveUsingCHA(ClassType receiverType, MethodSignature methodSig, JavaView view) {
    Set<MethodSignature> targets = new HashSet<>();
    String methodName = methodSig.getName();
    List<Type> paramTypes = methodSig.getParameterTypes();

    Set<ClassType> hierarchyTypes = collectSubtypes(receiverType, view);

    for (ClassType type : hierarchyTypes) {
      findMostSpecificMethod(type, methodName, paramTypes, view, targets);
    }
    return targets;
  }
  
  // find most specific method (stops at first match)
  private void findMostSpecificMethod(ClassType type, String methodName, List<Type> paramTypes, JavaView view, Set<MethodSignature> targets) {
    ClassType current = type;
    Set<ClassType> visited = new HashSet<>();
    boolean found = false;
    
    while (current != null && !visited.contains(current) && !found) {
      visited.add(current);
      Optional<JavaSootClass> classOpt = view.getClass(current);
      if (!classOpt.isPresent()) break;
      
      JavaSootClass sootClass = classOpt.get();
      
      if (!sootClass.isInterface()) {
        for (JavaSootMethod m : sootClass.getMethods()) {
          if (m.getName().equals(methodName) && m.getParameterTypes().equals(paramTypes)) {
            targets.add(m.getSignature());
            found = true;
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

  // collect type and subtypes
  private Set<ClassType> collectSubtypes(ClassType startType, JavaView view) {
    Set<ClassType> types = new HashSet<>();
    types.add(startType);
    
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

      for (JavaSootClass c : view.getClasses()) {
        if (c.hasSuperclass()) {
          Optional<? extends ClassType> superTypeOpt = c.getSuperclass();
          if (superTypeOpt.isPresent() && superTypeOpt.get().equals(current)) {
            if (!visited.contains(c.getType())) {
              types.add(c.getType());
              queue.add(c.getType());
            }
          }
        }
      }

      if (sootClass.isInterface()) {
        for (JavaSootClass c : view.getClasses()) {
          if (c.getInterfaces().contains(current)) {
            if (!visited.contains(c.getType())) {
              types.add(c.getType());
              queue.add(c.getType());
            }
          }
        }
      }
    }

    return types;
  }

  static class Pair<A, B> {
    final A first;
    final B second;

    public Pair(A first, B second) {
      this.first = first;
      this.second = second;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o == null || getClass() != o.getClass()) return false;
      Pair<?, ?> pair = (Pair<?, ?>) o;
      if (!Objects.equals(first, pair.first)) return false;
      return Objects.equals(second, pair.second);
    }

    @Override
    public int hashCode() {
      int result = first != null ? first.hashCode() : 0;
      result = 31 * result + (second != null ? second.hashCode() : 0);
      return result;
    }

    @Override
    public String toString() {
      return "(" + first + ", " + second + ')';
    }
  }

  // graph to track variable types
  private class TypePropagationGraph {
    private final Graph graph;
    private final TarjanStronglyConnectedComponents tscc = new TarjanStronglyConnectedComponents();

    public TypePropagationGraph() {
      this.graph = new MultiGraph("tpg");
    }

    private boolean containsNode(Value value) {
      return graph.getNode(createId(value)) != null;
    }

    private boolean containsEdge(Value source, Value target) {
      return graph.getEdge(createId(source) + "-" + createId(target)) != null;
    }

    private String createId(Value value) {
      if (value instanceof JFieldRef) return value.toString();
      return Integer.toHexString(System.identityHashCode(value));
    }

    public void addNode(Value value) {
      if (!containsNode(value)) {
        Node node = graph.addNode(createId(value));
        node.setAttribute("value", value);
        node.setAttribute("ui.label", value);
        node.setAttribute("tags", new HashSet<ClassType>());
      }
    }

    public void tagNode(Value value, ClassType classTag) {
      if (containsNode(value)) {
        getNodeTags(value).add(classTag);
      }
    }

    public Set<Pair<Value, Set<ClassType>>> getTaggedNodes() {
      return graph.getNodeSet().stream()
          .map(n -> new Pair<Value, Set<ClassType>>(n.getAttribute("value"), n.getAttribute("tags")))
          .filter(p -> p.second.size() > 0)
          .collect(Collectors.toSet());
    }

    public Set<ClassType> getNodeTags(Value val) {
      Node node = graph.getNode(createId(val));
      if (node == null) {
        return new HashSet<>();
      }
      return node.getAttribute("tags");
    }

    public void addEdge(Value source, Value target) {
      if (!containsEdge(source, target)) {
        Node sourceNode = graph.getNode(createId(source));
        Node targetNode = graph.getNode(createId(target));
        if (sourceNode == null || targetNode == null)
          log.error("Could not find one of the nodes. Source: " + sourceNode + " - Target: " + targetNode);
        else
          graph.addEdge(createId(source) + "-" + createId(target), sourceNode, targetNode, true);
      }
    }

    public Set<Value> getTargetsFor(Value initialNode) {
      if (!containsNode(initialNode)) return Collections.emptySet();
      Node source = graph.getNode(createId(initialNode));
      Collection<org.graphstream.graph.Edge> edges = source.getLeavingEdgeSet();
      return edges.stream()
          .map(e -> (Value) e.getTargetNode().getAttribute("value"))
          .collect(Collectors.toSet());
    }

    public void annotateScc() {
      tscc.init(graph);
      tscc.compute();
    }

    public Object getSccIndex(Value value) {
      if (!containsNode(value)) return null;
      return graph.getNode(createId(value)).getAttribute(tscc.getSCCIndexAttribute());
    }

    public void draw() {
      graph.display();
    }
  }
}
