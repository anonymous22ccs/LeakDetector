package ??.??.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

import ??.??.configure.SootEnvironment;
import soot.Body;
import soot.Local;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
import soot.jimple.IdentityStmt;
import soot.jimple.Jimple;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.UnitValueBoxPair;

public class InterProcedureVariableAnalysis {
	private static String gBanner = "[InterProcedureVariableAnalysis]";
	
	private static boolean isDebug = false;
	
	private static final int maxInvokeDeep = 8;
	private static final int maxTgtNumber = 8;
	
	// ---- //
	
	// variable definition analysis reversely traverses the method and the callgraph
	
	public static List<Unit> findDefs(Body body, Stmt stmt, Local local) {
		String lBanner = gBanner + "[findDefs]" + " ";
		
		HashSet<SootMethod> handledMethods = new HashSet<SootMethod>(); // prevent recursive invocation
		handledMethods.add(body.getMethod());
		
		CallGraph cg = Scene.v().getCallGraph();
		List<Unit> defs = new ArrayList<Unit>();
		
		// [1] perform intra-procedure analysis
		List<Unit> intraDefs = IntraProcedureVariableAnalysis.findDefs(body, stmt, local);
		for (Unit intraDef : intraDefs) {
			defs.add(intraDef); // record each intra-definition
			// [2] perform inter-procedure analysis
			// [2-1] case: function A(*) { Object obj = *; B(obj); } | function B(*) { use obj }
			if (intraDef instanceof IdentityStmt) {
				IdentityStmt identity = (IdentityStmt) intraDef;
				Value identityRop = identity.getRightOp();
				if (!(identityRop instanceof ParameterRef)) {
					if (isDebug) {
						System.out.println(lBanner + "CASE-1: Right operator of IdentityStmt is not a ParameterRef instance.");
						System.out.println(lBanner + "{" + intraDef + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(intraDef) + "}");
					}
					continue;
				}
				ParameterRef paramRef = (ParameterRef) identityRop;
				int paramIdx = paramRef.getIndex();
				
				SootMethod tgtMethod = body.getMethod();
				int tgtCount = 0;
				Iterator<Edge> edges = cg.edgesInto(tgtMethod); // <-
				while (edges.hasNext()) {
					edges.next();
					tgtCount++;
				}
				if (tgtCount > maxTgtNumber) {
					if (isDebug) {
						// System.out.println(lBanner + "CASE-1: Invocation chain exceeds deep limit.");
					}
				} else {
					edges = cg.edgesInto(tgtMethod); // reset
				}
				
				while (edges.hasNext()) {
					Edge edge = edges.next();
					if (tgtMethod.getParameterCount() != edge.srcStmt().getInvokeExpr().getArgCount())
						continue;
					
					SootMethod srcMethod = edge.src();
					if (handledMethods.contains(srcMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-1: Recursive invocation happens.");
							System.out.println(lBanner + "{" + srcMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + srcMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-1: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(srcMethod);
					Body srcBody = srcMethod.retrieveActiveBody();
					Stmt srcStmt = edge.srcStmt();
					assert srcStmt.containsInvokeExpr(); // sanity check
					Value srcArg = srcStmt.getInvokeExpr().getArg(paramIdx);
					if (srcArg instanceof Local) {
						Local srcLocal = (Local) srcArg;
						findDefsUtil(srcBody, srcStmt, srcLocal, cg, newHandledMethods, defs); // almost the same as findDefs(*)
					} else if (srcArg instanceof Constant) {
						Local fakeLocal = Jimple.v().newLocal("fakeLocal", srcArg.getType());
						AssignStmt fakeStmt = Jimple.v().newAssignStmt(fakeLocal, srcArg);
						defs.add(fakeStmt);
					} else {
						if (isDebug) {
							System.out.println(lBanner + "CASE-1: Argument of the invocation is not a constant value or a local variable.");
							System.out.println(lBanner + "{" + srcStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(srcStmt) + "}");
						}
						continue;
					}
				}
			}
			// [2-2] case: function A(*) { Object obj = B(); } | function B(*) { return obj }
			if (intraDef instanceof AssignStmt && ((AssignStmt) intraDef).containsInvokeExpr()) {
				AssignStmt assign = (AssignStmt) intraDef;
				
				HashSet<SootMethod> tgtMethods = new HashSet<SootMethod>();
				// incorrect?
				tgtMethods.add(assign.getInvokeExpr().getMethod());
				// correct?
				Iterator<Edge> edges = cg.edgesOutOf(assign);
				while (edges.hasNext()) {
					Edge edge = edges.next();
					tgtMethods.add(edge.tgt());
				}
				if (tgtMethods.size() > maxTgtNumber)
					tgtMethods = new HashSet<SootMethod>();
				
				for (SootMethod tgtMethod : tgtMethods) {
					if (handledMethods.contains(tgtMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-2: Recursive invocation happens.");
							System.out.println(lBanner + "{" + tgtMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + tgtMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-2: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					if (!tgtMethod.isConcrete())
						continue;
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(tgtMethod);
					Body tgtBody = tgtMethod.retrieveActiveBody();
					UnitGraph tgtCfg = new BriefUnitGraph(tgtBody);
					List<Unit> tails = tgtCfg.getTails();
					for (Unit tail : tails) {
						if (!(tail instanceof ReturnStmt))
							continue;
						ReturnStmt tgtStmt = (ReturnStmt) tail;
						Value tgtValue = tgtStmt.getOp();
						if (tgtValue instanceof Local) {
							Local tgtLocal = (Local) tgtValue;
							findDefsUtil(tgtBody, tgtStmt, tgtLocal, cg, newHandledMethods, defs); // almost the same as findDefs(*)
						} else if (tgtValue instanceof Constant) {
							Local fakeLocal = Jimple.v().newLocal("fakeLocal", tgtValue.getType());
							AssignStmt fakeStmt = Jimple.v().newAssignStmt(fakeLocal, tgtValue);
							defs.add(fakeStmt);
						} else {
							if (isDebug) {
								System.out.println(lBanner + "CASE-2: The returned is not a constant value or a local variable.");
								System.out.println(lBanner + "{" + tgtStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(tgtStmt) + "}");
							}
							continue;
						}
					}
				}
			}
		}
		return defs;
	}
	
	private static void findDefsUtil(Body body, Stmt stmt, Local local, CallGraph cg, HashSet<SootMethod> handledMethods,  List<Unit> defs) {
		String lBanner = gBanner + "[findDefsUtil]" + " ";
		
		// [1] perform intra-procedure analysis
		List<Unit> intraDefs = IntraProcedureVariableAnalysis.findDefs(body, stmt, local);
		for (Unit intraDef : intraDefs) {
			defs.add(intraDef); // record each intra-definition
			// [2] perform inter-procedure analysis
			// [2-1] case: function A(*) { Object obj = *; B(obj); } | function B(*) { use obj }
			if (intraDef instanceof IdentityStmt) {
				IdentityStmt identity = (IdentityStmt) intraDef;
				Value identityRop = identity.getRightOp();
				if (!(identityRop instanceof ParameterRef)) {
					if (isDebug) {
						System.out.println(lBanner + "CASE-1: Right operator of IdentityStmt is not a ParameterRef instance.");
						System.out.println(lBanner + "{" + intraDef + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(intraDef) + "}");
					}
					continue;
				}
				ParameterRef paramRef = (ParameterRef) identityRop;
				int paramIdx = paramRef.getIndex();
				
				SootMethod tgtMethod = body.getMethod();
				int tgtCount = 0;
				Iterator<Edge> edges = cg.edgesInto(tgtMethod); // <-
				while (edges.hasNext()) {
					edges.next();
					tgtCount++;
				}
				if (tgtCount > maxTgtNumber) {
					if (isDebug) {
						// System.out.println(lBanner + "CASE-1: Invocation chain exceeds deep limit.");
					}
				} else {
					edges = cg.edgesInto(tgtMethod); // reset
				}
				
				while (edges.hasNext()) {
					Edge edge = edges.next();
					if (tgtMethod.getParameterCount() != edge.srcStmt().getInvokeExpr().getArgCount())
						continue;
					
					SootMethod srcMethod = edge.src();
					if (handledMethods.contains(srcMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-1: Recursive invocation happens.");
							System.out.println(lBanner + "{" + srcMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + srcMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-1: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(srcMethod);
					Body srcBody = srcMethod.retrieveActiveBody();
					Stmt srcStmt = edge.srcStmt();
					assert srcStmt.containsInvokeExpr(); // sanity check
					Value srcArg = srcStmt.getInvokeExpr().getArg(paramIdx);
					if (srcArg instanceof Local) {
						Local srcLocal = (Local) srcArg;
						findDefsUtil(srcBody, srcStmt, srcLocal, cg, newHandledMethods, defs); // almost the same as findDefs(*)
					} else if (srcArg instanceof Constant) {
						Local fakeLocal = Jimple.v().newLocal("fakeLocal", srcArg.getType());
						AssignStmt fakeStmt = Jimple.v().newAssignStmt(fakeLocal, srcArg);
						defs.add(fakeStmt);
					} else {
						if (isDebug) {
							System.out.println(lBanner + "CASE-1: Argument of the invocation is not a constant value or a local variable.");
							System.out.println(lBanner + "{" + srcStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(srcStmt) + "}");
						}
						continue;
					}
				}
			}
			// [2-2] case: function A(*) { Object obj = B(); } | function B(*) { return obj }
			if (intraDef instanceof AssignStmt && ((AssignStmt) intraDef).containsInvokeExpr()) {
				AssignStmt assign = (AssignStmt) intraDef;
				
				HashSet<SootMethod> tgtMethods = new HashSet<SootMethod>();
				// incorrect?
				tgtMethods.add(assign.getInvokeExpr().getMethod());
				// correct?
				Iterator<Edge> edges = cg.edgesOutOf(assign);
				while (edges.hasNext()) {
					Edge edge = edges.next();
					tgtMethods.add(edge.tgt());
				}
				if (tgtMethods.size() > maxTgtNumber)
					tgtMethods = new HashSet<SootMethod>();
				
				for (SootMethod tgtMethod : tgtMethods) {
					if (handledMethods.contains(tgtMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-2: Recursive invocation happens.");
							System.out.println(lBanner + "{" + tgtMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + tgtMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-2: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					if (!tgtMethod.isConcrete())
						continue;
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(tgtMethod);
					Body tgtBody = tgtMethod.retrieveActiveBody();
					UnitGraph tgtCfg = new BriefUnitGraph(tgtBody);
					List<Unit> tails = tgtCfg.getTails();
					for (Unit tail : tails) {
						if (!(tail instanceof ReturnStmt))
							continue;
						ReturnStmt tgtStmt = (ReturnStmt) tail;
						Value tgtValue = tgtStmt.getOp();
						if (tgtValue instanceof Local) {
							Local tgtLocal = (Local) tgtValue;
							findDefsUtil(tgtBody, tgtStmt, tgtLocal, cg, newHandledMethods, defs); // almost the same as findDefs(*)
						} else if (tgtValue instanceof Constant) {
							Local fakeLocal = Jimple.v().newLocal("fakeLocal", tgtValue.getType());
							AssignStmt fakeStmt = Jimple.v().newAssignStmt(fakeLocal, tgtValue);
							defs.add(fakeStmt);
						} else {
							if (isDebug) {
								System.out.println(lBanner + "CASE-2: The returned is not a constant value or a local variable.");
								System.out.println(lBanner + "{" + tgtStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(tgtStmt) + "}");
							}
							continue;
						}
					}
				}
			}
		}
	}
	
	// ---- //
	
	// variable use analysis reversely traverses the method and the callgraph to find variable definitions,
	// and then, it forwardly traverses the method and the callgraph to find variable uses.
	/*
	public static List<UnitValueBoxPair> findUses(Body body, Stmt stmt, Local local) {
		String lBanner = gBanner + "[findUses]" + " ";
		
		HashSet<SootMethod> handledMethods = new HashSet<SootMethod>(); // prevent recursive invocation
		handledMethods.add(body.getMethod());
		
		CallGraph cg = Scene.v().getCallGraph();
		List<UnitValueBoxPair> uses = new ArrayList<UnitValueBoxPair>();
		
		// [1] perform inter-procedure analysis (backward)
		List<Unit> intraDefs = IntraProcedureVariableAnalysis.findDefs(body, stmt, local);
		for (Unit intraDef : intraDefs) {
			// [1-1] case: function A(*) { Object obj = *; B(obj); } | function B(*) { use obj }
			if (intraDef instanceof IdentityStmt) {
				IdentityStmt identity = (IdentityStmt) intraDef;
				Value identityRop = identity.getRightOp();
				if (!(identityRop instanceof ParameterRef)) {
					System.out.println(lBanner + "CASE-1: Right operator of IdentityStmt is not a ParameterRef instance.");
					System.out.println(lBanner + "{" + intraDef + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(intraDef) + "}");
					continue;
				}
				ParameterRef paramRef = (ParameterRef) identityRop;
				int paramIdx = paramRef.getIndex();
				SootMethod tgtMethod = body.getMethod();
				Iterator<Edge> edges = cg.edgesInto(tgtMethod); // <-
				while (edges.hasNext()) {
					Edge edge = edges.next();
					SootMethod srcMethod = edge.src();
					// if (handledMethods.contains(srcMethod)) {
					if (false) {
						System.out.println(lBanner + "CASE-1: Recursive invocation happens.");
						System.out.println(lBanner + "{" + srcMethod.getSignature() + "}" + " " + "will call itself.");
						continue;
					}
					handledMethods.add(srcMethod);
					Body srcBody = srcMethod.retrieveActiveBody();
					Stmt srcStmt = edge.srcStmt();
					Value srcArg = srcStmt.getInvokeExpr().getArg(paramIdx);
					if (srcArg instanceof Local) {
						Local srcLocal = (Local) srcArg;
						findUsesBckwardUtil(srcBody, srcStmt, srcLocal, cg, handledMethods, uses);
					} else if (srcArg instanceof Constant) {
						Local fakeLocal = Jimple.v().newLocal("fakeLocal", srcArg.getType());
						AssignStmt fakeStmt = Jimple.v().newAssignStmt(fakeLocal, srcArg);
						ValueBox fakeValueBox = fakeStmt.getLeftOpBox();
						UnitValueBoxPair pair = new UnitValueBoxPair(fakeStmt, fakeValueBox);
						uses.add(pair);
					} else {
						System.out.println(lBanner + "CASE-1: Argument of the invocation is not a constant value or a local variable.");
						System.out.println(lBanner + "{" + srcStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(srcStmt) + "}");
						continue;
					}
				}
			}
			// [1-2] case: function A(*) { Object obj = B(); } | function B(*) { return obj }
			if (intraDef instanceof AssignStmt && ((AssignStmt) intraDef).containsInvokeExpr()) {
				AssignStmt assign = (AssignStmt) intraDef;
				SootMethod tgtMethod = assign.getInvokeExpr().getMethod();
				// if (handledMethods.contains(tgtMethod)) {
				if (false) {
					System.out.println(lBanner + "CASE-2: Recursive invocation happens.");
					System.out.println(lBanner + "{" + tgtMethod.getSignature() + "}" + " " + "will call itself.");
					continue;
				}
				if (!tgtMethod.isConcrete())
					continue;
				handledMethods.add(tgtMethod);
				Body tgtBody = tgtMethod.retrieveActiveBody();
				UnitGraph tgtCfg = new BriefUnitGraph(tgtBody);
				List<Unit> tails = tgtCfg.getTails();
				for (Unit tail : tails) {
					if (!(tail instanceof ReturnStmt))
						continue;
					ReturnStmt tgtStmt = (ReturnStmt) tail;
					Value tgtValue = tgtStmt.getOp();
					if (tgtValue instanceof Local) {
						Local tgtLocal = (Local) tgtValue;
						findUsesBckwardUtil(tgtBody, tgtStmt, tgtLocal, cg, handledMethods, uses);
					} else if (tgtValue instanceof Constant) {
						Local fakeLocal = Jimple.v().newLocal("fakeLocal", tgtValue.getType());
						AssignStmt fakeStmt = Jimple.v().newAssignStmt(fakeLocal, tgtValue);
						ValueBox fakeValueBox = fakeStmt.getLeftOpBox();
						UnitValueBoxPair pair = new UnitValueBoxPair(fakeStmt, fakeValueBox);
						uses.add(pair);
					} else {
						System.out.println(lBanner + "CASE-2: The returned is not a constant value or a local variable.");
						System.out.println(lBanner + "{" + tgtStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(tgtStmt) + "}");
						continue;
					}
				}
			}
		}
		// [2] perform intra-procedure analysis
		List<UnitValueBoxPair> intraUses = IntraProcedureVariableAnalysis.findUses(body, stmt, local); // *
		for (UnitValueBoxPair pair : intraUses) {
			Stmt intraUse = (Stmt) pair.unit;
			uses.add(pair); // record each intra-use
			// [3] perform inter-procedure analysis (forward)
			// [3-1] case: function A(*) { Object obj = *; B(obj); } | function B(*) { use obj }
			if (intraUse.containsInvokeExpr()) {
				if (intraUse instanceof AssignStmt)
					if (pair.getValueBox() == ((AssignStmt) intraUse).getLeftOpBox())
						continue;
				
				SootMethod tgtMethod = intraUse.getInvokeExpr().getMethod();
				// if (handledMethods.contains(tgtMethod)) {
				if (false) {
					System.out.println(lBanner + "CASE-3: Recursive invocation happens.");
					System.out.println(lBanner + "{" + tgtMethod.getSignature() + "}" + " " + "will call itself.");
					continue;
				}
				if (!tgtMethod.isConcrete())
					continue;
				handledMethods.add(tgtMethod);
				int argIdx = -1;
				for (int idx = 0; idx < intraUse.getInvokeExpr().getArgCount(); idx++) {
					ValueBox vb = intraUse.getInvokeExpr().getArgBox(idx);
					if (pair.getValueBox() == vb)
						argIdx = idx;
				}
				Body tgtBody = tgtMethod.retrieveActiveBody();
				Stmt tgtStmt = null;
				Local tgtLocal = null;
				for (Unit u : tgtBody.getUnits()) {
					if (argIdx == -1) {
						if (u instanceof IdentityStmt && ((IdentityStmt) u).getRightOp() instanceof ThisRef) {
							tgtStmt = (Stmt) u;
							tgtLocal = (Local) ((IdentityStmt) u).getLeftOp();
						}
					} else {
						if (u instanceof IdentityStmt && ((IdentityStmt) u).getRightOp() instanceof ParameterRef) {
							if (((ParameterRef) ((IdentityStmt) u).getRightOp()).getIndex() == argIdx) {
								tgtStmt = (Stmt) u;
								tgtLocal = (Local) ((IdentityStmt) u).getLeftOp();
							}
						}
					}
					if (tgtStmt != null || tgtLocal != null)
						break;
				}
				if (tgtStmt == null || tgtLocal == null)
					continue;
				findUsesForwardUtil(tgtBody, tgtStmt, tgtLocal, cg, handledMethods, uses);
			}
		}
		
		return uses;
	}
	*/
	
	public static List<UnitValueBoxPair> findUsesBckward(Body body, Stmt stmt, Local local) {
		String lBanner = gBanner + "[findUsesBackward]" + " ";
		
		HashSet<SootMethod> handledMethods = new HashSet<SootMethod>(); // prevent recursive invocation
		handledMethods.add(body.getMethod());
		
		CallGraph cg = Scene.v().getCallGraph();
		List<UnitValueBoxPair> uses = new ArrayList<UnitValueBoxPair>();
		
		// [1] perform inter-procedure analysis (backward)
		List<Unit> intraDefs = IntraProcedureVariableAnalysis.findDefs(body, stmt, local);
		for (Unit intraDef : intraDefs) {
			// [1-1] case: function A(*) { Object <obj> = *; B(<obj>); } | function B(*) { use <obj> }
			if (intraDef instanceof IdentityStmt) {
				IdentityStmt identity = (IdentityStmt) intraDef;
				Value identityRop = identity.getRightOp();
				if (!(identityRop instanceof ParameterRef)) {
					if (isDebug) {
						System.out.println(lBanner + "CASE-1: Right operator of IdentityStmt is not a ParameterRef instance.");
						System.out.println(lBanner + "{" + intraDef + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(intraDef) + "}");
					}
					continue;
				}
				ParameterRef paramRef = (ParameterRef) identityRop;
				int paramIdx = paramRef.getIndex();
				
				SootMethod tgtMethod = body.getMethod();
				int tgtCount = 0;
				Iterator<Edge> edges = cg.edgesInto(tgtMethod); // <-
				while (edges.hasNext()) {
					edges.next();
					tgtCount++;
				}
				if (tgtCount > maxTgtNumber) {
					if (isDebug) {
						// System.out.println(lBanner + "CASE-1: Invocation chain exceeds deep limit.");
					}
				} else {
					edges = cg.edgesInto(tgtMethod); // reset
				}
				
				while (edges.hasNext()) {
					Edge edge = edges.next();
					if (tgtMethod.getParameterCount() != edge.srcStmt().getInvokeExpr().getArgCount())
						continue;
					
					SootMethod srcMethod = edge.src();
					if (handledMethods.contains(srcMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-1: Recursive invocation happens.");
							System.out.println(lBanner + "{" + srcMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + srcMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-1: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(srcMethod);
					Body srcBody = srcMethod.retrieveActiveBody();
					Stmt srcStmt = edge.srcStmt();
					Value srcArg = srcStmt.getInvokeExpr().getArg(paramIdx);
					if (srcArg instanceof Local) {
						Local srcLocal = (Local) srcArg;
						findUsesBckwardUtil(srcBody, srcStmt, srcLocal, cg, newHandledMethods, uses);
					} else if (srcArg instanceof Constant) {
						Local fakeLocal = Jimple.v().newLocal("fakeLocal", srcArg.getType());
						AssignStmt fakeStmt = Jimple.v().newAssignStmt(fakeLocal, srcArg);
						ValueBox fakeValueBox = fakeStmt.getLeftOpBox();
						UnitValueBoxPair pair = new UnitValueBoxPair(fakeStmt, fakeValueBox);
						uses.add(pair);
					} else {
						if (isDebug) {
							System.out.println(lBanner + "CASE-1: Argument of the invocation is not a constant value or a local variable.");
							System.out.println(lBanner + "{" + srcStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(srcStmt) + "}");
						}
						continue;
					}
				}
			}
			// [1-2] case: function A(*) { Object <obj> = B(); } | function B(*) { return <obj>; }
			if (intraDef instanceof AssignStmt && ((AssignStmt) intraDef).containsInvokeExpr()) {
				AssignStmt assign = (AssignStmt) intraDef;
				
				// collect target methods
				HashSet<SootMethod> tgtMethods = new HashSet<SootMethod>();
				// incorrect?
				tgtMethods.add(assign.getInvokeExpr().getMethod());
				// correct?
				Iterator<Edge> edges = cg.edgesOutOf(assign);
				while (edges.hasNext()) {
					Edge edge = edges.next();
					tgtMethods.add(edge.tgt());
				}
				if (tgtMethods.size() > maxTgtNumber)
					tgtMethods = new HashSet<SootMethod>();
				
				for (SootMethod tgtMethod : tgtMethods) {
					if (handledMethods.contains(tgtMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-2: Recursive invocation happens.");
							System.out.println(lBanner + "{" + tgtMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + tgtMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-2: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					if (!tgtMethod.isConcrete())
						continue;
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(tgtMethod);
					Body tgtBody = tgtMethod.retrieveActiveBody();
					UnitGraph tgtCfg = new BriefUnitGraph(tgtBody);
					List<Unit> tails = tgtCfg.getTails();
					for (Unit tail : tails) {
						if (!(tail instanceof ReturnStmt))
							continue;
						ReturnStmt tgtStmt = (ReturnStmt) tail;
						Value tgtValue = tgtStmt.getOp();
						if (tgtValue instanceof Local) {
							Local tgtLocal = (Local) tgtValue;
							findUsesBckwardUtil(tgtBody, tgtStmt, tgtLocal, cg, newHandledMethods, uses);
						} else if (tgtValue instanceof Constant) {
							Local fakeLocal = Jimple.v().newLocal("fakeLocal", tgtValue.getType());
							AssignStmt fakeStmt = Jimple.v().newAssignStmt(fakeLocal, tgtValue);
							ValueBox fakeValueBox = fakeStmt.getLeftOpBox();
							UnitValueBoxPair pair = new UnitValueBoxPair(fakeStmt, fakeValueBox);
							uses.add(pair);
						} else {
							if (isDebug) {
								System.out.println(lBanner + "CASE-2: The returned is not a constant value or a local variable.");
								System.out.println(lBanner + "{" + tgtStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(tgtStmt) + "}");
							}
							continue;
						}
					}
				}
			}
		}
		// [2] perform intra-procedure analysis
		List<UnitValueBoxPair> intraUses = IntraProcedureVariableAnalysis.findUsesBckward(body, stmt, local); // *
		for (UnitValueBoxPair pair : intraUses) {
			Stmt intraUse = (Stmt) pair.unit;
			uses.add(pair); // record each intra-use
			// [3] perform inter-procedure analysis (forward)
			// [3-1] case: function A(*) { Object <obj> = *; B(<obj>); } | function B(*) { use <obj> }
			if (intraUse.containsInvokeExpr()) {
				if (intraUse instanceof AssignStmt)
					if (pair.getValueBox() == ((AssignStmt) intraUse).getLeftOpBox())
						continue;
				
				// collect target methods
				HashSet<SootMethod> tgtMethods = new HashSet<SootMethod>();
				// incorrect?
				tgtMethods.add(intraUse.getInvokeExpr().getMethod());
				// correct?
				Iterator<Edge> edges = cg.edgesOutOf(intraUse);
				while (edges.hasNext()) {
					Edge edge = edges.next();
					tgtMethods.add(edge.tgt());
				}
				if (tgtMethods.size() > maxTgtNumber)
					tgtMethods = new HashSet<SootMethod>();
				
				for (SootMethod tgtMethod : tgtMethods) {
					if (handledMethods.contains(tgtMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-3: Recursive invocation happens.");
							System.out.println(lBanner + "{" + tgtMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + tgtMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-3: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					if (!tgtMethod.isConcrete())
						continue;
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(tgtMethod);
					int argIdx = -1;
					for (int idx = 0; idx < intraUse.getInvokeExpr().getArgCount(); idx++) {
						ValueBox vb = intraUse.getInvokeExpr().getArgBox(idx);
						if (pair.getValueBox() == vb)
							argIdx = idx;
					}
					Body tgtBody = tgtMethod.retrieveActiveBody();
					Stmt tgtStmt = null;
					Local tgtLocal = null;
					for (Unit u : tgtBody.getUnits()) {
						if (argIdx == -1) {
							if (u instanceof IdentityStmt && ((IdentityStmt) u).getRightOp() instanceof ThisRef) {
								tgtStmt = (Stmt) u;
								tgtLocal = (Local) ((IdentityStmt) u).getLeftOp();
							}
						} else {
							if (u instanceof IdentityStmt && ((IdentityStmt) u).getRightOp() instanceof ParameterRef) {
								if (((ParameterRef) ((IdentityStmt) u).getRightOp()).getIndex() == argIdx) {
									tgtStmt = (Stmt) u;
									tgtLocal = (Local) ((IdentityStmt) u).getLeftOp();
								}
							}
						}
						if (tgtStmt != null || tgtLocal != null)
							break;
					}
					if (tgtStmt == null || tgtLocal == null)
						continue;
					findUsesForwardUtil(tgtBody, tgtStmt, tgtLocal, cg, newHandledMethods, uses);
				}
			}
		}
		
		return uses;
	}
	
	private static void findUsesBckwardUtil(Body body, Stmt stmt, Local local, CallGraph cg, HashSet<SootMethod> handledMethods, List<UnitValueBoxPair> uses) {
		String lBanner = gBanner + "[findUsesBckwardUtil]" + " ";
		
		// [1] perform inter-procedure analysis (backward)
		List<Unit> intraDefs = IntraProcedureVariableAnalysis.findDefs(body, stmt, local);
		for (Unit intraDef : intraDefs) {
			// [1-1] case: function A(*) { Object obj = *; B(<obj>); } | function B(*) { use <obj> }
			if (intraDef instanceof IdentityStmt) {
				IdentityStmt identity = (IdentityStmt) intraDef;
				Value identityRop = identity.getRightOp();
				if (!(identityRop instanceof ParameterRef)) {
					if (isDebug) {
						System.out.println(lBanner + "CASE-1: Right operator of IdentityStmt is not a ParameterRef instance.");
						System.out.println(lBanner + "{" + intraDef + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(intraDef) + "}");
					}
					continue;
				}
				ParameterRef paramRef = (ParameterRef) identityRop;
				int paramIdx = paramRef.getIndex();
				
				SootMethod tgtMethod = body.getMethod();
				int tgtCount = 0;
				Iterator<Edge> edges = cg.edgesInto(tgtMethod); // <-
				while (edges.hasNext()) {
					edges.next();
					tgtCount++;
				}
				if (tgtCount > maxTgtNumber) {
					if (isDebug) {
						// System.out.println(lBanner + "CASE-1: Invocation chain exceeds deep limit.");
					}
				} else {
					edges = cg.edgesInto(tgtMethod); // reset
				}
				
				while (edges.hasNext()) {
					Edge edge = edges.next();
					if (tgtMethod.getParameterCount() != edge.srcStmt().getInvokeExpr().getArgCount())
						continue;
					
					SootMethod srcMethod = edge.src();
					if (handledMethods.contains(srcMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-1: Recursive invocation happens.");
							System.out.println(lBanner + "{" + srcMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + srcMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-1: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(srcMethod);
					Body srcBody = srcMethod.retrieveActiveBody();
					Stmt srcStmt = edge.srcStmt();
					Value srcArg = srcStmt.getInvokeExpr().getArg(paramIdx);
					if (srcArg instanceof Local) {
						Local srcLocal = (Local) srcArg;
						findUsesBckwardUtil(srcBody, srcStmt, srcLocal, cg, newHandledMethods, uses);
					} else if (srcArg instanceof Constant) {
						Local fakeLocal = Jimple.v().newLocal("fakeLocal", srcArg.getType());
						AssignStmt fakeStmt = Jimple.v().newAssignStmt(fakeLocal, srcArg);
						ValueBox fakeValueBox = fakeStmt.getLeftOpBox();
						UnitValueBoxPair pair = new UnitValueBoxPair(fakeStmt, fakeValueBox);
						uses.add(pair);
					} else {
						if (isDebug) {
							System.out.println(lBanner + "CASE-1: Argument of the invocation is not a constant value or a local variable.");
							System.out.println(lBanner + "{" + srcStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(srcStmt) + "}");
						}
						continue;
					}
				}
			}
			// [1-2] case: function A(*) { Object <obj> = B(); } | function B(*) { return <obj>; }
			if (intraDef instanceof AssignStmt && ((AssignStmt) intraDef).containsInvokeExpr()) {
				AssignStmt assign = (AssignStmt) intraDef;
				
				// collect target methods
				HashSet<SootMethod> tgtMethods = new HashSet<SootMethod>();
				// incorrect?
				tgtMethods.add(assign.getInvokeExpr().getMethod());
				// correct?
				Iterator<Edge> edges = cg.edgesOutOf(assign);
				while (edges.hasNext()) {
					Edge edge = edges.next();
					tgtMethods.add(edge.tgt());
				}
				if (tgtMethods.size() > maxTgtNumber)
					tgtMethods = new HashSet<SootMethod>();
				
				for (SootMethod tgtMethod : tgtMethods) {
					if (handledMethods.contains(tgtMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-2: Recursive invocation happens.");
							System.out.println(lBanner + "{" + tgtMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + tgtMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-2: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					if (!tgtMethod.isConcrete())
						continue;
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(tgtMethod);
					Body tgtBody = tgtMethod.retrieveActiveBody();
					UnitGraph tgtCfg = new BriefUnitGraph(tgtBody);
					List<Unit> tails = tgtCfg.getTails();
					for (Unit tail : tails) {
						if (!(tail instanceof ReturnStmt))
							continue;
						ReturnStmt tgtStmt = (ReturnStmt) tail;
						Value tgtValue = tgtStmt.getOp();
						if (tgtValue instanceof Local) {
							Local tgtLocal = (Local) tgtValue;
							findUsesBckwardUtil(tgtBody, tgtStmt, tgtLocal, cg, newHandledMethods, uses);
						} else if (tgtValue instanceof Constant) {
							Local fakeLocal = Jimple.v().newLocal("fakeLocal", tgtValue.getType());
							AssignStmt fakeStmt = Jimple.v().newAssignStmt(fakeLocal, tgtValue);
							ValueBox fakeValueBox = fakeStmt.getLeftOpBox();
							UnitValueBoxPair pair = new UnitValueBoxPair(fakeStmt, fakeValueBox);
							uses.add(pair);
						} else {
							if (isDebug) {
								System.out.println(lBanner + "CASE-2: The returned is not a constant value or a local variable.");
								System.out.println(lBanner + "{" + tgtStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(tgtStmt) + "}");
							}
							continue;
						}
					}
				}
			}
		}
		// [2] perform intra-procedure analysis
		List<UnitValueBoxPair> intraUses = IntraProcedureVariableAnalysis.findUsesBckward(body, stmt, local); // *
		for (UnitValueBoxPair pair : intraUses) {
			Stmt intraUse = (Stmt) pair.unit;
			uses.add(pair); // record each intra-use
			// [3] perform inter-procedure analysis (forward)
			// [3-1] case: function A(*) { Object <obj> = *; B(<obj>); } | function B(*) { use <obj> }
			if (intraUse.containsInvokeExpr()) {
				if (intraUse instanceof AssignStmt)
					if (pair.getValueBox() == ((AssignStmt) intraUse).getLeftOpBox())
						continue;
				
				// collect target methods
				HashSet<SootMethod> tgtMethods = new HashSet<SootMethod>();
				// incorrect?
				tgtMethods.add(intraUse.getInvokeExpr().getMethod());
				// correct?
				Iterator<Edge> edges = cg.edgesOutOf(intraUse);
				while (edges.hasNext()) {
					Edge edge = edges.next();
					tgtMethods.add(edge.tgt());
				}
				if (tgtMethods.size() > maxTgtNumber)
					tgtMethods = new HashSet<SootMethod>();
				
				for (SootMethod tgtMethod : tgtMethods) {
					if (handledMethods.contains(tgtMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-3: Recursive invocation happens.");
							System.out.println(lBanner + "{" + tgtMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + tgtMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-3: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					if (!tgtMethod.isConcrete())
						continue;
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(tgtMethod);
					int argIdx = -1;
					for (int idx = 0; idx < intraUse.getInvokeExpr().getArgCount(); idx++) {
						ValueBox vb = intraUse.getInvokeExpr().getArgBox(idx);
						if (pair.getValueBox() == vb)
							argIdx = idx;
					}
					Body tgtBody = tgtMethod.retrieveActiveBody();
					Stmt tgtStmt = null;
					Local tgtLocal = null;
					for (Unit u : tgtBody.getUnits()) {
						if (argIdx == -1) {
							if (u instanceof IdentityStmt && ((IdentityStmt) u).getRightOp() instanceof ThisRef) {
								tgtStmt = (Stmt) u;
								tgtLocal = (Local) ((IdentityStmt) u).getLeftOp();
							}
						} else {
							if (u instanceof IdentityStmt && ((IdentityStmt) u).getRightOp() instanceof ParameterRef) {
								if (((ParameterRef) ((IdentityStmt) u).getRightOp()).getIndex() == argIdx) {
									tgtStmt = (Stmt) u;
									tgtLocal = (Local) ((IdentityStmt) u).getLeftOp();
								}
							}
						}
						if (tgtStmt != null || tgtLocal != null)
							break;
					}
					if (tgtStmt == null || tgtLocal == null)
						continue;
					findUsesForwardUtil(tgtBody, tgtStmt, tgtLocal, cg, newHandledMethods, uses);
				}
			}
		}
	}
	
	public static List<UnitValueBoxPair> findUsesForward(Body body, Stmt stmt, Local local) {
		String lBanner = gBanner + "[findUsesForward]" + " ";
		
		HashSet<SootMethod> handledMethods = new HashSet<SootMethod>(); // prevent recursive invocation
		handledMethods.add(body.getMethod());
		
		CallGraph cg = Scene.v().getCallGraph();
		List<UnitValueBoxPair> uses = new ArrayList<UnitValueBoxPair>();

		// [1] perform inter-procedure analysis (backward)
		List<Unit> intraDefs = IntraProcedureVariableAnalysis.findDefs(body, stmt, local);
		for (Unit intraDef : intraDefs) {
			// [1-1] case: function A(*) { B(<obj>); Object * = <obj>;  } | function B(*) { use <obj> }
			if (intraDef instanceof IdentityStmt) {
				IdentityStmt identity = (IdentityStmt) intraDef;
				Value identityRop = identity.getRightOp();
				if (!(identityRop instanceof ParameterRef)) {
					if (isDebug) {
						System.out.println(lBanner + "CASE-1: Right operator of IdentityStmt is not a ParameterRef instance.");
						System.out.println(lBanner + "{" + intraDef + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(intraDef) + "}");
					}
					continue;
				}
				ParameterRef paramRef = (ParameterRef) identityRop;
				int paramIdx = paramRef.getIndex();
				
				SootMethod tgtMethod = body.getMethod();
				int tgtCount = 0;
				Iterator<Edge> edges = cg.edgesInto(tgtMethod); // <-
				while (edges.hasNext()) {
					edges.next();
					tgtCount++;
				}
				if (tgtCount > maxTgtNumber) {
					if (isDebug) {
						// System.out.println(lBanner + "CASE-1: Invocation chain exceeds deep limit.");
					}
				} else {
					edges = cg.edgesInto(tgtMethod); // reset
				}
				
				while (edges.hasNext()) {
					Edge edge = edges.next();
					if (tgtMethod.getParameterCount() != edge.srcStmt().getInvokeExpr().getArgCount())
						continue;
					
					SootMethod srcMethod = edge.src();
					if (handledMethods.contains(srcMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-1: Recursive invocation happens.");
							System.out.println(lBanner + "{" + srcMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + srcMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-1: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(srcMethod);
					Body srcBody = srcMethod.retrieveActiveBody();
					Stmt srcStmt = edge.srcStmt();
					Value srcArg = srcStmt.getInvokeExpr().getArg(paramIdx);
					if (srcArg instanceof Local) {
						Local srcLocal = (Local) srcArg;
						findUsesForwardUtil(srcBody, srcStmt, srcLocal, cg, newHandledMethods, uses);
					} else if (srcArg instanceof Constant) {
						Local fakeLocal = Jimple.v().newLocal("fakeLocal", srcArg.getType());
						AssignStmt fakeStmt = Jimple.v().newAssignStmt(fakeLocal, srcArg);
						ValueBox fakeValueBox = fakeStmt.getLeftOpBox();
						UnitValueBoxPair pair = new UnitValueBoxPair(fakeStmt, fakeValueBox);
						uses.add(pair);
					} else {
						if (isDebug) {
							System.out.println(lBanner + "CASE-1: Argument of the invocation is not a constant value or a local variable.");
							System.out.println(lBanner + "{" + srcStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(srcStmt) + "}");
						}
						continue;
					}
				}
			}
		}
		// [2] perform intra-procedure analysis
		List<UnitValueBoxPair> intraUses = IntraProcedureVariableAnalysis.findUsesForward(body, stmt, local); // *
		for (UnitValueBoxPair pair : intraUses) {
			Stmt intraUse = (Stmt) pair.unit;
			uses.add(pair); // record each intra-use
			// [3] perform inter-procedure analysis (forward)
			// [3-1] case: function A(*) { Object <obj> = *; B(<obj>); } | function B(*) { use <obj> }
			if (intraUse.containsInvokeExpr()) {
				if (intraUse instanceof AssignStmt)
					if (pair.getValueBox() == ((AssignStmt) intraUse).getLeftOpBox())
						continue;
				
				HashSet<SootMethod> tgtMethods = new HashSet<SootMethod>();
				// incorrect?
				tgtMethods.add(intraUse.getInvokeExpr().getMethod());
				// correct?
				Iterator<Edge> edges = cg.edgesOutOf(intraUse);
				while (edges.hasNext()) {
					Edge edge = edges.next();
					tgtMethods.add(edge.tgt());
				}
				if (tgtMethods.size() > maxTgtNumber)
					tgtMethods = new HashSet<SootMethod>();
				
				for (SootMethod tgtMethod : tgtMethods) {
					if (handledMethods.contains(tgtMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-2: Recursive invocation happens.");
							System.out.println(lBanner + "{" + tgtMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + tgtMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-2: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					if (!tgtMethod.isConcrete())
						continue;
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(tgtMethod);
					int argIdx = -1;
					for (int idx = 0; idx < intraUse.getInvokeExpr().getArgCount(); idx++) {
						ValueBox vb = intraUse.getInvokeExpr().getArgBox(idx);
						if (pair.getValueBox() == vb)
							argIdx = idx;
					}
					Body tgtBody = tgtMethod.retrieveActiveBody();
					Stmt tgtStmt = null;
					Local tgtLocal = null;
					for (Unit u : tgtBody.getUnits()) {
						if (argIdx == -1) {
							if (u instanceof IdentityStmt && ((IdentityStmt) u).getRightOp() instanceof ThisRef) {
								tgtStmt = (Stmt) u;
								tgtLocal = (Local) ((IdentityStmt) u).getLeftOp();
							}
						} else {
							if (u instanceof IdentityStmt && ((IdentityStmt) u).getRightOp() instanceof ParameterRef) {
								if (((ParameterRef) ((IdentityStmt) u).getRightOp()).getIndex() == argIdx) {
									tgtStmt = (Stmt) u;
									tgtLocal = (Local) ((IdentityStmt) u).getLeftOp();
								}
							}
						}
						if (tgtStmt != null || tgtLocal != null)
							break;
					}
					if (tgtStmt == null || tgtLocal == null)
						continue;
					findUsesForwardUtil(tgtBody, tgtStmt, tgtLocal, cg, newHandledMethods, uses);
				}
			}
			// [3-2] case: function A(*) { Object <obj-alias> = B(*); use <obj-alias> } | function B(*) { Object <obj>; ret <obj>; }
			/*
			if (intraUse instanceof ReturnStmt) {
				if (!(((ReturnStmt) intraUse).getOp() instanceof Local))
					continue;
				SootMethod tgtMethod = body.getMethod();
				
				int tgtCount = 0;
				Iterator<Edge> edges = cg.edgesInto(tgtMethod); // <-
				while (edges.hasNext()) {
					edges.next();
					tgtCount++;
				}
				if (tgtCount > maxTgtNumber) {
					if (isDebug) {
						// System.out.println(lBanner + "CASE-3: Invocation chain exceeds deep limit.");
					}
				} else {
					edges = cg.edgesInto(tgtMethod); // reset
				}
				
				while (edges.hasNext()) {
					Edge edge = edges.next();
					SootMethod srcMethod = edge.src();
					if (handledMethods.contains(srcMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-3: Recursive invocation happens.");
							System.out.println(lBanner + "{" + srcMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + srcMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-3: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(srcMethod);
					Body srcBody = srcMethod.retrieveActiveBody();
					Stmt srcStmt = edge.srcStmt();
					if (!(srcStmt instanceof AssignStmt))
						continue;
					Value assigneeValue = ((AssignStmt) srcStmt).getLeftOp();
					if (assigneeValue instanceof Local) {
						findUsesForwardUtil(srcBody, srcStmt, (Local) assigneeValue, cg, newHandledMethods, uses);
					} else {
						if (isDebug) {
							System.out.println(lBanner + "CASE-3: Argument of the invocation is not a local variable.");
							System.out.println(lBanner + "{" + srcStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(srcStmt) + "}");
						}
						continue;
					}
				}
			}
			*/
		}
		
		return uses;
	}
	
	private static void findUsesForwardUtil(Body body, Stmt stmt, Local local, CallGraph cg, HashSet<SootMethod> handledMethods, List<UnitValueBoxPair> uses) {
		String lBanner = gBanner + "[findUsesForwardUtil]" + " ";

		// [1] perform inter-procedure analysis (backward)
		List<Unit> intraDefs = IntraProcedureVariableAnalysis.findDefs(body, stmt, local);
		for (Unit intraDef : intraDefs) {
			// [1-1] case: function A(*) { B(obj); Object * = obj;  } | function B(*) { use obj }
			if (intraDef instanceof IdentityStmt) {
				IdentityStmt identity = (IdentityStmt) intraDef;
				Value identityRop = identity.getRightOp();
				if (!(identityRop instanceof ParameterRef)) {
					if (isDebug) {
						System.out.println(lBanner + "CASE-1: Right operator of IdentityStmt is not a ParameterRef instance.");
						System.out.println(lBanner + "{" + intraDef + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(intraDef) + "}");
					}
					continue;
				}
				ParameterRef paramRef = (ParameterRef) identityRop;
				int paramIdx = paramRef.getIndex();
				
				SootMethod tgtMethod = body.getMethod();
				int tgtCount = 0;
				Iterator<Edge> edges = cg.edgesInto(tgtMethod); // <-
				while (edges.hasNext()) {
					edges.next();
					tgtCount++;
				}
				if (tgtCount > maxTgtNumber) {
					if (isDebug) {
						// System.out.println(lBanner + "CASE-1: Invocation chain exceeds deep limit.");
					}
				} else {
					edges = cg.edgesInto(tgtMethod); // reset
				}
				
				while (edges.hasNext()) {
					Edge edge = edges.next();
					if (tgtMethod.getParameterCount() != edge.srcStmt().getInvokeExpr().getArgCount())
						continue;
					
					SootMethod srcMethod = edge.src();
					if (handledMethods.contains(srcMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-1: Recursive invocation happens.");
							System.out.println(lBanner + "{" + srcMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + srcMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-1: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(srcMethod);
					Body srcBody = srcMethod.retrieveActiveBody();
					Stmt srcStmt = edge.srcStmt();
					Value srcArg = srcStmt.getInvokeExpr().getArg(paramIdx);
					if (srcArg instanceof Local) {
						Local srcLocal = (Local) srcArg;
						findUsesForwardUtil(srcBody, srcStmt, srcLocal, cg, newHandledMethods, uses);
					} else if (srcArg instanceof Constant) {
						Local fakeLocal = Jimple.v().newLocal("fakeLocal", srcArg.getType());
						AssignStmt fakeStmt = Jimple.v().newAssignStmt(fakeLocal, srcArg);
						ValueBox fakeValueBox = fakeStmt.getLeftOpBox();
						UnitValueBoxPair pair = new UnitValueBoxPair(fakeStmt, fakeValueBox);
						uses.add(pair);
					} else {
						if (isDebug) {
							System.out.println(lBanner + "CASE-1: Argument of the invocation is not a constant value or a local variable.");
							System.out.println(lBanner + "{" + srcStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(srcStmt) + "}");
						}
						continue;
					}
				}
			}
		}	
		// [2] perform intra-procedure analysis
		List<UnitValueBoxPair> intraUses = IntraProcedureVariableAnalysis.findUsesForward(body, stmt, local); // *
		for (UnitValueBoxPair pair : intraUses) {
			Stmt intraUse = (Stmt) pair.unit;
			uses.add(pair); // record each intra-use
			// [3] perform inter-procedure analysis (forward)
			// [3-1] case: function A(*) { Object obj = *; B(obj); } | function B(*) { use obj }
			if (intraUse.containsInvokeExpr()) {
				if (intraUse instanceof AssignStmt)
					if (pair.getValueBox() == ((AssignStmt) intraUse).getLeftOpBox())
						continue;
				
				// collect target methods
				HashSet<SootMethod> tgtMethods = new HashSet<SootMethod>();
				// incorrect?
				tgtMethods.add(intraUse.getInvokeExpr().getMethod());
				// correct?
				Iterator<Edge> edges = cg.edgesOutOf(intraUse);
				while (edges.hasNext()) {
					Edge edge = edges.next();
					tgtMethods.add(edge.tgt());
				}
				if (tgtMethods.size() > maxTgtNumber)
					tgtMethods = new HashSet<SootMethod>();
				
				for (SootMethod tgtMethod : tgtMethods) {
					if (handledMethods.contains(tgtMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-2: Recursive invocation happens.");
							System.out.println(lBanner + "{" + tgtMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + tgtMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-2: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					if (!tgtMethod.isConcrete())
						continue;
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(tgtMethod);
					int argIdx = -1;
					for (int idx = 0; idx < intraUse.getInvokeExpr().getArgCount(); idx++) {
						ValueBox vb = intraUse.getInvokeExpr().getArgBox(idx);
						if (pair.getValueBox() == vb)
							argIdx = idx;
					}
					Body tgtBody = tgtMethod.retrieveActiveBody();
					Stmt tgtStmt = null;
					Local tgtLocal = null;
					for (Unit u : tgtBody.getUnits()) {
						if (argIdx == -1) {
							if (u instanceof IdentityStmt && ((IdentityStmt) u).getRightOp() instanceof ThisRef) {
								tgtStmt = (Stmt) u;
								tgtLocal = (Local) ((IdentityStmt) u).getLeftOp();
							}
						} else {
							if (u instanceof IdentityStmt && ((IdentityStmt) u).getRightOp() instanceof ParameterRef) {
								if (((ParameterRef) ((IdentityStmt) u).getRightOp()).getIndex() == argIdx) {
									tgtStmt = (Stmt) u;
									tgtLocal = (Local) ((IdentityStmt) u).getLeftOp();
								}
							}
						}
						if (tgtStmt != null || tgtLocal != null)
							break;
					}
					if (tgtStmt == null || tgtLocal == null)
						continue;
					findUsesForwardUtil(tgtBody, tgtStmt, tgtLocal, cg, newHandledMethods, uses);
				}
			}
			// [3-2] case: function A(*) { Object <obj-alias> = B(*); use <obj-alias> } | function B(*) { Object <obj>; ret <obj>; }
			/*
			if (intraUse instanceof ReturnStmt) {
				if (!(((ReturnStmt) intraUse).getOp() instanceof Local))
					continue;
				SootMethod tgtMethod = body.getMethod();
				
				int tgtCount = 0;
				Iterator<Edge> edges = cg.edgesInto(tgtMethod); // <-
				while (edges.hasNext()) {
					edges.next();
					tgtCount++;
				}
				if (tgtCount > maxTgtNumber) {
					if (isDebug) {
						// System.out.println(lBanner + "CASE-3: Invocation chain exceeds deep limit.");
					}
				} else {
					edges = cg.edgesInto(tgtMethod); // reset
				}
				
				while (edges.hasNext()) {
					Edge edge = edges.next();
					SootMethod srcMethod = edge.src();
					if (handledMethods.contains(srcMethod)) {
					// if (false) {
						if (isDebug) {
							System.out.println(lBanner + "CASE-3: Recursive invocation happens.");
							System.out.println(lBanner + "{" + srcMethod.getSignature() + "}" + " " + "will be called recursively.");
							for (SootMethod handledMethod : handledMethods) {
								System.out.println(lBanner + "    " + handledMethod.getSignature());
							}
							System.out.println(lBanner + "    " + srcMethod.getSignature());
						}
						continue;
					}
					if (handledMethods.size() > maxInvokeDeep) {
						if (isDebug) {
							// System.out.println(lBanner + "CASE-3: Invocation chain exceeds deep limit.");
						}
						continue;
					}
					HashSet<SootMethod> newHandledMethods = new HashSet<SootMethod>(handledMethods);
					newHandledMethods.add(srcMethod);
					Body srcBody = srcMethod.retrieveActiveBody();
					Stmt srcStmt = edge.srcStmt();
					if (!(srcStmt instanceof AssignStmt))
						continue;
					Value assigneeValue = ((AssignStmt) srcStmt).getLeftOp();
					if (assigneeValue instanceof Local) {
						findUsesForwardUtil(srcBody, srcStmt, (Local) assigneeValue, cg, newHandledMethods, uses);
					} else {
						if (isDebug) {
							System.out.println(lBanner + "CASE-3: Argument of the invocation is not a local variable.");
							System.out.println(lBanner + "{" + srcStmt + "}" + " in " + "{" + SootEnvironment.Unit2MethodMap.get(srcStmt) + "}");
						}
						continue;
					}
				}
			}
			*/
		}
	}

}
