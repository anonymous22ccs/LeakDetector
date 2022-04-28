package ??.??.analysis;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import ??.??.configure.SootEnvironment;
import soot.Body;
import soot.Local;
import soot.Modifier;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.FieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.scalar.UnitValueBoxPair;

public class PermissionFinder {
	private static boolean isDebug = true;
	
	// output
	// method -> permissions
	public static HashMap<SootMethod, HashSet<String>> method2permissions = new HashMap<SootMethod, HashSet<String>>();
	// sensitive field -> paths
	public static HashMap<SootField, HashSet<ArrayList<SootMethod>>> field2paths = new HashMap<SootField, HashSet<ArrayList<SootMethod>>>();
	// method that returns sensitive data -> paths
	public static HashMap<SootMethod, HashSet<ArrayList<SootMethod>>> srcMethod2paths = new HashMap<SootMethod, HashSet<ArrayList<SootMethod>>>();
	// sensitive class -> paths
	public static HashMap<SootClass, HashSet<ArrayList<SootMethod>>> class2paths = new HashMap<SootClass, HashSet<ArrayList<SootMethod>>>();
	// ----
	
	private static void printOutput() {
		// sensitive field
		for (SootField sootField : field2paths.keySet()) {
			System.out.println("Field: " + sootField);
			HashSet<ArrayList<SootMethod>> paths = field2paths.get(sootField);
			if (paths == null)
				paths = new HashSet<ArrayList<SootMethod>>();
			int pathIdx = 0;
			for (ArrayList<SootMethod> path : paths) {
				HashSet<String> permissions = new HashSet<String>();
				for (SootMethod pathElement : path) {
					if (method2permissions.containsKey(pathElement)) {
						permissions.addAll(method2permissions.get(pathElement));
					}
				}
				System.out.println("\tPath-" + pathIdx);
				for (String permission : permissions) {
					System.out.println("\t\t" + permission);
				}
				pathIdx++;
			}
		}
		// method that returns sensitive data
		for (SootMethod sootMethod : srcMethod2paths.keySet()) {
			System.out.println("Method: " + sootMethod);
			HashSet<ArrayList<SootMethod>> paths = srcMethod2paths.get(sootMethod);
			if (paths == null)
				paths = new HashSet<ArrayList<SootMethod>>();
			int pathIdx = 0;
			for (ArrayList<SootMethod> path : paths) {
				HashSet<String> permissions = new HashSet<String>();
				for (SootMethod pathElement : path) {
					if (method2permissions.containsKey(pathElement)) {
						permissions.addAll(method2permissions.get(pathElement));
					}
				}
				System.out.println("\tPath-" + pathIdx);
				for (String permission : permissions) {
					System.out.println("\t\t" + permission);
				}
				pathIdx++;
			}
		}
	}
	
	// exported interface
	public static void analyze() {
		innerAnalyze();
	}
	
	private static void innerAnalyze() {
		HashMap<SootMethod, HashSet<Unit>> method2permissionUnit = new HashMap<>(); // method => units that consume permission strings
		HashMap<Unit, HashSet<String>> unit2permissions = new HashMap<>(); // unit => consumed permission strings
		
		CallGraph cg = Scene.v().getCallGraph();
		
		// Step-1: find permission string consumer
		HashSet<SootMethod> permissionConsumerSet = new HashSet<SootMethod>(); // method that takes permission string as parameter
		
		for (SootClass sootClass : Scene.v().getClasses()) {
			if (sootClass.isPhantom())
				continue;
			for (SootMethod sootMethod : sootClass.getMethods()) {
				// test
				// if (sootMethod.getName().equals("createVirtualDisplay")) {
					// if (sootMethod.hasActiveBody())
						// System.out.println(sootMethod.getActiveBody());
				// } else {
					// continue;
				// }
				
				if (!sootMethod.isConcrete())
					continue;
				
				Body body = sootMethod.retrieveActiveBody();
				for (Unit unit : body.getUnits()) {
					Stmt stmt = (Stmt) unit;
					// case-1: xx.method(xx, "*.permission.*", xx)
					//         xx = xx.method(xx, "*.permission.*, xx")
					if (stmt.containsInvokeExpr()) {
						boolean hasPermissionArg = false;
						String permissionString = null;
						
						List<Value> argValues = stmt.getInvokeExpr().getArgs();
						for (Value argValue : argValues) {
							if (!(argValue instanceof StringConstant))
								continue;
							String argString = ((StringConstant) argValue).value;
							if (argString.contains(".permission.") && !argString.contains(" ")) { // ignore the sentence that contains permission string
								if (Scene.v().getSootClassUnsafe(argString, false) != null)
									continue; // handle the case that argString is class name
								if (argString.contains("INTERACT_ACROSS_USERS")
								 || argString.contains("INTERACT_ACROSS_PROFILES")
								 || argString.contains("MANAGE_USERS")
								 || argString.contains("MANAGE_PROFILE_AND_DEVICE_OWNERS")
								 || argString.contains("INSTANT_APPS")) // ignore the special permission
									continue;
								
								hasPermissionArg = true;
								permissionString = argString;
								break;
							}
						}
						
						if (hasPermissionArg) {
							// System.out.println(String.format("[ case-1: %s ] in %s => %s", stmt, sootMethod.getSignature(), stmt.getInvokeExpr().getMethod())); // Debug
							// -> permissionConsumerSet
							permissionConsumerSet.add(stmt.getInvokeExpr().getMethod());
							// -> method2permissionUnit
							if (!method2permissionUnit.containsKey(sootMethod))
								method2permissionUnit.put(sootMethod, new HashSet<Unit>());
							method2permissionUnit.get(sootMethod).add(unit);
							// -> unit2permissions
							if (!unit2permissions.containsKey(unit))
								unit2permissions.put(unit, new HashSet<String>());
							unit2permissions.get(unit).add(permissionString);
						}
					}
					// case-2: xx = "*.permission.*"
					if (stmt instanceof AssignStmt) {
						Value rhsValue = ((AssignStmt) stmt).getRightOp();
						if (!(rhsValue instanceof StringConstant))
							continue;
						boolean hasPermissionString = false;
						String permissionString = null;
						
						String rhsString = ((StringConstant) rhsValue).value;
						if (rhsString.contains(".permission.") && !rhsString.contains(" ")) { // ignore the sentence that contains permission string
							if (Scene.v().getSootClassUnsafe(rhsString, false) != null) {
								// handle the case that rhsString is class name
							} else if (rhsString.contains("INTERACT_ACROSS_USERS")
									|| rhsString.contains("INSTANT_APPS")) {
								// handle the special permission
							} else {
								hasPermissionString = true;
								permissionString = rhsString;
							}
						}
						
						if (hasPermissionString) {
							if (sootMethod.getName().equals("<clinit>")) {
								// System.err.println(String.format("TODO: [ case-2: %s ] in %s", stmt, sootMethod.getSignature())); // Debug
							} else {
								// System.out.println(String.format("[ case-2: %s ] in %s", stmt, sootMethod.getSignature())); // Debug
								
								Value lhsValue = ((AssignStmt) stmt).getLeftOp();
								if (lhsValue instanceof Local) {
									List<UnitValueBoxPair> forwardUses = IntraProcedureVariableAnalysis.findUsesForward(body, stmt, (Local) lhsValue);
									for (UnitValueBoxPair forwardUse : forwardUses) {
										Unit useUnit = forwardUse.unit;
										// System.out.println("\t" + useUnit); // Debug
										
										Stmt useStmt = (Stmt) useUnit;
										if (!useStmt.containsInvokeExpr())
											continue;
										for (int argIdx = 0; argIdx < useStmt.getInvokeExpr().getArgCount(); argIdx++) {
											Value argValue = useStmt.getInvokeExpr().getArg(argIdx);
											if (argValue == lhsValue) {
												String argType = useStmt.getInvokeExpr().getMethod().getParameterType(argIdx).toString();
												if (argType.equals("java.lang.String")) {
													// System.out.println(String.format("\t[ case-2: %s ] in %s => %s", useStmt, sootMethod.getSignature(), useStmt.getInvokeExpr().getMethod())); // Debug
													// -> permissionConsumerSet
													permissionConsumerSet.add(useStmt.getInvokeExpr().getMethod());
													// -> method2permissionUnit
													if (!method2permissionUnit.containsKey(sootMethod))
														method2permissionUnit.put(sootMethod, new HashSet<Unit>());
													method2permissionUnit.get(sootMethod).add(useUnit);
													// -> unit2permissions
													if (!unit2permissions.containsKey(useUnit))
														unit2permissions.put(useUnit, new HashSet<String>());
													unit2permissions.get(useUnit).add(permissionString);
												}
											}
										}
									}
								} else if (lhsValue instanceof ArrayRef && ((ArrayRef) lhsValue).getBase() instanceof Local) {
									List<UnitValueBoxPair> forwardUses = IntraProcedureVariableAnalysis.findUsesForward(body, stmt, (Local) ((ArrayRef) lhsValue).getBase());
									for (UnitValueBoxPair forwardUse : forwardUses) {
										Unit useUnit = forwardUse.unit;
										// System.out.println("\t" + useUnit); // Debug
										
										Stmt useStmt = (Stmt) useUnit;
										if (!useStmt.containsInvokeExpr())
											continue;
										for (int argIdx = 0; argIdx < useStmt.getInvokeExpr().getArgCount(); argIdx++) {
											Value argValue = useStmt.getInvokeExpr().getArg(argIdx);
											if (argValue == ((ArrayRef) lhsValue).getBase()) {
												String argType = useStmt.getInvokeExpr().getMethod().getParameterType(argIdx).toString();
												if (argType.equals("java.lang.String[]")) {
													// System.out.println(String.format("\t[ case-2: %s ] in %s => %s", useStmt, sootMethod.getSignature(), useStmt.getInvokeExpr().getMethod())); // Debug
													// -> permissionConsumerSet
													permissionConsumerSet.add(useStmt.getInvokeExpr().getMethod());
													// -> method2permissionUnit
													if (!method2permissionUnit.containsKey(sootMethod))
														method2permissionUnit.put(sootMethod, new HashSet<Unit>());
													method2permissionUnit.get(sootMethod).add(useUnit);
													// -> unit2permissions
													if (!unit2permissions.containsKey(useUnit))
														unit2permissions.put(useUnit, new HashSet<String>());
													unit2permissions.get(useUnit).add(permissionString);
												}
											}
										}
									}
								} else {
									System.err.println(" ???? " + lhsValue.getClass());
								}
							}
						}
					}
				}
			}
		}
		
		// Debug
		// for (SootMethod sootMethod : method2permissionUnit.keySet()) {
			// System.out.println(sootMethod.getSignature());
			// for (Unit unit : method2permissionUnit.get(sootMethod)) {
				// System.out.println("\t" + unit);
				// HashSet<String> permissions = unit2permissions.get(unit);
				// for (String permission : permissions) {
					// System.out.println("\t\t" + permission);
				// }
			// }
		// }
		
		// Step2: find permission check methods
		HashSet<SootMethod> permissionCheckSet = new HashSet<SootMethod>(); // high-possible permission check method
		for (SootMethod permissionConsumer : permissionConsumerSet) {
			if ((permissionConsumer.getName().contains("permission") || permissionConsumer.getName().contains("Permission"))
			 && (permissionConsumer.getName().contains("check") || permissionConsumer.getName().contains("Check") 
			  || permissionConsumer.getName().contains("enforce") || permissionConsumer.getName().contains("Enforce")
			  || permissionConsumer.getName().contains("has") || permissionConsumer.getName().contains("Has"))) {
				permissionCheckSet.add(permissionConsumer);
				// System.out.println(String.format("[ Likely: %s ]", permissionConsumer.getSignature())); // Debug
			}
		}
		
		boolean isStable = false;
		while (isStable == false) {
			isStable = true;
			
			ArrayList<SootMethod> permissionConsumerList = new ArrayList<SootMethod>(permissionConsumerSet);
			permissionConsumerList.removeAll(permissionCheckSet);
			permissionConsumerList.sort(new Comparator<SootMethod>() {
				public int compare(SootMethod method1, SootMethod method2) {
					return method1.getSignature().compareTo(method2.getSignature());
				}
			});
			for (SootMethod permissionConsumer : permissionConsumerList) {
				// System.out.println(permissionConsumer.getSignature()); // Debug
				if (!permissionConsumer.isConcrete())
					continue;
			
				HashSet<SootMethod> calleeSet = new HashSet<SootMethod>();
			
				Queue<SootMethod> queue = new LinkedList<SootMethod>();
				queue.add(permissionConsumer);
				while (!queue.isEmpty()) {
					SootMethod sootMethod = queue.poll();
					if (calleeSet.contains(sootMethod))
						continue;
					calleeSet.add(sootMethod);
				
					Body body = sootMethod.getActiveBody();
					for (Unit unit : body.getUnits()) {
						Stmt stmt = (Stmt) unit;
						if (!stmt.containsInvokeExpr())
							continue;
						SootMethod callee = stmt.getInvokeExpr().getMethod();
						calleeSet.add(callee);
					
						if (callee.isConcrete())
							queue.add(callee);
					}
				}
			
				for (SootMethod callee : calleeSet) {
					if (permissionCheckSet.contains(callee)) {
						// System.err.println("\tYES: " + callee.getSignature()); // Debug
						permissionCheckSet.add(permissionConsumer);
						isStable = false;
						break;
					} else {
						// System.err.println("\tNO: " + callee.getSignature()); // Debug
					}
				}
				
				if (isStable == false)
					break;
			}
		}
		
		// for (SootMethod permissionCheck : permissionCheckSet) {
			// System.out.println(String.format("[ Permission Checker: %s ]", permissionCheck.getSignature())); // Debug
		// }
		// permissionConsumerSet.removeAll(permissionCheckSet);
		// for (SootMethod permissionConsumer : permissionConsumerSet) {
			// System.out.println(String.format("[ Permission Consumer: %s ]", permissionConsumer.getSignature())); // Debug
		// }
		
		// Step-3: fill in output
		for (SootMethod sootMethod : method2permissionUnit.keySet()) {
			if (isDebug) { System.out.println(sootMethod.getSignature()); } // Debug
			for (Unit unit : method2permissionUnit.get(sootMethod)) {
				Stmt stmt = (Stmt) unit;
				if (permissionCheckSet.contains(stmt.getInvokeExpr().getMethod())) {
					if (isDebug) { System.out.println("\tYES: " + unit); }
					HashSet<String> permissions = unit2permissions.get(unit);
					for (String permission : permissions) {
						if (isDebug) { System.out.println("\t\t" + permission); }
						if (!method2permissions.containsKey(sootMethod))
							method2permissions.put(sootMethod, new HashSet<String>());
						method2permissions.get(sootMethod).add(permission);
					}
				} else {
					if (isDebug) { System.out.println("\t NO: " + unit); }
				}
			}
		}
		
		// Step-4: 
		for (SootMethod sootMethod : method2permissions.keySet()) {
			// Test
			// if (!sootMethod.getSignature().equals("<com.android.server.adb.AdbService: java.util.Map getPairedDevices()>")) {
			// if (!sootMethod.getSignature().equals("<com.android.server.telecom.TelecomServiceImpl: boolean canReadPhoneState(java.lang.String,java.lang.String,java.lang.String)>")) {
			// if (!sootMethod.getSignature().equals("<com.android.server.telecom.TelecomServiceImpl$1: java.util.List getPhoneAccountsForPackage(java.lang.String)>")) {
			if (!sootMethod.getSignature().equals("<com.android.server.wifi.WifiServiceImpl: void enforceAccessPermission()>")) {
				// continue;
			}
			
			if (isDebug) { System.out.println(String.format("[ Paths to permission checker %s ]", sootMethod.getSignature())); } // Debug
			HashSet<ArrayList<SootMethod>> paths = CallgraphAnalysis.cmpPathBackward(sootMethod, null, 4);
			
			int pathIdx = 0;
			for (ArrayList<SootMethod> path : paths) {
				// filtering
				// check-1
				boolean hasGetMethod = false;
				for (SootMethod pathElement : path) {
					if ((pathElement.getName().startsWith("get") || pathElement.getName().startsWith("Get"))
					 || (pathElement.getName().length() > 6 && (pathElement.getName().startsWith("list") || pathElement.getName().startsWith("List")))) {
						hasGetMethod = true;
						break;
					}
				}
				if (hasGetMethod == false)
					continue;
				// check-2
				boolean hasConstructor = false;
				for (SootMethod pathElement : path) {
					if ((pathElement.getName().equals("<init>"))) {
						hasConstructor = true;
						break;
					}
				}
				if (hasConstructor == true)
					continue;
				// check-3
				if (path.size() < 2)
					continue;
				
				// record the discovered sensitive fields and classes in a path
				HashSet<SootField> pathSensitiveFieldSet = new HashSet<SootField>();
				HashSet<SootClass> pathSensitiveClassSet = new HashSet<SootClass>();
				
				// Debug
				pathIdx++;
				if (isDebug) { System.out.println(String.format("--Path-%d", pathIdx)); }
				ArrayList<SootMethod> orderedPath = new ArrayList<SootMethod>(path);
				Collections.reverse(orderedPath);
				// for (SootMethod element : orderedPath) {
					// System.out.println("\t" + element.getSignature());
				// }
				
				// find sensitive information
				for (int elementIdx = 0; elementIdx < orderedPath.size(); elementIdx++) {
					// record the discovered sensitive fields and classes in a path element
					HashSet<SootField> sensitiveFieldSet = new HashSet<SootField>();
					HashSet<SootClass> sensitiveClassSet = new HashSet<SootClass>();
					
					SootMethod element = orderedPath.get(elementIdx);
					SootMethod nextElement = null;
					if (elementIdx < orderedPath.size() - 1)
						nextElement = orderedPath.get(elementIdx + 1);
					if (isDebug) { System.out.println("\t" + element.getSignature()); } // Debug
					if ((nextElement != null) && element.getName().equals(nextElement.getName()))
						continue; // heuristic
					if (!element.getName().startsWith("get") && !element.getName().startsWith("Get")
					 && !element.getName().startsWith("list") && !element.getName().startsWith("List"))
						continue; // heuristic
					
					// find ret statements
					ArrayList<Unit> retUnits = new ArrayList<Unit>();
					Body body = element.retrieveActiveBody();
					for (Unit unit : body.getUnits()) {
						Stmt stmt = (Stmt) unit;
						if (stmt instanceof ReturnStmt) {
							// System.out.println("\t\tReturnStmt: " + stmt); // Debug
							Value retValue = ((ReturnStmt) stmt).getOp();
							if (retValue instanceof Constant)
								continue;
							retUnits.add(unit);
						}
					}
					
					// heuristic filtering
					if (retUnits.size() > 10)
						continue;
					
					// filtering
					boolean retAliasNextMethod = false;
					for (Unit retUnit : retUnits) {
						ReturnStmt retStmt = (ReturnStmt) retUnit;
						Value retValue = retStmt.getOp();
						if (!(retValue instanceof Local))
							continue;
						List<Unit> retDefs = InterProcedureVariableAnalysis.findDefs(body, retStmt, (Local) retValue);
						for (Unit retDef : retDefs) {
							if (!((Stmt) retDef).containsInvokeExpr())
								continue;
							Iterator<Edge> callees = cg.edgesOutOf(retDef);
							while (callees.hasNext()) {
								SootMethod callee = callees.next().tgt();
								if ((nextElement != null) && callee.getSignature().equals(nextElement.getSignature())) {
									retAliasNextMethod = true;
									break;
								}
							}
							if (retAliasNextMethod == true)
								break;
						}
						if (retAliasNextMethod == true)
							break;
					}
					if (retAliasNextMethod == true)
						continue;
					
					for (Unit retUnit : retUnits) {
						if (isDebug) { System.out.println("\t\tReturn Stmt: " + retUnit); } // Debug
						ReturnStmt retStmt = (ReturnStmt) retUnit;
						Value retValue = retStmt.getOp();
						if (!(retValue instanceof Local))
							continue;
						// List<Unit> retDefs = IntraProcedureVariableAnalysis.findDefs(body, stmt, (Local) retValue);
						List<Unit> retDefs = InterProcedureVariableAnalysis.findDefs(body, retStmt, (Local) retValue);
						if (retDefs.size() > 24) {
							if (isDebug) { System.out.println("\t\tDef-Analysis Number: " + retDefs.size()); } // Debug
							continue;
						}
						
						for (Unit retDef : retDefs) {
							if (!(retDef instanceof AssignStmt))
								continue;
							if (((AssignStmt) retDef).getLeftOp().toString().equals("fakeLocal") || ((AssignStmt) retDef).getLeftOp().toString().equals("fakeLocal"))
								continue;
							// Value retDefLhs = ((AssignStmt) retDef).getLeftOp();
							Value retDefRhs = ((AssignStmt) retDef).getRightOp();
							if (retDefRhs instanceof Constant)
								continue;
							if ((retDefRhs instanceof CastExpr) && !(((CastExpr) retDefRhs).getOp() instanceof Local))
								continue;
							
							if (isDebug) { System.out.println("\t\t  Def-Analysis: " + retDef + " [" + SootEnvironment.Unit2MethodMap.get(retDef).getSignature() + "]"); } // Debug
							// findSensitiveEntity(retStmt, retDef, new HashSet<Stmt>(), orderedPath);
							findSensitiveEntity(retStmt, retDef, new HashSet<Stmt>(), sensitiveFieldSet, sensitiveClassSet);
						}
					}
					
					// update pathSensitiveFieldSet and pathSensitiveClassSet
					if (sensitiveFieldSet.size() > 0 || sensitiveClassSet.size() > 0) {
						pathSensitiveFieldSet = new HashSet<SootField>(sensitiveFieldSet);
						pathSensitiveClassSet = new HashSet<SootClass>(sensitiveClassSet);
					}
				}
				
				// filtering sensitive fields according to sensitive classes
				for (SootField sensitiveField : new HashSet<SootField>(pathSensitiveFieldSet)) {
					if (pathSensitiveClassSet.contains(sensitiveField.getDeclaringClass())) {
						pathSensitiveFieldSet.remove(sensitiveField);
						continue;
					}
					// conservatively
					for (SootClass sensitiveClass : pathSensitiveClassSet) {
						if (sensitiveClass.getName().equals(sensitiveField.getDeclaringClass().getName())) {
							pathSensitiveFieldSet.remove(sensitiveField);
							break;
						}
					}
				}
				
				// fill in field2paths
				for (SootField sensitiveField : pathSensitiveFieldSet) {
					if (!field2paths.containsKey(sensitiveField))
						field2paths.put(sensitiveField, new HashSet<ArrayList<SootMethod>>());
					field2paths.get(sensitiveField).add(orderedPath);
				}
				// fill in class2paths
				for (SootClass sensitiveClass : pathSensitiveClassSet) {
					if (!class2paths.containsKey(sensitiveClass))
						class2paths.put(sensitiveClass, new HashSet<ArrayList<SootMethod>>());
					class2paths.get(sensitiveClass).add(orderedPath);
				}
			}
		}
	}
	
	// private static void findSensitiveEntity(Stmt retStmt, Unit retDef, HashSet<Stmt> handledStmts, ArrayList<SootMethod> orderedPath) {
	private static void findSensitiveEntity(Stmt retStmt, Unit retDef, HashSet<Stmt> handledStmts, HashSet<SootField> sensitiveFieldSet, HashSet<SootClass> sensitiveClassSet) {
		handledStmts.add(retStmt);
		
		// Value retDefLhs = ((AssignStmt) retDef).getLeftOp();
		Value retDefRhs = ((AssignStmt) retDef).getRightOp();
		
		if (retDefRhs instanceof FieldRef) {
			SootField retDefField = ((FieldRef) retDefRhs).getField();
			
			boolean passCheck = true;
			passCheck = refFieldCheck(retDefField);
			if (passCheck == true) {
				if (isDebug) { System.out.println("\t\t\tDef-Ref: " + retDefField); }
				
				// fill in field2paths
				// if (!field2paths.containsKey(retDefField))
					// field2paths.put(retDefField, new HashSet<ArrayList<SootMethod>>());
				// field2paths.get(retDefField).add(orderedPath);
				sensitiveFieldSet.add(retDefField);
				// ----
				
				// fill in class2paths
				Type fieldType = retDefField.getType();
				if (!fieldType.toString().endsWith("[]") && isBasicType(fieldType) == false && newTypeCheck(fieldType) == true) {
					SootClass fieldClass = Scene.v().getSootClass(fieldType.toString());
				
					// if (!class2paths.containsKey(fieldClass))
						// class2paths.put(fieldClass, new HashSet<ArrayList<SootMethod>>());
					// class2paths.get(fieldClass).add(orderedPath);
					sensitiveClassSet.add(fieldClass);
				}
				// ----
			}
		}
		
		// new **
		if (retDefRhs instanceof NewExpr) {
			Type newType = ((NewExpr) retDefRhs).getType();
			
			// if (newType.toString().contains("List")
			//  || newType.toString().contains("Set")
			//  || newType.toString().contains("Map"))
			// 	System.out.println("[??-test] " + newType.toString()); // test
			
			ArrayList<String> listClassNames = new ArrayList<String>();
			// ParceledList (<init>(List))
			listClassNames.add("android.content.pm.ParceledListSlice");
			listClassNames.add("android.content.pm.StringParceledListSlice");
			listClassNames.add("com.android.wifi.x.com.android.modules.utils.ParceledListSlice");
			// list (add)
			listClassNames.add("java.util.ArrayList");
			listClassNames.add("java.util.LinkedList");
			// map (put, append)
			listClassNames.add("android.util.ArrayMap");
			listClassNames.add("java.util.HashMap");
			listClassNames.add("java.util.LinkedHashMap");
			// set (add, append)
			listClassNames.add("android.util.ArraySet");
			listClassNames.add("java.util.HashSet");
			
			if (listClassNames.contains(newType.toString())) {
				// List<Unit> listElementDefs = handleListDefs((Stmt) retDef, (Local) ((AssignStmt) retDef).getLeftOp(), handledStmts, orderedPath);
				List<Unit> listElementDefs = handleListDefs((Stmt) retDef, (Local) ((AssignStmt) retDef).getLeftOp(), handledStmts, sensitiveFieldSet, sensitiveClassSet);
				for (Unit elementDef : listElementDefs) {
					if (!(elementDef instanceof AssignStmt))
						continue;
					
					Value elementDefLhs = ((AssignStmt) elementDef).getLeftOp();
					Value elementDefRhs = ((AssignStmt) elementDef).getRightOp();
					if (elementDefRhs instanceof FieldRef) {
						SootField elementDefField = ((FieldRef) elementDefRhs).getField();
						
						boolean passCheck = true;
						passCheck = refFieldCheck(elementDefField);
						if (passCheck == false)
							continue;
						
						if (isDebug) {
							System.out.println(String.format("\t\t\tElement-Def: %s in (%s)", elementDef, SootEnvironment.Unit2MethodMap.get(elementDef))); // Debug
							System.out.println(String.format("\t\t\tElement-Def-Ref: %s, %s", elementDef, elementDefField)); // Debug
						}
						
						// fill in field2paths
						// if (!field2paths.containsKey(elementDefField))
							// field2paths.put(elementDefField, new HashSet<ArrayList<SootMethod>>());
						// field2paths.get(elementDefField).add(orderedPath);
						sensitiveFieldSet.add(elementDefField);
						// ----
						
						// fill in class2paths
						Type elementType = elementDefField.getType();
						if (!elementType.toString().endsWith("[]") && isBasicType(elementType) == false && newTypeCheck(elementType) == true) {
							SootClass elementClass = Scene.v().getSootClass(elementType.toString());
						
							// if (!class2paths.containsKey(elementClass))
								// class2paths.put(elementClass, new HashSet<ArrayList<SootMethod>>());
							// class2paths.get(elementClass).add(orderedPath);
							sensitiveClassSet.add(elementClass);
						}
						// ----
					} else if (elementDefRhs instanceof NewExpr) {
						Type elementType = ((NewExpr) elementDefRhs).getType();
						if (!elementType.toString().endsWith("[]") && isBasicType(elementType) == false && newTypeCheck(elementType) == true) {
							SootClass elementClass = Scene.v().getSootClass(elementType.toString());
						
							if (isDebug) {
								System.out.println(String.format("\t\t\tElement-Def: %s in (%s)", elementDef, SootEnvironment.Unit2MethodMap.get(elementDef))); // Debug
								System.out.println(String.format("\t\t\tElement-Def-Ref: %s, new %s", elementDef, elementType.toString())); // Debug
							}
							
							// fill in class2paths
							// if (!class2paths.containsKey(elementClass))
								// class2paths.put(elementClass, new HashSet<ArrayList<SootMethod>>());
							// class2paths.get(elementClass).add(orderedPath);
							sensitiveClassSet.add(elementClass);
							// ----
						}
					} else {
						Type elementType = elementDefLhs.getType();
						if (!elementType.toString().endsWith("[]") && isBasicType(elementType) == false && newTypeCheck(elementType) == true) {
							SootClass elementClass = Scene.v().getSootClass(elementType.toString());
						
							if (isDebug) {
								System.out.println(String.format("\t\t\tElement-Def: %s in (%s)", elementDef, SootEnvironment.Unit2MethodMap.get(elementDef))); // Debug
								System.out.println(String.format("\t\t\tElement-Def-Ref: %s, class %s", elementDef, elementType.toString())); // Debug
							}
							
							// fill in class2paths
							// if (!class2paths.containsKey(elementClass))
								// class2paths.put(elementClass, new HashSet<ArrayList<SootMethod>>());
							// class2paths.get(elementClass).add(orderedPath);
							sensitiveClassSet.add(elementClass);
							// ----
						}
					}
				}
			} else {
				if (!newType.toString().endsWith("[]") && isBasicType(newType) == false && newTypeCheck(newType) == true) {
					SootClass newClass = Scene.v().getSootClass(newType.toString());
				
					if (isDebug) { System.out.println(String.format("\t\t\tDef-New: %s", newType)); } // Debug
			
					// fill in class2paths
					// if (!class2paths.containsKey(newClass))
						// class2paths.put(newClass, new HashSet<ArrayList<SootMethod>>());
					// class2paths.get(newClass).add(orderedPath);
					sensitiveClassSet.add(newClass);
					// ----
				}
			}
		}
		
		// newarray (BaseType)**
		if (retDefRhs instanceof NewArrayExpr) {
			// Type baseType = ((NewArrayExpr) retDefRhs).getBaseType();
			
			// case-1
			List<Unit> arrayElementDefs = handleArrayDefs((Stmt) retDef, (Local) ((AssignStmt) retDef).getLeftOp());
			for (Unit elementDef : arrayElementDefs) {
				if (!(elementDef instanceof AssignStmt))
					continue;
				
				Value elementDefLhs = ((AssignStmt) elementDef).getLeftOp();
				Value elementDefRhs = ((AssignStmt) elementDef).getRightOp();
				if (elementDefRhs instanceof FieldRef) {
					SootField elementDefField = ((FieldRef) elementDefRhs).getField();
					
					boolean passCheck = true;
					passCheck = refFieldCheck(elementDefField);
					if (passCheck == false)
						continue;
					
					if (isDebug) {
						System.out.println(String.format("\t\t\tElement-Def: %s in (%s)", elementDef, SootEnvironment.Unit2MethodMap.get(elementDef))); // Debug
						System.out.println(String.format("\t\t\tElement-Def-Ref: %s, %s", elementDef, elementDefField)); // Debug
					}
					
					// fill in field2paths
					// if (!field2paths.containsKey(elementDefField))
						// field2paths.put(elementDefField, new HashSet<ArrayList<SootMethod>>());
					// field2paths.get(elementDefField).add(orderedPath);
					sensitiveFieldSet.add(elementDefField);
					// ----
					
					// fill in class2paths
					Type elementType = elementDefField.getType();
					if (!elementType.toString().endsWith("[]") && isBasicType(elementType) == false && newTypeCheck(elementType) == true) {
						SootClass elementClass = Scene.v().getSootClass(elementType.toString());
				
						// if (!class2paths.containsKey(elementClass))
							// class2paths.put(elementClass, new HashSet<ArrayList<SootMethod>>());
						// class2paths.get(elementClass).add(orderedPath);
						sensitiveClassSet.add(elementClass);
					}
					// ----
				} else if (elementDefRhs instanceof NewExpr) {
					Type elementType = ((NewExpr) elementDefRhs).getType();
					if (!elementType.toString().endsWith("[]") && isBasicType(elementType) == false && newTypeCheck(elementType) == true) {
						SootClass elementClass = Scene.v().getSootClass(elementType.toString());
						
						if (isDebug) {
							System.out.println(String.format("\t\t\tElement-Def: %s in (%s)", elementDef, SootEnvironment.Unit2MethodMap.get(elementDef))); // Debug
							System.out.println(String.format("\t\t\tElement-Def-Ref: %s, new %s", elementDef, elementType.toString())); // Debug
						}
						
						// fill in class2paths
						// if (!class2paths.containsKey(elementClass))
							// class2paths.put(elementClass, new HashSet<ArrayList<SootMethod>>());
						// class2paths.get(elementClass).add(orderedPath);
						sensitiveClassSet.add(elementClass);
						// ----
					}
				} else {
					Type elementType = elementDefLhs.getType();
					if (!elementType.toString().endsWith("[]") && isBasicType(elementType) == false && newTypeCheck(elementType) == true) {
						SootClass elementClass = Scene.v().getSootClass(elementType.toString());
						
						if (isDebug) {
							System.out.println(String.format("\t\t\tElement-Def: %s in (%s)", elementDef, SootEnvironment.Unit2MethodMap.get(elementDef))); // Debug
							System.out.println(String.format("\t\t\tElement-Def-Ref: %s, class %s", elementDef, elementType.toString())); // Debug
						}
						
						// fill in class2paths
						// if (!class2paths.containsKey(elementClass))
							// class2paths.put(elementClass, new HashSet<ArrayList<SootMethod>>());
						// class2paths.get(elementClass).add(orderedPath);
						sensitiveClassSet.add(elementClass);
						// ----
					}
				}
			}
		}
		
		/*
		if (retDefRhs instanceof CastExpr) {
			List<Unit> retPreDefs = InterProcedureVariableAnalysis.findDefs(SootEnvironment.Unit2MethodMap.get(retDef).retrieveActiveBody(), (Stmt) retDef, (Local) ((CastExpr) retDefRhs).getOp());
			for (Unit retPreDef : retPreDefs) {
				if (!(retPreDef instanceof AssignStmt))
					continue;
				Value retPreDefLhs = ((AssignStmt) retPreDef).getLeftOp();
				Value retPreDefRhs = ((AssignStmt) retPreDef).getRightOp();
				if (!(retPreDefRhs instanceof FieldRef) && !(retPreDefRhs instanceof InvokeExpr))
					continue;
				// check: callees should have same return values
				boolean passCheck = true;
				for (int preElementIdx = 0; preElementIdx < elementIdx; preElementIdx ++) {
					if (preElementIdx == (orderedPath.size() - 2))
						break;
					if (!orderedPath.get(preElementIdx).getReturnType().toString().equals(orderedPath.get(preElementIdx + 1).getReturnType().toString())) {
						passCheck = false;
						break;
					}
				}
				// for (int pstElementIdx = (elementIdx + 1); pstElementIdx < orderedPath.size(); pstElementIdx ++) {
					// if (!orderedPath.get(pstElementIdx).getReturnType().toString().equals(orderedPath.get(elementIdx).getReturnType().toString())) {
						// passCheck = false;
						// break;
					// }
				// }
				if (passCheck == false)
					continue;
				
				if (retPreDefRhs instanceof FieldRef) {
					SootField retPreDefRefField = ((FieldRef) retPreDefRhs).getField();
					if (refFieldCheck(retPreDefRefField) == false)
						continue;
					
					System.out.println(String.format("\t\t\tRet-Def-Pre: %s", retPreDef));
					System.out.println(String.format("\t\t\tRet-Def-Pre-Ref: %s", retPreDefRefField));
					
					// fill in field2paths
					if (!field2paths.containsKey(retPreDefRefField))
						field2paths.put(retPreDefRefField, new HashSet<ArrayList<SootMethod>>());
					field2paths.get(retPreDefRefField).add(orderedPath);
					// ----
				}
				if (retPreDefRhs instanceof InvokeExpr) {
					SootMethod retPreDefSrcMethod = ((InvokeExpr) retPreDefRhs).getMethod();
					if (!retPreDefSrcMethod.isConcrete())
						continue;
					if (isBasicType(retPreDefLhs.getType()))
						continue;
					if (srcMethodCheck(retPreDefSrcMethod) == false)
						continue;
					
					System.out.println(String.format("\t\t\tRet-Def-Pre: %s", retPreDef));
					System.out.println(String.format("\t\t\tRet-Def-Pref-Src: %s", retPreDefSrcMethod));
					
					// fill in srcMethod2paths
					if (!srcMethod2paths.containsKey(retPreDefSrcMethod))
						srcMethod2paths.put(retPreDefSrcMethod, new HashSet<ArrayList<SootMethod>>());
					srcMethod2paths.get(retPreDefSrcMethod).add(orderedPath);
					// ----
				}
			}
		}
		*/
		
		if (retDefRhs instanceof InvokeExpr) {
			InvokeExpr retDefInvokeExpr = (InvokeExpr) retDefRhs;
			// normal case
			
			SootMethod retDefSrcMethod = retDefInvokeExpr.getMethod();
			if (retDefSrcMethod.isConcrete()) {
				// boolean passCheck = true;
				// check-1: callees should have same return values
				/*
				for (int preElementIdx = 0; preElementIdx < elementIdx; preElementIdx ++) {
					if (preElementIdx == (orderedPath.size() - 2))
						break;
					if (!orderedPath.get(preElementIdx).getReturnType().toString().equals(orderedPath.get(preElementIdx + 1).getReturnType().toString())) {
						passCheck = false;
						break;
					}
				}
				*/
				/*
				for (int pstElementIdx = (elementIdx + 1); pstElementIdx < orderedPath.size(); pstElementIdx ++) {
					if (!orderedPath.get(pstElementIdx).getReturnType().toString().equals(orderedPath.get(elementIdx).getReturnType().toString())) {
						passCheck = false;
						break;
					}
				}
				*/
				// check-2
				/*
				if (passCheck == true)
					passCheck = srcMethodCheck(retDefSrcMethod);
				
				if (passCheck == true) {
					if (!isBasicType(retDefLhs.getType())) {
						System.out.println(String.format("\t\t\tRet-Src: %s", retDefSrcMethod));
						
						// fill in srcMethod2paths
						if (!srcMethod2paths.containsKey(retDefSrcMethod))
							srcMethod2paths.put(retDefSrcMethod, new HashSet<ArrayList<SootMethod>>());
						srcMethod2paths.get(retDefSrcMethod).add(orderedPath);
						// ----
					}
				}
				*/
			}
			
			// special case - 1
			if (retDefInvokeExpr instanceof InstanceInvokeExpr) {
				Local retDefInvokeBase = (Local) ((InstanceInvokeExpr) retDefInvokeExpr).getBase();
				List<Unit> retDepDefs = IntraProcedureVariableAnalysis.findDefs(SootEnvironment.Unit2MethodMap.get(retDef).retrieveActiveBody(), (Stmt) retDef, retDefInvokeBase);
				for (Unit retDepDef : retDepDefs) {
					// System.out.println(retDepDef); // Debug
					if (!(retDepDef instanceof AssignStmt))
						continue;
					Value retDepRef = ((AssignStmt) retDepDef).getRightOp();
					
					if ((retStmt instanceof ReturnStmt) && (retDepRef instanceof FieldRef)) {
						SootField retDepField = ((FieldRef) retDepRef).getField();
						if (aliasTypeCheck(((ReturnStmt) retStmt).getOp().getType(), retDepField.getType()) == false)
							continue;
						
						boolean passCheck = true;
						passCheck = refFieldCheck(retDepField);
						if (passCheck == false)
							continue;
						
						if (isDebug) { System.out.println(String.format("\t\t\tRet-Dep-Def: %s, %s", retDepDef, retDepField)); }
					
						// fill in field2paths
						// if (!field2paths.containsKey(retDepField))
							// field2paths.put(retDepField, new HashSet<ArrayList<SootMethod>>());
						// field2paths.get(retDepField).add(orderedPath);
						sensitiveFieldSet.add(retDepField);
						// ----
						
						// fill in class2paths
						Type fieldType = retDepField.getType();
						if (!fieldType.toString().endsWith("[]") && isBasicType(fieldType) == false && newTypeCheck(fieldType) == true) {
							SootClass fieldClass = Scene.v().getSootClass(fieldType.toString());
					
							// if (!class2paths.containsKey(fieldClass))
								// class2paths.put(fieldClass, new HashSet<ArrayList<SootMethod>>());
							// class2paths.get(fieldClass).add(orderedPath);
							sensitiveClassSet.add(fieldClass);
						}
						// ----
					}
					
					// for case like "List.toArray()"
					/*
					if (retDepRef instanceof NewArrayExpr) {
						Type newBaseType = ((NewArrayExpr) retDepRef).getBaseType();
						if (newTypeCheck(newBaseType) == true) {
							SootClass elementClass = Scene.v().getSootClass(newBaseType.toString());
									
							System.out.println(String.format("\t\t\tElement-Def: %s in (%s)", elementDef, SootEnvironment.Unit2MethodMap.get(elementDef))); // Debug
							System.out.println(String.format("\t\t\tElement-Def-Ref: %s, new %s", elementDef, elementType.toString())); // Debug
								
							// fill in class2paths
							if (!class2paths.containsKey(elementClass))
								class2paths.put(elementClass, new HashSet<ArrayList<SootMethod>>());
							class2paths.get(elementClass).add(orderedPath);
							// ----
						}
					}
					*/
				}
			}
		}
	}
	
	//
	// ParceledList ( <init>(List) )
	// "android.content.pm.ParceledListSlice"
	// "android.content.pm.StringParceledListSlice"
	// "com.android.wifi.x.com.android.modules.utils.ParceledListSlice"
	// List ( <init>(Collection), addAll([*,] Collection), add(Object) )
	// "java.util.ArrayList"
	// "java.util.LinkedList"
	// Map ( <init>(Map), putAll(Map), put(Object, Object), append(Object, Object) )
	// "android.util.ArrayMap"
	// "java.util.HashMap"
	// "java.util.LinkedHashMap"
	// Set ( <init>(Collection), addAll(Collection), add(Object), append(Object) )
	// "android.util.ArraySet"
	// "java.util.HashSet"
	
	// private static List<Unit> handleListDefs(Stmt newListStmt, Local listLocal, HashSet<Stmt> handledStmts, ArrayList<SootMethod> orderedPath) {
	private static List<Unit> handleListDefs(Stmt newListStmt, Local listLocal, HashSet<Stmt> handledStmts, HashSet<SootField> sensitiveFieldSet, HashSet<SootClass> sensitiveClassSet) {
		List<Unit> listElementDefs = new ArrayList<Unit>();
		
		SootMethod curMethod = SootEnvironment.Unit2MethodMap.get(newListStmt);
		if (curMethod == null)
			return listElementDefs; // rare cases
		Body curBody = curMethod.retrieveActiveBody();
		
		List<UnitValueBoxPair> listUses = IntraProcedureVariableAnalysis.findUsesForward(curBody, newListStmt, listLocal);
		for (UnitValueBoxPair listUse : listUses) {
			Unit listUseUnit = listUse.unit;
			Stmt listUseStmt = (Stmt) listUseUnit;
			if (!listUseStmt.containsInvokeExpr())
				continue;
			InvokeExpr invokeExpr = listUseStmt.getInvokeExpr();
			
			if (handledStmts.contains(listUseStmt))
				continue;
			
			// filtering (listLocal should not be a parameter)
			boolean ignore = false;
			for (Value paramValue : invokeExpr.getArgs()) {
				if (paramValue == listLocal) {
					ignore = true;
					break;
				}
			}
			if (ignore == true)
				continue;
				
			// for copy
			if ((invokeExpr.getMethod().getName().equals("<init>")
			 || invokeExpr.getMethod().getName().equals("addAll")
			 || invokeExpr.getMethod().getName().equals("putAll"))
			 && invokeExpr.getArgCount() > 0) {
				if (isDebug) { System.out.println("\t\t\tList-Copy: " + listUseUnit); }
				SootClass listClass = invokeExpr.getMethod().getDeclaringClass();
				for (int paramIdx = 0; paramIdx < invokeExpr.getArgCount(); paramIdx++) {
					Type paramType = invokeExpr.getMethod().getParameterType(paramIdx);
					if (isBasicType(paramType))
						continue;
					SootClass paramClass = Scene.v().getSootClass(paramType.toString());
					boolean isCopyTarget = false;
					if (isCopyTarget == false) {
						if (paramClass.toString().equals("java.util.List")) {
							isCopyTarget = true;
						}
					}
					if (isCopyTarget == false) {
						try {
							isCopyTarget = Scene.v().getActiveHierarchy().isClassSubclassOfIncluding(paramClass, listClass);
						} catch (Exception e) { isCopyTarget = false; }
					}
					if (isCopyTarget == false) {
						try {
							isCopyTarget = Scene.v().getActiveHierarchy().isClassSubclassOfIncluding(listClass, paramClass);
						} catch (Exception e) { isCopyTarget = false; }
					}
					if (isCopyTarget == false) {
						try {
							isCopyTarget = Scene.v().getActiveHierarchy().isInterfaceSubinterfaceOf(paramClass, listClass);
						} catch (Exception e) { isCopyTarget = false; }
					}
					if (isCopyTarget == false) {
						try {
							isCopyTarget = Scene.v().getActiveHierarchy().isInterfaceSubinterfaceOf(listClass, paramClass);
						} catch (Exception e) { isCopyTarget = false; }
					}
					
					if (isCopyTarget == true) {
						Value copyTarget = invokeExpr.getArg(paramIdx);
						if (!(copyTarget instanceof Local))
							continue;
						List<Unit> copyTargetDefs = InterProcedureVariableAnalysis.findDefs(curBody, listUseStmt, (Local) copyTarget);
						for (Unit copyTargetDef : copyTargetDefs) {
							if (!(copyTargetDef instanceof AssignStmt))
								continue;
							
							if (isDebug) { System.out.println("\t\t\t\tList-Copy-Def: " + copyTargetDef); }
							Stmt copyTargetStmt = (Stmt) copyTargetDef;
							if (!(copyTargetStmt instanceof AssignStmt))
								continue;
							Value copyListValue = ((AssignStmt) copyTargetStmt).getLeftOp();
							if (!(copyListValue instanceof Local))
								continue;
							
							// findSensitiveEntity(listUseStmt, copyTargetDef, new HashSet<Stmt>(handledStmts), orderedPath);
							findSensitiveEntity(listUseStmt, copyTargetDef, new HashSet<Stmt>(handledStmts), sensitiveFieldSet, sensitiveClassSet);
						}
					}
				}
			}
			
			// for add/append element
			if ((invokeExpr.getMethod().getName().equals("add")
			  || invokeExpr.getMethod().getName().equals("append")) 
			 && invokeExpr.getArgCount() == 1) {
				if (isDebug) { System.out.println("\t\t\tList-Use: " + listUseUnit); }
				Value elementValue = invokeExpr.getArg(0);
				if (!(elementValue instanceof Local))
					continue;
				List<Unit> elementDefs = InterProcedureVariableAnalysis.findDefs(curMethod.retrieveActiveBody(), listUseStmt, (Local) elementValue);
				for (Unit elementDef : elementDefs) {
					if (!(elementDef instanceof AssignStmt))
						continue;
					if (((AssignStmt) elementDef).getLeftOp().toString().equals("fakeLocal") || ((AssignStmt) elementDef).getRightOp().toString().equals("fakeLocal"))
						continue;
					// System.out.println("\t\t\t  Element-Def: " + elementDef); // Debug
					listElementDefs.add(elementDef);
				}
			}
			
			// for put/append element
			if ((invokeExpr.getMethod().getName().equals("put")
			  || invokeExpr.getMethod().getName().equals("append")) 
			 && invokeExpr.getArgCount() == 2) {
				if (isDebug) { System.out.println("\t\t\tMap-Use: " + listUseUnit); }
				Value elementValue = invokeExpr.getArg(1);
				if (!(elementValue instanceof Local))
					continue;
				List<Unit> elementDefs = InterProcedureVariableAnalysis.findDefs(curMethod.retrieveActiveBody(), listUseStmt, (Local) elementValue);
				for (Unit elementDef : elementDefs) {
					if (!(elementDef instanceof AssignStmt))
						continue;
					if (((AssignStmt) elementDef).getLeftOp().toString().equals("fakeLocal") || ((AssignStmt) elementDef).getRightOp().toString().equals("fakeLocal"))
						continue;
					// System.out.println("\t\t\t  Element-Def: " + elementDef); // Debug
					listElementDefs.add(elementDef);
				}
			}
		}
		
		// filtering
		if (listElementDefs.size() > (8 * 2))
			return new ArrayList<Unit>();
		
		return listElementDefs;
	}
	//
	
	private static List<Unit> handleArrayDefs(Stmt newArrayStmt, Local arrayLocal) {
		List<Unit> arrayElementDefs = new ArrayList<Unit>();
		
		SootMethod curMethod = SootEnvironment.Unit2MethodMap.get(newArrayStmt);
		List<UnitValueBoxPair> arrayUses = IntraProcedureVariableAnalysis.findUsesForward(curMethod.retrieveActiveBody(), newArrayStmt, arrayLocal);
		for (UnitValueBoxPair arrayUse : arrayUses) {
			Unit arrayUseUnit = arrayUse.unit;
			Stmt arrayUseStmt = (Stmt) arrayUseUnit;
			if (!(arrayUseStmt instanceof AssignStmt))
				continue;
			if (!(((AssignStmt) arrayUseStmt).getLeftOp() instanceof ArrayRef))
				continue;
			
			if (isDebug) { System.out.println("\t\t\tList-Use: " + arrayUseUnit); }
			Value elementValue = ((AssignStmt) arrayUseStmt).getRightOp();
			if (!(elementValue instanceof Local))
				continue;
			List<Unit> elementDefs = InterProcedureVariableAnalysis.findDefs(curMethod.retrieveActiveBody(), arrayUseStmt, (Local) elementValue);
			for (Unit elementDef : elementDefs) {
				if (!(elementDef instanceof AssignStmt))
					continue;
				if (((AssignStmt) elementDef).getLeftOp().toString().equals("fakeLocal") || ((AssignStmt) elementDef).getRightOp().toString().equals("fakeLocal"))
					continue;
				// System.out.println("\t\t\t  Element-Def: " + elementDef); // Debug
				arrayElementDefs.add(elementDef);
			}
		}
		
		// filtering
		if (arrayElementDefs.size() > (8 * 2))
			return new ArrayList<Unit>();
		
		return arrayElementDefs;
	}
	
	/*
	private static void handleMapDefs(Stmt newMapStmt, Local mapLocal) {
		SootMethod curMethod = SootEnvironment.Unit2MethodMap.get(newMapStmt);
		List<UnitValueBoxPair> mapUses = IntraProcedureVariableAnalysis.findUsesForward(curMethod.retrieveActiveBody(), newMapStmt, mapLocal);
		for (UnitValueBoxPair mapUse : mapUses) {
			Unit mapUseUnit = mapUse.unit;
			Stmt mapUseStmt = (Stmt) mapUseUnit;
			if (!mapUseStmt.containsInvokeExpr())
				continue;
			InvokeExpr putExpr = mapUseStmt.getInvokeExpr();
			if (!putExpr.getMethod().getName().equals("put"))
				continue;
			if (putExpr.getArgCount() != 2)
				continue;
			System.out.println("\t\t\tMap-Use: " + mapUseUnit);
			Value elementValue = putExpr.getArg(1);
			if (!(elementValue instanceof Local))
				continue;
			List<Unit> elementDefs = InterProcedureVariableAnalysis.findDefs(curMethod.retrieveActiveBody(), mapUseStmt, (Local) elementValue);
			for (Unit elementDef : elementDefs) {
				System.out.println("\t\t\t  Element-Def: " + elementDef);
			}
		}
	}
	*/
	
	private static boolean aliasTypeCheck(Type type1, Type type2) {
		// simple case
		if (type1.toString().equals(type2.toString()))
			return true;
		// machine/atomic types
		// byte
		if ((type1.toString().equals("byte") || type1.toString().equals("java.lang.Byte"))
		 && (type2.toString().equals("byte") || type2.toString().equals("java.lang.Byte")))
			return true;
		// short
		if ((type1.toString().equals("short") || type1.toString().equals("java.lang.Short"))
		 && (type2.toString().equals("short") || type2.toString().equals("java.lang.Short")))
			return true;
		// int
		if ((type1.toString().equals("int") || type1.toString().equals("java.lang.Integer") || type1.toString().equals("java.util.concurrent.atomic.AtomicInteger"))
		 && (type2.toString().equals("int") || type2.toString().equals("java.lang.Integer") || type2.toString().equals("java.util.concurrent.atomic.AtomicInteger")))
			return true;
		// long
		if ((type1.toString().equals("long") || type1.toString().equals("java.lang.Long") || type1.toString().equals("java.util.concurrent.atomic.AtomicLong"))
		 && (type2.toString().equals("long") || type2.toString().equals("java.lang.Long") || type2.toString().equals("java.util.concurrent.atomic.AtomicLong")))
			return true;
		// char
		if ((type1.toString().equals("char") || type1.toString().equals("java.lang.Character"))
		 && (type2.toString().equals("char") || type2.toString().equals("java.lang.Character")))
			return true;
		// float
		if ((type1.toString().equals("float") || type1.toString().equals("java.lang.Float"))
		 && (type2.toString().equals("float") || type2.toString().equals("java.lang.Float")))
			return true;
		// double
		if ((type1.toString().equals("double") || type1.toString().equals("java.lang.Double"))
		 && (type2.toString().equals("double") || type2.toString().equals("java.lang.Double")))
			return true;
		// boolean
		if ((type1.toString().equals("boolean") || type1.toString().equals("java.lang.Boolean") || type1.toString().equals("java.util.concurrent.atomic.AtomicBoolean"))
		 && (type2.toString().equals("boolean") || type2.toString().equals("java.lang.Boolean") || type2.toString().equals("java.util.concurrent.atomic.AtomicBoolean")))
			return true;
		
		return false;
	}
	
	private static boolean isBasicType(Type type) {
		String typeString = type.toString();
		// byte
		if (typeString.equals("byte") || typeString.equals("java.lang.Byte"))
			return true;
		// short
		if (typeString.equals("short") || typeString.equals("java.lang.Short"))
			return true;
		// int
		if (typeString.equals("int") || typeString.equals("java.lang.Integer"))
			return true;
		// long
		if (typeString.equals("long") || typeString.equals("java.lang.Long"))
			return true;
		// char
		if (typeString.equals("char") || typeString.equals("java.lang.Character"))
			return true;
		// float
		if (typeString.equals("float") || typeString.equals("java.lang.Float"))
			return true;
		// double
		if (typeString.equals("double") || typeString.equals("java.lang.Double"))
			return true;
		// boolean
		if (typeString.equals("boolean") || typeString.equals("java.lang.Boolean"))
			return true;
		
		// String
		if (typeString.equals("java.lang.String"))
			return true;
		
		return false;
	}
	
	private static boolean newTypeCheck(Type type) {
		String typeRaw = type.toString();
		
		if (typeRaw.startsWith("java.util."))
			return false;
		if (typeRaw.startsWith("java.lang."))
			return false;
		if (typeRaw.startsWith("android.app."))
			return false;
		if (typeRaw.startsWith("android.content."))
			return false;
		if (typeRaw.startsWith("android.database."))
			return false;
		if (typeRaw.startsWith("android.graphics."))
			return false;
		if (typeRaw.startsWith("android.net.Uri"))
			return false;
		if (typeRaw.startsWith("android.os."))
			return false;
		if (typeRaw.startsWith("android.util."))
			return false;
		if (typeRaw.startsWith("android.view."))
			return false;
		if (typeRaw.startsWith("android.widget."))
			return false;
		if (typeRaw.startsWith("com.android.internal.util."))
			return false;
		if (typeRaw.startsWith("libcore.util."))
			return false;
		if (typeRaw.startsWith("org.json."))
			return false;
		
		// special cases
		if (typeRaw.endsWith("Builder"))
			return false;
		if (typeRaw.contains("ParceledListSlice"))
			return false;
		
		return true;
	}
	
	private static boolean refFieldCheck(SootField field) {
		if (!field.getType().toString().equals("java.lang.String") && isBasicType(field.getType()) && Modifier.isFinal(field.getModifiers()))
			return false;
		
		SootClass declareClass = field.getDeclaringClass();
		
		if (declareClass.toString().startsWith("java.util."))
			return false;
		if (declareClass.toString().startsWith("java.lang."))
			return false;
		if (declareClass.toString().startsWith("android.app."))
			return false;
		if (declareClass.toString().startsWith("android.content."))
			return false;
		if (declareClass.toString().startsWith("android.database."))
			return false;
		if (declareClass.toString().startsWith("android.graphics."))
			return false;
		if (declareClass.toString().startsWith("android.net.Uri"))
			return false;
		if (declareClass.toString().startsWith("android.os."))
			return false;
		if (declareClass.toString().startsWith("android.util."))
			return false;
		if (declareClass.toString().startsWith("android.view."))
			return false;
		if (declareClass.toString().startsWith("android.widget."))
			return false;
		if (declareClass.toString().startsWith("com.android.internal.util."))
			return false;
		if (declareClass.toString().startsWith("libcore.util."))
			return false;
		if (declareClass.toString().startsWith("org.json."))
			return false;
		
		// special cases
		if (declareClass.toString().endsWith("Builder"))
			return false;
		if (declareClass.toString().equals("com.android.server.location.provider.LocationProviderManager") && field.getName().equals("mName"))
			return false;
		
		/*
		if (declareClass.toString().equals("android.content.pm.ApplicationInfo"))
			return false;
		if (declareClass.toString().equals("com.android.server.am.UserController"))
			return false;
		*/
		
		return true;
	}
	
	/*
	private static boolean srcMethodCheck(SootMethod method) {
		SootClass declareClass = method.getDeclaringClass();
		
		if (declareClass.toString().equals("android.os.Bundle"))
			return false;
			
		return true;
	}
	*/
	
	// ---- //
	
	// module-test
	
	public static void main(String[] args) {
		SootEnvironment.init();
		SootEnvironment.buildCallgraph();
		
		innerAnalyze();
		printOutput();
	}

}
