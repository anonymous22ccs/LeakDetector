package ??.??.analysis.app;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import ??.??.analysis.IntraProcedureVariableAnalysis;
import ??.??.configure.Configure;
import ??.??.configure.SootEnvironment;
import soot.Body;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.toolkits.scalar.UnitValueBoxPair;

public class AppPermissionFinder {
	
	private static void innerAnalyze() {
		ArrayList<String> apk2Analyze = new ArrayList<String>(); // result
		
		File apkDir = new File(Configure.AppDir);
		if (!apkDir.isDirectory())
			System.err.println(String.format("[Error] %s is not a directory storing APKs????", apkDir.getAbsolutePath()));
		
		File[] apkFiles = apkDir.listFiles();
		Arrays.sort(apkFiles);
		
		int apkIdx = 0;
		for (File apkFile : apkFiles) {
			String apkPath = apkFile.getAbsolutePath();
			
			apkIdx++;
			if (!apkFile.exists()) {
				System.err.println(String.format("[%d/%d] Error: APK %s does not exist????", apkIdx, apkFiles.length, apkPath));
				continue;
			}
			
			// -->> start analyze
			
			// init Soot
			try {
				SootEnvironment.initForAPK(apkPath);
			} catch (Exception e) {
				System.err.println(String.format("[%d/%d] Error: init Soot fail for APK %s????", apkIdx, apkFiles.length, apkPath));
				continue;
			}
			
			System.out.println(String.format("[%d/%d] Debug: analyzing APK %s", apkIdx, apkFiles.length, apkPath));
			
			// heuristic filtering
			boolean reqPermission = false;
			for (SootClass sootClass : Scene.v().getClasses()) {
				if (!sootClass.isConcrete())
					continue;
				for (SootMethod sootMethod : sootClass.getMethods()) {
					if (!sootMethod.isConcrete())
						continue;
					Body body = sootMethod.retrieveActiveBody();
					for (Unit unit : body.getUnits()) {
						Stmt stmt = (Stmt) unit;
						if (!stmt.containsInvokeExpr())
							continue;
						SootMethod calleeMethod = stmt.getInvokeExpr().getMethod();
						SootClass calleeClass = calleeMethod.getDeclaringClass();
						if (calleeClass.getName().startsWith("android.")
						 || calleeClass.getName().startsWith("androidx.")
						 || calleeClass.getName().startsWith("com.android.")) {
							if ((calleeMethod.getName().contains("request") || calleeMethod.getName().contains("Request"))
							 && (calleeMethod.getName().contains("permissions") || calleeMethod.getName().contains("Permissions"))) {
								reqPermission = true;
								break;
							}
						}
					}
					if (reqPermission == true)
						break;
				}
				if (reqPermission == true)
					continue;
			}
			if (apkPath.contains("Bluetooth.apk")
			 || apkPath.contains("TeleService.apk")
			 || apkPath.contains("Telecom.apk")) {
				reqPermission = false;
			}
			if (reqPermission == true) {
				System.out.println(String.format("[%d/%d] Debug: APK %s calls reqPermission, ignore...", apkIdx, apkFiles.length, apkPath));
				continue;
			}
			
			// method -> permissions
			HashMap<SootMethod, HashSet<String>> method2permissions = new HashMap<SootMethod, HashSet<String>>();
			innerPermissionAnalyze(method2permissions);
			// check
			for (SootMethod method : new ArrayList<SootMethod>(method2permissions.keySet())) {
				if (!method2permissions.containsKey(method))
					continue;
				
				System.out.println("\t" + method.getSignature());
				for (String permission : method2permissions.get(method)) {
					System.out.println("\t\t" + permission);
				}
				
				// heuristic filtering
				// (1-a)
				if (method.getName().equals("<init>") || method.getName().equals("<clinit>")) {
					method2permissions.remove(method);
					System.out.println("\t" + "---- find ignore case ----");
					continue;
				}
				// (1-b)
				for (SootClass sootClass : Scene.v().getClasses()) {
					if (!sootClass.isConcrete())
						continue;
					for (SootMethod sootMethod : sootClass.getMethods()) {
						if (!sootMethod.isConcrete())
							continue;
						Body body = sootMethod.retrieveActiveBody();
						for (Unit unit : body.getUnits()) {
							Stmt stmt = (Stmt) unit;
							if (!stmt.containsInvokeExpr())
								continue;
							SootMethod calleeMethod = stmt.getInvokeExpr().getMethod();
							if (calleeMethod.getSignature().equals(method.getSignature())
							 && (sootMethod.getName().equals("<init>") || sootMethod.getName().equals("<clinit>"))) {
								method2permissions.remove(method);
								System.out.println("\t" + "---- find ignore case ----");
								break;
							}
						}
					}
					if (!method2permissions.containsKey(method))
						break;
				}
				// (2-a)
				//
				if (method.getName().equals("onCreate")) {
					method2permissions.clear();
					System.out.println("\t" + "xxxx find error case xxxx");
					continue;
				}
				//
				// (2-b)
				//
				for (SootClass sootClass : Scene.v().getClasses()) {
					if (!sootClass.isConcrete())
						continue;
					for (SootMethod sootMethod : sootClass.getMethods()) {
						if (!sootMethod.isConcrete())
							continue;
						Body body = sootMethod.retrieveActiveBody();
						for (Unit unit : body.getUnits()) {
							Stmt stmt = (Stmt) unit;
							if (!stmt.containsInvokeExpr())
								continue;
							SootMethod calleeMethod = stmt.getInvokeExpr().getMethod();
							if (calleeMethod.getSignature().equals(method.getSignature())
							 && (sootMethod.getName().equals("onCreate"))) {
								method2permissions.clear();
								System.out.println("\t" + "xxxx find error case xxxx" + " " + sootMethod.getSignature());
								break;
							}
						}
					}
					if (!method2permissions.containsKey(method))
						break;
				}
				//
			}
			
			if (!method2permissions.keySet().isEmpty())
				apk2Analyze.add(apkPath);
		}
		
		// Debug output
		for (String apkPath : apk2Analyze)
			System.out.println(String.format("[Debug] %s", apkPath));
	}
	
	// copy from PermissionFinder.java
	private static void innerPermissionAnalyze(HashMap<SootMethod, HashSet<String>> method2permissions) {
		HashMap<SootMethod, HashSet<Unit>> method2permissionUnit = new HashMap<>(); // method => units that consume permission strings
		HashMap<Unit, HashSet<String>> unit2permissions = new HashMap<>(); // unit => consumed permission strings
		
		// Step-0: find non-framework related APKs by finding permission request methods
		boolean ignoreAPK = false;
		for (SootClass sootClass : new ArrayList<SootClass>(Scene.v().getClasses())) {
			if (sootClass.isPhantom())
				continue;
			if (sootClass.isLibraryClass())
				continue;
			if (sootClass.getName().startsWith("android.")
			 || sootClass.getName().startsWith("androidx.")
			 || sootClass.getName().startsWith("com.android."))
				continue;
			for (SootMethod sootMethod : new ArrayList<SootMethod>(sootClass.getMethods())) {
				if (!sootMethod.isConcrete())
					continue;
				Body body = sootMethod.retrieveActiveBody();
				for (Unit unit : body.getUnits()) {
					Stmt stmt = (Stmt) unit;
					if (!stmt.containsInvokeExpr())
						continue;
					SootMethod tgtMethod = stmt.getInvokeExpr().getMethod();
					if ((tgtMethod.getName().contains("permissions") || tgtMethod.getName().contains("Permissions"))
					 && (tgtMethod.getName().contains("request") || tgtMethod.getName().contains("Request"))) {
						System.err.println(String.format("%s in (%s)", stmt, sootMethod.getSignature()));
						ignoreAPK = true;
						break;
					}
				}
				if (ignoreAPK == true)
					break;
			}
			if (ignoreAPK == true)
				break;
		}
		if (ignoreAPK == true)
			return;
		
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
								if (argString.contains("INTERACT_ACROSS_USERS")) // ignore the special permission
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
							} else if (rhsString.contains("INTERACT_ACROSS_USERS")) {
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
			// System.out.println(sootMethod.getSignature()); // Debug
			for (Unit unit : method2permissionUnit.get(sootMethod)) {
				Stmt stmt = (Stmt) unit;
				if (permissionCheckSet.contains(stmt.getInvokeExpr().getMethod())) {
					// System.out.println("\tYES: " + unit);
					HashSet<String> permissions = unit2permissions.get(unit);
					for (String permission : permissions) {
						// System.out.println("\t\t" + permission);
						if (!method2permissions.containsKey(sootMethod))
							method2permissions.put(sootMethod, new HashSet<String>());
						method2permissions.get(sootMethod).add(permission);
					}
				} else {
					// System.out.println("\t NO: " + unit);
				}
			}
		}
	}
	
	// ---- //
	
	public static void main(String[] args) {
		innerAnalyze();
	}

}
