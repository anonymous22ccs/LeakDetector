package ??.??.analysis.app;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

import ??.??.analysis.CallgraphAnalysis;
import ??.??.analysis.IntentAnalysis;
import ??.??.analysis.IntentFilterAnalysis;
import ??.??.analysis.InterProcedureVariableAnalysis;
import ??.??.analysis.IntraProcedureVariableAnalysis;
import ??.??.analysis.LeakDetector;
import ??.??.analysis.PermissionFinder;
import ??.??.configure.Configure;
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
import soot.jimple.AssignStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.NewExpr;
import soot.jimple.NullConstant;
import soot.jimple.ReturnStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.scalar.UnitValueBoxPair;

public class AppIntentAnalysis {
	// output
	// method -> Intent.<init>
	public static HashMap<SootMethod, ArrayList<Unit>> method2intentInitMap = new HashMap<SootMethod, ArrayList<Unit>>();
	// Intent.<init> -> Intent.putExtra
	public static HashMap<Unit, ArrayList<Unit>> intentInit2putExtraMap = new HashMap<Unit, ArrayList<Unit>>();
	// Intent.putExtra -> class's field that has data dependence with extra
	public static HashMap<Unit, HashSet<SootField>> putExtra2fieldMap = new HashMap<Unit, HashSet<SootField>>();
	// Intent.putExtra -> method that returns extra
	public static HashMap<Unit, HashSet<SootMethod>> putExtra2srcMethodMap = new HashMap<Unit, HashSet<SootMethod>>();
	// Intent.putExtra -> class
	public static HashMap<Unit, HashSet<SootClass>> putExtra2classMap = new HashMap<Unit, HashSet<SootClass>>();
	// Intent.putExtra -> actionName
	public static HashMap<Unit, HashSet<String>> putExtra2actionMap = new HashMap<Unit, HashSet<String>>();
	// ----
	
	private static void printOutput() {
		for (SootMethod sootMethod : method2intentInitMap.keySet()) {
			System.out.println("Method: " + sootMethod.getSignature());
			ArrayList<Unit> intentInitUnits = method2intentInitMap.get(sootMethod);
			if (intentInitUnits == null)
				intentInitUnits = new ArrayList<Unit>();
			for (Unit intentInitUnit : intentInitUnits) {
				System.out.println("\tIntent.<init>: " + intentInitUnit);
				ArrayList<Unit> putExtraUnits = intentInit2putExtraMap.get(intentInitUnit);
				if (putExtraUnits == null)
					putExtraUnits = new ArrayList<Unit>();
				for (Unit putExtraUnit : putExtraUnits) {
					System.out.println("\t\tIntent.putExtra: " + putExtraUnit);
					HashSet<SootField> extraDepFields = putExtra2fieldMap.get(putExtraUnit);
					if (extraDepFields == null)
						extraDepFields = new HashSet<SootField>();
					for (SootField extraDepField : extraDepFields) {
						System.out.println("\t\t\tExtra-Dep: " + extraDepField.toString());
					}
					HashSet<SootMethod> extraDepMethods = putExtra2srcMethodMap.get(putExtraUnit);
					if (extraDepMethods == null)
						extraDepMethods = new HashSet<SootMethod>();
					for (SootMethod extraDepMethod : extraDepMethods) {
						System.out.println("\t\t\tExtra-Src: " + extraDepMethod.getSignature());
					}
				}
			}
		}
	}
	
	// exported interface
	public static void analyze() {
		// read paths of APK files to be ignored
		ArrayList<String> apkList = new ArrayList<String>();
		File apkLst = new File(Configure.AppLst);
		if (apkLst.exists()) {
			BufferedReader br = null;
			try {
				br = new BufferedReader(new FileReader(apkLst));
				String line = null;
				while((line = br.readLine()) != null) {
					String apkPath = line.split(" ")[1].trim();
					if (apkPath.endsWith(".apk"))
						apkList.add(apkPath);
				}
			} catch (Exception e) { 
				// do nothing
			}
			
			try {
				br.close();
			} catch (Exception e) {
				// do nothing
			}
		}
		// apkList = new ArrayList<String>(); // do not ignore
		
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
			// if (apkList.contains(apkPath)) {
			if (!apkList.contains(apkPath)) {
				System.err.println(String.format("[%d/%d] Ignore: APK %s", apkIdx, apkFiles.length, apkPath));
				continue;
			}
			
			// Test
			// if (!apkPath.contains("SamsungMessages"))
				// continue;
			
			// Test
			if (apkIdx <= 107) {
				// System.err.println(String.format("[%d/%d] Ignore: APK %s", apkIdx, apkFiles.length, apkPath));
				// continue;
			}
			
			Long startProcess1 = System.nanoTime();
			
			try {
				SootEnvironment.initForAPK(apkPath);
			} catch (Exception e) {
				System.err.println(String.format("[%d/%d] Error: init Soot fail for APK %s????", apkIdx, apkFiles.length, apkPath));
				continue;
			}
			
			System.out.println(String.format("[%d/%d] Debug: analyzing APK %s", apkIdx, apkFiles.length, apkPath));
			SootEnvironment.buildApkCallgraph();
		
			Long endProcess1 = System.nanoTime();
			LeakDetector.time4Process1 += (endProcess1 - startProcess1);
			
			// parse manifest
			AppManifestAnalysis.analyze(apkPath);
			
			LeakDetector.time4Process2 += 0; // no Process-2
			
			Long startProcess3 = System.nanoTime();
			
			method2intentInitMap = new HashMap<SootMethod, ArrayList<Unit>>(); // reset
			intentInit2putExtraMap = new HashMap<Unit, ArrayList<Unit>>(); // reset
			putExtra2fieldMap = new HashMap<Unit, HashSet<SootField>>(); // reset
			putExtra2srcMethodMap = new HashMap<Unit, HashSet<SootMethod>>(); // reset
			putExtra2classMap = new HashMap<Unit, HashSet<SootClass>>(); // reset
			putExtra2actionMap = new HashMap<Unit, HashSet<String>>(); // reset
			analyzeInner();
			// printOutput();
			
			Long endProcess3 = System.nanoTime();
			LeakDetector.time4Process3 += (endProcess3 - startProcess3);
			
			// ---->>>> copy from LeakDetector.java
			
			// collect leaked fields
			HashSet<SootField> appLeakedFields = new HashSet<SootField>();
			for (Unit putExtraUnit : putExtra2fieldMap.keySet()) {
				appLeakedFields.addAll(putExtra2fieldMap.get(putExtraUnit));
				// for (SootField sootField : appLeakedFields) {
					// System.out.println(String.format("[Debug] SootField %s in (%s)", sootField, putExtraUnit)); // Debug
				// }
			}
			for (SootField leakedField : appLeakedFields) {
				for (SootField recordedField : PermissionFinder.field2paths.keySet()) {
					if (leakedField.toString().equals(recordedField.toString())) {
						System.out.println("Leaked Field: " + leakedField);
						// details about leaked Intent
						for (Unit putExtraUnit : putExtra2fieldMap.keySet()) {
							if (putExtra2fieldMap.get(putExtraUnit).contains(leakedField)) {
								for (String actionName : putExtra2actionMap.get(putExtraUnit))
									System.out.println("\tIntent: " + putExtraUnit + ", Action: " + actionName + " in [ " + SootEnvironment.Unit2MethodMap.get(putExtraUnit).getSignature() + "]");
							}
						}
						// details about leaked Field
						HashSet<ArrayList<SootMethod>> paths = PermissionFinder.field2paths.get(recordedField);
						int pathIdx = 1;
						for (ArrayList<SootMethod> path : paths) {
							int pathLength = path.size();
							for (SootMethod pathElement : path) {
								System.out.println(String.format("\t[Path-%d] %s", pathIdx, pathElement.getSignature()));
							}
							System.out.println("\t[Permission]");
							HashSet<String> permissions = PermissionFinder.method2permissions.get(path.get(pathLength - 1));
							for (String permission : permissions) {
								System.out.println("\t\t" + permission);
							}
							pathIdx++;
						}
						
						break;
					}
				}
			}
					
			// collect leaked src methods
			// HashSet<SootMethod> appLeakedMethods = new HashSet<SootMethod>();
			// for (Unit putExtraUnit : putExtra2srcMethodMap.keySet()) {
				// appLeakedMethods.addAll(putExtra2srcMethodMap.get(putExtraUnit));
				// for (SootMethod sootMethod : appLeakedMethods) {
					// System.out.println(String.format("[Debug] SootMethod %s in (%s)", sootMethod, putExtraUnit)); // Debug
				// }
			// }
			// for (SootMethod leakedMethod : appLeakedMethods) {
				// for (SootMethod recordedMethod : PermissionFinder.srcMethod2paths.keySet()) {
					// if (leakedMethod.toString().equals(recordedMethod.toString())) {
						// System.out.println("Leaked Method: " + leakedMethod);
						// break;
					// }
				// }
			// }
					
			// collect leaked classes 
			HashSet<SootClass> appLeakedClasses = new HashSet<SootClass>();
			for (Unit putExtraUnit : putExtra2classMap.keySet()) {
				appLeakedClasses.addAll(putExtra2classMap.get(putExtraUnit));
				// for (SootClass sootClass : appLeakedClasses) {
					// System.out.println(String.format("[Debug] SootClass %s in (%s)", sootClass, putExtraUnit)); // Debug
				// }
			}
			for (SootClass leakedClass : appLeakedClasses) {
				for (SootClass recordedClass : PermissionFinder.class2paths.keySet()) {
					if (leakedClass.toString().equals(recordedClass.toString())) {
						System.out.println("Leaked Class: " + leakedClass);
						// details about leaked Intent
						for (Unit putExtraUnit : putExtra2classMap.keySet()) {
							if (putExtra2classMap.get(putExtraUnit).contains(leakedClass)) {
								for (String actionName : putExtra2actionMap.get(putExtraUnit))
									System.out.println("\tIntent: " + putExtraUnit + ", Action: " + actionName + " in [ " + SootEnvironment.Unit2MethodMap.get(putExtraUnit).getSignature() + "]");
							}
						}
						// details about leaked Class
						HashSet<ArrayList<SootMethod>> paths = PermissionFinder.class2paths.get(recordedClass);
						int pathIdx = 1;
						for (ArrayList<SootMethod> path : paths) {
							int pathLength = path.size();
							for (SootMethod pathElement : path) {
								System.out.println(String.format("\t[Path-%d] %s", pathIdx, pathElement.getSignature()));
							}
							System.out.println("\t[Permission]");
							HashSet<String> permissions = PermissionFinder.method2permissions.get(path.get(pathLength - 1));
							for (String permission : permissions) {
								System.out.println("\t\t" + permission);
							}
							pathIdx++;
						}
						
						break;
					}
				}
			}
			
			Long endProcess4 = System.nanoTime();
			LeakDetector.time4Process4 += (endProcess4 - endProcess3);
			
			// find privileged Intent
			IntentFilterAnalysis.analyze();
			
			//
			for (SootClass sootClass : Scene.v().getClasses()) {
				LeakDetector.classSet.add(sootClass.getName());
				for (SootMethod sootMethod : sootClass.getMethods()) {
					LeakDetector.methodSet.add(sootMethod.getSignature());
				}
			}
		}
	}
	
	private static void analyzeInner() {
		CallGraph cg = Scene.v().getCallGraph();
		
		// Step-1: find Intent constructors that do not specify target
		ArrayList<SootMethod> IntentInitMethods = new ArrayList<SootMethod>(); // only includes 
		SootClass IntentClass = Scene.v().getSootClass("android.content.Intent");
		for (SootMethod method : IntentClass.getMethods()) {
			if (!method.getName().equals("<init>"))
				continue;
			boolean hasTarget = false;
			for (Type paramType : method.getParameterTypes()) {
				if (paramType.toString().equals("android.content.Context") 
				 || paramType.toString().equals("java.lang.Class")
				 || paramType.toString().equals("android.content.Intent")) {
					hasTarget = true;
					break;
				}
			}
			
			if (hasTarget == false) {
				// System.out.println(method.toString()); // Debug
				IntentInitMethods.add(method);
			}
		}
		
		// 
		int analyzeIdx = 1;
		for (SootClass sootClass : new ArrayList<SootClass>(Scene.v().getClasses())) {
			if (sootClass.isPhantom())
				continue;
			if (sootClass.getName().startsWith("android.content.Intent")) // include inner classes in android.content.Intent
				continue;
			
			for (SootMethod sootMethod : new ArrayList<SootMethod>(sootClass.getMethods())) {
				if (!sootMethod.isConcrete())
					continue;
				// if(!cg.edgesInto(sootMethod).hasNext())
					// continue; // ignore unreachable method (bug: lifecycle method)
				
				Body body = sootMethod.retrieveActiveBody();
				
				// Test
				// if (sootMethod.getSignature().equals("<com.android.server.adb.AdbDebuggingManager$AdbDebuggingHandler: void sendServerConnectionState(boolean,int)>")) {
				// if (sootMethod.getSignature().equals("<com.android.server.telecom.TtyManager: void updateCurrentTtyMode()>")) {
				// if (sootMethod.getSignature().equals("<com.android.server.wifi.ClientModeManager: void updateConnectModeState(int,int)>")) {
				// if (sootMethod.getSignature().equals("<com.android.internal.telephony.GsmCdmaPhone: void sendEmergencyCallbackModeChange()>")) {
				// if (sootMethod.getSignature().equals("<com.android.internal.telephony.imsphone.ImsPhone: void sendEmergencyCallbackModeChange()>")) {
				// if (sootMethod.getSignature().equals("<com.android.server.wifi.SoftApManager: void updateApState(int,int,int)>")) {
				if (sootMethod.getSignature().equals("<com.android.server.wifi.ConcreteClientModeManager: void updateConnectModeState(com.android.server.wifi.ActiveModeManager$ClientRole,int,int)>")) {
					// System.out.println(body); // Debug
				} else {
					// continue;
				}
				
				for (Unit unit : body.getUnits()) {
					Stmt stmt = (Stmt) unit;
					if (!stmt.containsInvokeExpr())
						continue;
					
					// Debug
					// CallGraph cg = Scene.v().getCallGraph();
					// Iterator<Edge> edgeIterator = cg.edgesOutOf(unit);
					// System.out.println("Unit: " + unit);
					// while (edgeIterator.hasNext()) {
						// Edge edge = edgeIterator.next();
						// System.out.println("  Edge: " + edge);
					// }
					
					InvokeExpr invokeExpr = stmt.getInvokeExpr();
					if (!IntentInitMethods.contains(invokeExpr.getMethod()))
						continue;
					if (!(invokeExpr instanceof SpecialInvokeExpr))
						continue;
					Value intentValue = ((SpecialInvokeExpr) invokeExpr).getBase();
					if (!(intentValue instanceof Local))
						continue;
					
					// System.out.println(String.format("[ %s ] in %s", stmt, sootMethod.getSignature())); // Debug
					
					boolean hasTarget = false;
					boolean hasDefaultTarget = false; // default package can be set by users
					boolean hasData = false;
					ArrayList<Unit> putExtraUnits = new ArrayList<Unit>();
					boolean hasSetAction = false;
					String actionName = "";
					boolean requirePermission = false;
					boolean shouldFilter = false;
					
					// boolean forResult = false;
					boolean setResult = false;
					
					List<UnitValueBoxPair> intentUses = new ArrayList<UnitValueBoxPair>();
					List<UnitValueBoxPair> intentIntraUses = IntraProcedureVariableAnalysis.findUsesForward(body, stmt, (Local) intentValue);
					List<UnitValueBoxPair> intentInterUses = new ArrayList<UnitValueBoxPair>();
					for (UnitValueBoxPair intentIntraUse : intentIntraUses) {
						// System.out.println(String.format("\tIntra-Use: %s in %s", intentIntraUse.unit, SootEnvironment.Unit2MethodMap.get(intentIntraUse.unit))); // Debug
						if (!intentUses.contains(intentIntraUse))
							intentUses.add(intentIntraUse);
							
						Unit intraUseUnit = intentIntraUse.unit;
						if (!(intraUseUnit instanceof ReturnStmt))
							continue;
						
						// perform simple inter-procedure analysis
						Iterator<Edge> intentUseEdges = cg.edgesInto(sootMethod);
						int edgeCount = 0;
						while (intentUseEdges.hasNext()) {
							intentUseEdges.next();
							edgeCount++;
						}
						if (edgeCount > 8) { // see InterProcedureVariableAnalysis.maxTgtNumber
							// 
						} else {
							intentUseEdges = cg.edgesInto(sootMethod); // reset
						}
						
						while (intentUseEdges.hasNext()) {
							Edge intentUseEdge = intentUseEdges.next();
							Unit intentUseUnit = intentUseEdge.srcUnit();
							if (intentUseUnit == null)
								continue;
							if (!(intentUseUnit instanceof AssignStmt))
								continue;
							Value intentAssignee = ((AssignStmt) intentUseUnit).getLeftOp();
							if (!(intentAssignee instanceof Local))
								continue;
							List<UnitValueBoxPair> interUses = IntraProcedureVariableAnalysis.findUsesForward(intentUseEdge.src().retrieveActiveBody(), (Stmt) intentUseUnit, (Local) intentAssignee);
							for (UnitValueBoxPair intentInterUse : interUses) {
								// System.out.println(String.format("\tInter-Use: %s in %s", intentInterUse.unit, SootEnvironment.Unit2MethodMap.get(intentInterUse.unit))); // Debug
								if (!intentInterUses.contains(intentInterUse))
									intentInterUses.add(intentInterUse);
								if (!intentUses.contains(intentInterUse))
									intentUses.add(intentInterUse);
							}
						}
					}
					
					// analyze Intent.setPackage
					for (UnitValueBoxPair intentUse : intentUses) {
						Unit useUnit = intentUse.unit;
						Stmt useStmt = (Stmt) useUnit;
						if (!useStmt.containsInvokeExpr())
							continue;
						if (!useStmt.getInvokeExpr().getMethod().getName().equals("setPackage"))
							continue;
						hasTarget = true;
						hasDefaultTarget = isDefaultPackage(useUnit);
						if (hasDefaultTarget == true)
							break;
					}
					
					// analyze Intent.****
					for (UnitValueBoxPair intentUse : intentUses) {
						Unit useUnit = intentUse.unit;
						Stmt useStmt = (Stmt) useUnit;
						// System.out.println(String.format("\tDef-Analysis: %s", useStmt)); // Debug
						// conservatively
						if (!useStmt.containsInvokeExpr())
							continue;
						if (useStmt.getInvokeExpr().getMethod().getName().equals("setClass")
						 || useStmt.getInvokeExpr().getMethod().getName().equals("setClassName")
						 || useStmt.getInvokeExpr().getMethod().getName().equals("setComponent"))
							hasTarget = true;
						// if (useStmt.getInvokeExpr().getMethod().getName().startsWith("setData")
						//  && useStmt.getInvokeExpr().getArgCount() == 1) {
						// 	hasData = true;
						// 	putExtraUnits.add(useStmt);
						// }
						// putExtra
						if (useStmt.getInvokeExpr().getMethod().getName().startsWith("put")
						 && useStmt.getInvokeExpr().getMethod().getName().endsWith("Extra")
						 && useStmt.getInvokeExpr().getArgCount() == 2) {
							hasData = true;
							putExtraUnits.add(useStmt);
						}
						// action related
						if (!invokeExpr.getMethod().getSignature().equals("<android.content.Intent: void <init>()>")) {
							if (invokeExpr.getMethod().getParameterType(0).toString().equals("java.lang.String")) {
								Value actionValue = invokeExpr.getArg(0);
								if (actionValue instanceof StringConstant) {
									actionName = ((StringConstant) actionValue).value;
									if (!actionName.equals(""))
										hasSetAction = true;
								}
								if (actionValue instanceof Local) {
									for (Unit actionDef : InterProcedureVariableAnalysis.findDefs(SootEnvironment.Unit2MethodMap.get(unit).retrieveActiveBody(), stmt, (Local) actionValue)) {
										if (!(actionDef instanceof AssignStmt))
											continue;
										if (((AssignStmt) actionDef).getRightOp() instanceof StringConstant) {
											actionName = ((StringConstant) ((AssignStmt) actionDef).getRightOp()).value;
											if (!actionName.equals(""))
												hasSetAction = true;
										}
										
										if (hasSetAction == true)
											break;
									}
								}
								
								if ((hasSetAction == true) 
								 && (actionName.contains("action.VIEW") || actionName.contains("action.SEND") || actionName.contains("action.SENDTO")))
									hasSetAction = false;
							}
						}
						if (useStmt.getInvokeExpr().getMethod().getName().startsWith("setAction")) {
							if (useStmt.getInvokeExpr().getMethod().getParameterType(0).toString().equals("java.lang.String")) {
								Value actionValue = useStmt.getInvokeExpr().getArg(0);
								if (actionValue instanceof StringConstant) {
									actionName = ((StringConstant) actionValue).value;
									if (!actionName.equals(""))
										hasSetAction = true;
								}
								if (actionValue instanceof Local) {
									for (Unit actionDef : InterProcedureVariableAnalysis.findDefs(SootEnvironment.Unit2MethodMap.get(useUnit).retrieveActiveBody(), useStmt, (Local) actionValue)) {
										if (!(actionDef instanceof AssignStmt))
											continue;
										if (((AssignStmt) actionDef).getRightOp() instanceof StringConstant) {
											actionName = ((StringConstant) ((AssignStmt) actionDef).getRightOp()).value;
											if (!actionName.equals(""))
												hasSetAction = true;
										}
										
										if (hasSetAction == true)
											break;
									}
								}
								
								if ((hasSetAction == true) 
								 && (actionName.contains("action.VIEW") || actionName.contains("action.SEND") || actionName.contains("action.SENDTO")))
									hasSetAction = false;
							}
						}
						// permission related
						if (useStmt.getInvokeExpr().getMethod().getName().contains("permission")
						 || useStmt.getInvokeExpr().getMethod().getName().contains("Permission"))
							requirePermission = true;
						for (Value useStmtArg : useStmt.getInvokeExpr().getArgs()) {
							if ((useStmtArg instanceof StringConstant) && ((StringConstant) useStmtArg).value.contains(".permission."))
								requirePermission = true;
							if (useStmtArg instanceof Local) {
								List<UnitValueBoxPair> argUses = IntraProcedureVariableAnalysis.findUsesBckward(body, useStmt, (Local) useStmtArg);
								for (UnitValueBoxPair argUse : argUses) {
									Unit argUseUnit = argUse.getUnit();
									if (!(argUseUnit instanceof AssignStmt))
										continue;
									Value argUseRhs = ((AssignStmt) argUseUnit).getRightOp();
									if (argUseRhs.toString().contains("permission")
									 || argUseRhs.toString().contains("Permission"))
										requirePermission = true;
								}
							}
						}
						if (requirePermission == false 
						 && useStmt.getInvokeExpr().getMethod().getDeclaringClass().getName().contains("ExternalSyntheticLambda0")) {
							boolean isIntentArg = false;
							for (Value intentArg : useStmt.getInvokeExpr().getArgs()) {
								Type intentArgType = intentArg.getType();
								if (intentArgType.toString().equals("android.content.Intent")) {
									isIntentArg = true;
									break;
								}
							}
							
							if (isIntentArg == true) {
								SootClass externalClass = useStmt.getInvokeExpr().getMethod().getDeclaringClass();
								for (SootMethod externalMethod : externalClass.getMethods()) {
									if (requirePermission == true)
										break;
									
									if (!externalMethod.isConcrete())
										continue;
									if (externalMethod.getName().equals("<init>") || externalMethod.getName().equals("<clinit>"))
										continue;
									if (externalMethod.isConstructor())
										continue;
									
									Body externalBody = externalMethod.retrieveActiveBody();
									for (Unit externalUnit : externalBody.getUnits()) {
										if (requirePermission == true)
											break;
										
										Stmt externalStmt = (Stmt) externalUnit;
										if (!externalStmt.containsInvokeExpr())
											continue;
										SootMethod externalCalleeMethod = externalStmt.getInvokeExpr().getMethod();
										if (!externalCalleeMethod.isConcrete())
											continue;
										if (externalCalleeMethod.getName().equals("<init>") || externalMethod.getName().equals("<clinit>"))
											continue;
										if (externalCalleeMethod.isConstructor())
											continue;
										
										Body externalCalleeBody = externalCalleeMethod.retrieveActiveBody();
										for (Unit externalCalleeUnit : externalCalleeBody.getUnits()) {
											if (requirePermission == true)
												break;
											
											Stmt externalCalleeStmt = (Stmt) externalCalleeUnit;
											if (!externalCalleeStmt.containsInvokeExpr())
												continue;
											for (Value externalCalleeArg : externalCalleeStmt.getInvokeExpr().getArgs()) {
												if ((externalCalleeArg instanceof StringConstant) && ((StringConstant) externalCalleeArg).value.contains(".permission.")) {
													requirePermission = true;
													break;
												}
											}
										}
									}
								}
							}
						}
						//
						// if (useStmt.getInvokeExpr().getMethod().getName().startsWith("setResult"))
						// 	shouldFilter = true;
					}
					
					// analyze startActivityForResult
					// for (UnitValueBoxPair intentUse : intentUses) {
					// 	Unit useUnit = intentUse.unit;
					// 	Stmt useStmt = (Stmt) useUnit;
					// 	if (!useStmt.containsInvokeExpr())
					// 		continue;
					// 	if (!useStmt.getInvokeExpr().getMethod().getName().equals("startActivityForResult"))
					// 		continue;
					// 	forResult = true;
					// }
					
					// analyze setResult
					for (UnitValueBoxPair intentUse : intentUses) {
						Unit useUnit = intentUse.unit;
						Stmt useStmt = (Stmt) useUnit;
						if (!useStmt.containsInvokeExpr())
							continue;
						if (!useStmt.getInvokeExpr().getMethod().getName().startsWith("setResult"))
							continue;
						setResult = true;
					}
					
					// Debug
					if ((hasTarget == false /* || (hasTarget == true && hasDefaultTarget == true) */ ) 
					 && hasData == true && requirePermission == false && shouldFilter == false 
					 && (hasSetAction == true || setResult == true)) {
						// System.out.println(String.format("[ %d-%s ] in %s", analyzeIdx++, stmt, sootMethod.getSignature())); // Debug
						
						boolean willSend = analyzeIntentSender(intentUses);
						// willSend = false; // Test
						if (willSend == false)
							continue;
						
						System.out.println(String.format("[ %d-%s ] in %s", analyzeIdx++, stmt, sootMethod.getSignature())); // Debug
						
						// fill in method2intentInitMap
						if (!method2intentInitMap.containsKey(sootMethod))
							method2intentInitMap.put(sootMethod, new ArrayList<Unit>());
						method2intentInitMap.get(sootMethod).add(unit);
						// ----
						
						for (UnitValueBoxPair intentUse : intentUses) {
							Unit useUnit = intentUse.unit;
							Stmt useStmt = (Stmt) useUnit;
							System.out.println(String.format("\tIntent-Use: %s", useUnit)); // Debug
							if (putExtraUnits.contains(useUnit)) {
								Value putExtraValue = null;
								if (useStmt.getInvokeExpr().getArgCount() == 1)
									putExtraValue = useStmt.getInvokeExpr().getArg(0);
								else
									putExtraValue = useStmt.getInvokeExpr().getArg(1);
								if (!(putExtraValue instanceof Local))
									continue;
								
								// fill in intentInit2putExtraMap
								if (!intentInit2putExtraMap.containsKey(unit))
									intentInit2putExtraMap.put(unit, new ArrayList<Unit>());
								intentInit2putExtraMap.get(unit).add(useUnit);
								// ----
								
								// extra-defs
								List<Unit> extraDefs = InterProcedureVariableAnalysis.findDefs(body, useStmt, (Local) putExtraValue);
								for (Unit extraDef : new ArrayList<Unit>(extraDefs)) {
									if (!(extraDef instanceof AssignStmt)) {
										extraDefs.remove(extraDef);
										continue;
									}
									if (((AssignStmt) extraDef).getLeftOp().toString().equals("fakeLocal") || ((AssignStmt) extraDef).getLeftOp().toString().equals("fakeLocal")) {
										extraDefs.remove(extraDef);
										continue;
									}
								}
								if (extraDefs.size() > (8 * 2)) {
									System.out.println("\t\tExtra-Def Number: " + extraDefs.size()); // Debug
									continue;
								}
								
								for (Unit extraDef : extraDefs) {
									if (!(extraDef instanceof AssignStmt))
										continue;
									if (((AssignStmt) extraDef).getLeftOp().toString().equals("fakeLocal") || ((AssignStmt) extraDef).getRightOp().toString().equals("fakeLocal"))
										continue;
									
									findSensitiveExtraDefs(extraDef, putExtraValue, new HashSet<Unit>(), useUnit, actionName);
								}
								// extra-use (backward)
								List<UnitValueBoxPair> extraUsesBckward = InterProcedureVariableAnalysis.findUsesBckward(body, useStmt, (Local) putExtraValue);
								for (UnitValueBoxPair extraUse : new ArrayList<UnitValueBoxPair>(extraUsesBckward)) {
									Unit extraUseUnit = extraUse.unit;
									Stmt extraUseStmt = (Stmt) extraUseUnit;
									if (!(extraUseStmt instanceof AssignStmt) && !extraUseStmt.containsInvokeExpr()) {
										extraUsesBckward.remove(extraUse);
										continue;
									}
									if ((extraUseStmt instanceof AssignStmt) 
									 && (((AssignStmt) extraUseStmt).getLeftOp().toString().equals("fakeLocal") || ((AssignStmt) extraUseStmt).getRightOp().toString().equals("fakeLocal"))) {
										extraUsesBckward.remove(extraUse);
										continue;
									}
								}
								if (extraUsesBckward.size() > 128) {
									System.out.println("\t\tExtra-Use Number (Bckward): " + extraUsesBckward.size()); // Debug
									continue;
								}
								
								for (UnitValueBoxPair extraUse : extraUsesBckward) {
									Unit extraUseUnit = extraUse.unit;
									Stmt extraUseStmt = (Stmt) extraUseUnit;
									Value extraValue = extraUse.valueBox.getValue();
									if (!(extraUseStmt instanceof AssignStmt) && !extraUseStmt.containsInvokeExpr())
										continue;
									if ((extraUseStmt instanceof AssignStmt) 
									 && (((AssignStmt) extraUseStmt).getLeftOp().toString().equals("fakeLocal") || ((AssignStmt) extraUseStmt).getRightOp().toString().equals("fakeLocal")))
										continue;
									if (extraUseStmt.containsInvokeExpr() && !(extraUseStmt.getInvokeExpr() instanceof InstanceInvokeExpr))
										continue;
									if (extraUseStmt.containsInvokeExpr() 
									 && (((InstanceInvokeExpr) extraUseStmt.getInvokeExpr()).getBase().equals(extraValue)
									  || !(((InstanceInvokeExpr) extraUseStmt.getInvokeExpr()).getBase() instanceof Local)))
										continue;
									// System.out.println(String.format("\t\tExtra-Use (Bckward): %s in ( %s )", extraUse.unit, SootEnvironment.Unit2MethodMap.get(extraUse.unit))); // Debug
									if (extraUseStmt.containsInvokeExpr()) {
										InvokeExpr extraUseInvokeExpr = extraUseStmt.getInvokeExpr();
										Local extraUseInvokeBase = (Local) ((InstanceInvokeExpr) extraUseInvokeExpr).getBase();
										List<Unit> extraDepDefs = IntraProcedureVariableAnalysis.findDefs(SootEnvironment.Unit2MethodMap.get(extraUseStmt).retrieveActiveBody(), extraUseStmt, extraUseInvokeBase);
										for (Unit extraDepDef : new ArrayList<Unit>(extraDepDefs)) {
											if (!(extraDepDef instanceof AssignStmt)) {
												extraDepDefs.remove(extraDepDef);
												continue;
											}
										}
										if (extraDepDefs.size() > 8) {
											System.out.println("\t\t\tExtra-Dep-Def Number: " + extraDepDefs.size()); // Debug
											continue;
										}
										
										for (Unit extraDepDef : extraDepDefs) {
											if (!(extraDepDef instanceof AssignStmt))
												continue;
											Value extraDepRef = ((AssignStmt) extraDepDef).getRightOp();
											if (!(extraDepRef instanceof FieldRef))
												continue;
											SootField extraDepField = ((FieldRef) extraDepRef).getField();
											if (aliasTypeCheck(putExtraValue.getType(), extraDepField.getType()) == false)
												continue;
											if (refFieldCheck(extraDepField) == false)
												continue;
											
											System.out.println(String.format("\t\tExtra-Use (Bckward): %s in ( %s )", extraUse.unit, SootEnvironment.Unit2MethodMap.get(extraUse.unit))); // Debug
											System.out.println(String.format("\t\t\tExtra-Dep-Def: %s, %s", extraDepDef, extraDepField));
										
											// fill in putExtra2fieldMap
											if (!putExtra2fieldMap.containsKey(useUnit))
												putExtra2fieldMap.put(useUnit, new HashSet<SootField>());
											putExtra2fieldMap.get(useUnit).add(extraDepField);
											// ----
											
											// fill in putExtra2classMap
											Type fieldType = extraDepField.getType();
											if (!fieldType.toString().endsWith("[]") && isBasicType(fieldType) == false && newTypeCheck(fieldType) == true) {
												SootClass fieldClass = Scene.v().getSootClass(fieldType.toString());
												
												if (!putExtra2classMap.containsKey(useUnit))
													putExtra2classMap.put(useUnit, new HashSet<SootClass>());
												putExtra2classMap.get(useUnit).add(fieldClass);
											}
											// ----
											
											// fill in putExtra2actionMap
											if (!putExtra2actionMap.containsKey(useUnit))
												putExtra2actionMap.put(useUnit, new HashSet<String>());
											putExtra2actionMap.get(useUnit).add(actionName);
											// ----
										}
									} else if (extraUseStmt instanceof AssignStmt) {
										Value extraDepRef = ((AssignStmt) extraUseStmt).getLeftOp();
										if (!(extraDepRef instanceof FieldRef))
											continue;
										SootField extraDepField = ((FieldRef) extraDepRef).getField();
										if (aliasTypeCheck(putExtraValue.getType(), extraDepField.getType()) == false)
											continue;
										if (refFieldCheck(extraDepField) == false)
											continue;
										
										System.out.println(String.format("\t\tExtra-Use (Bckward): %s in ( %s )", extraUse.unit, SootEnvironment.Unit2MethodMap.get(extraUse.unit))); // Debug
										System.out.println(String.format("\t\t\tExtra-Dep-Def: %s, %s", extraUseStmt, extraDepField));
									
										// fill in putExtra2fieldMap
										if (!putExtra2fieldMap.containsKey(useUnit))
											putExtra2fieldMap.put(useUnit, new HashSet<SootField>());
										putExtra2fieldMap.get(useUnit).add(extraDepField);
										// ----
										
										// fill in putExtra2classMap
										Type fieldType = extraDepField.getType();
										if (!fieldType.toString().endsWith("[]") && isBasicType(fieldType) == false && newTypeCheck(fieldType) == true) {
											SootClass fieldClass = Scene.v().getSootClass(fieldType.toString());
											
											if (!putExtra2classMap.containsKey(useUnit))
												putExtra2classMap.put(useUnit, new HashSet<SootClass>());
											putExtra2classMap.get(useUnit).add(fieldClass);
										}
										// ----
										
										// fill in putExtra2actionMap
										if (!putExtra2actionMap.containsKey(useUnit))
											putExtra2actionMap.put(useUnit, new HashSet<String>());
										putExtra2actionMap.get(useUnit).add(actionName);
										// ----
									}
								}
								// extra-use (forward)
								List<UnitValueBoxPair> extraUsesForward = InterProcedureVariableAnalysis.findUsesForward(body, useStmt, (Local) putExtraValue);
								for (UnitValueBoxPair extraUse : new ArrayList<UnitValueBoxPair>(extraUsesForward)) {
									Unit extraUseUnit = extraUse.unit;
									Stmt extraUseStmt = (Stmt) extraUseUnit;
									if (!(extraUseStmt instanceof AssignStmt) && !extraUseStmt.containsInvokeExpr()) {
										extraUsesForward.remove(extraUse);
										continue;
									}
									if ((extraUseStmt instanceof AssignStmt) 
									 && (((AssignStmt) extraUseStmt).getLeftOp().toString().equals("fakeLocal") || ((AssignStmt) extraUseStmt).getRightOp().toString().equals("fakeLocal"))) {
										extraUsesForward.remove(extraUse);
										continue;
									}
								}
								if (extraUsesForward.size() > 128) {
									System.out.println("\t\tExtra-Use Numebr (Forward): " + extraUsesForward.size()); // Debug
									continue;
								}
								
								for (UnitValueBoxPair extraUse : extraUsesForward) {
									Unit extraUseUnit = extraUse.unit;
									Stmt extraUseStmt = (Stmt) extraUseUnit;
									Value extraValue = extraUse.valueBox.getValue();
									if (!(extraUseStmt instanceof AssignStmt) && !extraUseStmt.containsInvokeExpr())
										continue;
									if ((extraUseStmt instanceof AssignStmt) 
									 && (((AssignStmt) extraUseStmt).getLeftOp().toString().equals("fakeLocal") || ((AssignStmt) extraUseStmt).getRightOp().toString().equals("fakeLocal")))
										continue;
									if (extraUseStmt.containsInvokeExpr() && !(extraUseStmt.getInvokeExpr() instanceof InstanceInvokeExpr))
										continue;
									if (extraUseStmt.containsInvokeExpr() 
									 && (((InstanceInvokeExpr) extraUseStmt.getInvokeExpr()).getBase().equals(extraValue)
									  || !(((InstanceInvokeExpr) extraUseStmt.getInvokeExpr()).getBase() instanceof Local)))
										continue;
									// System.out.println(String.format("\t\tExtra-Use (Forward): %s in ( %s )", extraUse.unit, SootEnvironment.Unit2MethodMap.get(extraUse.unit))); // Debug
									if (extraUseStmt.containsInvokeExpr()) {
										InvokeExpr extraUseInvokeExpr = extraUseStmt.getInvokeExpr();
										Local extraUseInvokeBase = (Local) ((InstanceInvokeExpr) extraUseInvokeExpr).getBase();
										List<Unit> extraDepDefs = IntraProcedureVariableAnalysis.findDefs(SootEnvironment.Unit2MethodMap.get(extraUseStmt).retrieveActiveBody(), extraUseStmt, extraUseInvokeBase);
										for (Unit extraDepDef : new ArrayList<Unit>(extraDepDefs)) {
											if (!(extraDepDef instanceof AssignStmt)) {
												extraDepDefs.remove(extraDepDef);
												continue;
											}
										}
										if (extraDepDefs.size() > 8) {
										 	System.out.println("\t\t\tExtra-Dep-Def Number: " + extraDepDefs.size()); // Debug
											continue;
										}
										
										for (Unit extraDepDef : extraDepDefs) {
											if (!(extraDepDef instanceof AssignStmt))
												continue;
											Value extraDepRef = ((AssignStmt) extraDepDef).getRightOp();
											if (!(extraDepRef instanceof FieldRef))
												continue;
											SootField extraDepField = ((FieldRef) extraDepRef).getField();
											if (aliasTypeCheck(putExtraValue.getType(), extraDepField.getType()) == false)
												continue;
											if (refFieldCheck(extraDepField) == false)
												continue;
											
											System.out.println(String.format("\t\tExtra-Use (Forward): %s in ( %s )", extraUse.unit, SootEnvironment.Unit2MethodMap.get(extraUse.unit))); // Debug
											System.out.println(String.format("\t\t\tExtra-Dep-Def: %s, %s", extraDepDef, extraDepField));
										
											// fill in putExtra2fieldMap
											if (!putExtra2fieldMap.containsKey(useUnit))
												putExtra2fieldMap.put(useUnit, new HashSet<SootField>());
											putExtra2fieldMap.get(useUnit).add(extraDepField);
											// ----
											
											// fill in putExtra2classMap
											Type fieldType = extraDepField.getType();
											if (!fieldType.toString().endsWith("[]") && isBasicType(fieldType) == false && newTypeCheck(fieldType) == true) {
												SootClass fieldClass = Scene.v().getSootClass(fieldType.toString());
												
												if (!putExtra2classMap.containsKey(useUnit))
													putExtra2classMap.put(useUnit, new HashSet<SootClass>());
												putExtra2classMap.get(useUnit).add(fieldClass);
											}
											// ----
											
											// fill in putExtra2actionMap
											if (!putExtra2actionMap.containsKey(useUnit))
												putExtra2actionMap.put(useUnit, new HashSet<String>());
											putExtra2actionMap.get(useUnit).add(actionName);
											// ----
										}
									} else if (extraUseStmt instanceof AssignStmt) {
										Value extraDepRef = ((AssignStmt) extraUseStmt).getLeftOp();
										if (!(extraDepRef instanceof FieldRef))
											continue;
										SootField extraDepField = ((FieldRef) extraDepRef).getField();
										if (aliasTypeCheck(putExtraValue.getType(), extraDepField.getType()) == false)
											continue;
										if (refFieldCheck(extraDepField) == false)
											continue;
										
										System.out.println(String.format("\t\tExtra-Use (Forward): %s in ( %s )", extraUse.unit, SootEnvironment.Unit2MethodMap.get(extraUse.unit))); // Debug
										System.out.println(String.format("\t\t\tExtra-Dep-Def: %s, %s", extraUseStmt, extraDepField));
									
										// fill in putExtra2fieldMap
										if (!putExtra2fieldMap.containsKey(useUnit))
											putExtra2fieldMap.put(useUnit, new HashSet<SootField>());
										putExtra2fieldMap.get(useUnit).add(extraDepField);
										// ----
										
										// fill in putExtra2classMap
										Type fieldType = extraDepField.getType();
										if (!fieldType.toString().endsWith("[]") && isBasicType(fieldType) == false && newTypeCheck(fieldType) == true) {
											SootClass fieldClass = Scene.v().getSootClass(fieldType.toString());
											
											if (!putExtra2classMap.containsKey(useUnit))
												putExtra2classMap.put(useUnit, new HashSet<SootClass>());
											putExtra2classMap.get(useUnit).add(fieldClass);
										}
										// ----
										
										// fill in putExtra2actionMap
										if (!putExtra2actionMap.containsKey(useUnit))
											putExtra2actionMap.put(useUnit, new HashSet<String>());
										putExtra2actionMap.get(useUnit).add(actionName);
										// ----
									}
								}
							}
						}
					}
					//
				}
			}
		}
	}
	
	private static void findSensitiveExtraDefs(Unit extraDef, Value putExtraValue, HashSet<Unit> handledStmts, Unit useUnit, String actionName) {
		handledStmts.add(extraDef);
		
		Value extraDefLhs = ((AssignStmt) extraDef).getLeftOp();
		Value extraDefRhs = ((AssignStmt) extraDef).getRightOp();
		System.out.println(String.format("\t\tExtra-Def: %s in ( %s )", extraDef, SootEnvironment.Unit2MethodMap.get(extraDef))); // Debug
		if (extraDefRhs instanceof FieldRef) {
			SootField extraDefRefField = ((FieldRef) extraDefRhs).getField();
			if ((putExtraValue != null) && aliasTypeCheck(putExtraValue.getType(), extraDefRefField.getType()) == false)
				return;
			if (refFieldCheck(extraDefRefField) == false)
				return;
			
			System.out.println(String.format("\t\t\tExtra-Def-Ref: %s, %s", extraDef, extraDefRefField));
			
			// fill in putExtra2fieldMap
			if (!putExtra2fieldMap.containsKey(useUnit))
				putExtra2fieldMap.put(useUnit, new HashSet<SootField>());
			putExtra2fieldMap.get(useUnit).add(extraDefRefField);
			// ----
			
			// fill in putExtra2classMap
			Type fieldType = extraDefRefField.getType();
			if (!fieldType.toString().endsWith("[]") && isBasicType(fieldType) == false && newTypeCheck(fieldType) == true) {
				SootClass fieldClass = Scene.v().getSootClass(fieldType.toString());
				
				if (!putExtra2classMap.containsKey(useUnit))
					putExtra2classMap.put(useUnit, new HashSet<SootClass>());
				putExtra2classMap.get(useUnit).add(fieldClass);
			}
			// ----
			
			// fill in putExtra2actionMap
			if (!putExtra2actionMap.containsKey(useUnit))
				putExtra2actionMap.put(useUnit, new HashSet<String>());
			putExtra2actionMap.get(useUnit).add(actionName);
			// ----
		}
		if (extraDefRhs instanceof InvokeExpr) {
			SootMethod extraSrcMethod = ((InvokeExpr) extraDefRhs).getMethod();
			if (!extraSrcMethod.isConcrete())
				return;
			if (isBasicType(extraDefLhs.getType()))
				return;
			// if (srcMethodCheck(extraSrcMethod) == false)
				// return;
					
			// fill in putExtra2srcMethodMap
			// if (!putExtra2srcMethodMap.containsKey(useUnit))
				// putExtra2srcMethodMap.put(useUnit, new HashSet<SootMethod>());
			// putExtra2srcMethodMap.get(useUnit).add(extraSrcMethod);
			// ----
		}
		if (extraDefRhs instanceof NewExpr) {
			// copy from PermissionFinder
			
			Type newType = ((NewExpr) extraDefRhs).getType();
			
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
				List<Unit> listElementDefs = handleListDefs((Stmt) extraDef, (Local) ((AssignStmt) extraDef).getLeftOp(), handledStmts, useUnit, actionName);
				for (Unit elementDef : listElementDefs) {
					if (!(elementDef instanceof AssignStmt))
						continue;
					
					Value elementDefLhs = ((AssignStmt) elementDef).getLeftOp();
					Value elementDefRhs = ((AssignStmt) elementDef).getRightOp();
					if (elementDefRhs instanceof FieldRef) {
						SootField elementDefField = ((FieldRef) elementDefRhs).getField();
						
						System.out.println(String.format("\t\t\tExtra-Def-Element: %s in (%s)", elementDef, SootEnvironment.Unit2MethodMap.get(elementDef))); // Debug
						System.out.println(String.format("\t\t\tExtra-Def-Element-Def: %s, %s", elementDef, elementDefField)); // Debug
						
						// fill in putExtra2fieldMap
						if (!putExtra2fieldMap.containsKey(useUnit))
							putExtra2fieldMap.put(useUnit, new HashSet<SootField>());
						putExtra2fieldMap.get(useUnit).add(elementDefField);
						// ----
						
						// fill in putExtra2classMap
						Type elementType = elementDefField.getType();
						if (!elementType.toString().endsWith("[]") && isBasicType(elementType) == false && newTypeCheck(elementType) == true) {
							SootClass elementClass = Scene.v().getSootClass(elementType.toString());
							
							if (!putExtra2classMap.containsKey(useUnit))
								putExtra2classMap.put(useUnit, new HashSet<SootClass>());
							putExtra2classMap.get(useUnit).add(elementClass);
						}
						// ----
						
						// fill in putExtra2actionMap
						if (!putExtra2actionMap.containsKey(useUnit))
							putExtra2actionMap.put(useUnit, new HashSet<String>());
						putExtra2actionMap.get(useUnit).add(actionName);
						// ----
					} else if (elementDefRhs instanceof NewExpr) {
						// check whether the sensitive information has been wiped out
						boolean sensitive = true;
						if (elementDefLhs instanceof Local) {
							for (UnitValueBoxPair elementDefUse : IntraProcedureVariableAnalysis.findUsesForward(SootEnvironment.Unit2MethodMap.get(elementDef).retrieveActiveBody(), (Stmt) elementDef, (Local) elementDefLhs)) {
								if (sensitive == false)
									break;
								
								Stmt elementDefUseStmt = (Stmt) elementDefUse.getUnit();
								if (elementDefUseStmt.containsInvokeExpr() && elementDefUseStmt.getInvokeExpr().getMethod().getName().equals("<init>")) {
									for (Value argValue : elementDefUseStmt.getInvokeExpr().getArgs()) {
										if (argValue instanceof StringConstant && ((StringConstant) argValue).value.equals("")) {
											sensitive = false;
											break;
										}
										if (argValue instanceof NullConstant) {
											sensitive = false;
											break;
										}
									}
								}
							}
						}
						
						Type elementType = ((NewExpr) elementDefRhs).getType();
						if (sensitive == true && !elementType.toString().endsWith("[]") && newTypeCheck(elementType) == true) {
							SootClass elementClass = Scene.v().getSootClass(elementType.toString());
						
							System.out.println(String.format("\t\t\tExtra-Def-Element: %s in (%s)", elementDef, SootEnvironment.Unit2MethodMap.get(elementDef))); // Debug
							System.out.println(String.format("\t\t\tExtra-Def-Element-Def: %s, new %s", elementDef, elementType.toString())); // Debug
							
							// fill in putExtra2classMap
							if (!putExtra2classMap.containsKey(useUnit))
								putExtra2classMap.put(useUnit, new HashSet<SootClass>());
							putExtra2classMap.get(useUnit).add(elementClass);
							// ----
							
							// fill in putExtra2actionMap
							if (!putExtra2actionMap.containsKey(useUnit))
								putExtra2actionMap.put(useUnit, new HashSet<String>());
							putExtra2actionMap.get(useUnit).add(actionName);
							// ----
						}
					} else {
						Type elementType = elementDefLhs.getType();
						if (!elementType.toString().endsWith("[]") && newTypeCheck(elementType) == true) {
							SootClass elementClass = Scene.v().getSootClass(elementType.toString());
						
							System.out.println(String.format("\t\t\tElement-Def: %s in (%s)", elementDef, SootEnvironment.Unit2MethodMap.get(elementDef))); // Debug
							System.out.println(String.format("\t\t\tElement-Def-Ref: %s, class %s", elementDef, elementType.toString())); // Debug
					
							// fill in putExtra2classMap
							if (!putExtra2classMap.containsKey(useUnit))
								putExtra2classMap.put(useUnit, new HashSet<SootClass>());
							putExtra2classMap.get(useUnit).add(elementClass);
							// ----
							
							// fill in putExtra2actionMap
							if (!putExtra2actionMap.containsKey(useUnit))
								putExtra2actionMap.put(useUnit, new HashSet<String>());
							putExtra2actionMap.get(useUnit).add(actionName);
							// ----
						}
					}
				}
			} else {
				// check whether the sensitive information has been wiped out
				boolean sensitive = true;
				if (extraDefLhs instanceof Local) {
					for (UnitValueBoxPair extraDefUse : IntraProcedureVariableAnalysis.findUsesForward(SootEnvironment.Unit2MethodMap.get(extraDef).retrieveActiveBody(), (Stmt) extraDef, (Local) extraDefLhs)) {
						if (sensitive == false)
							break;
						
						Stmt extraDefUseStmt = (Stmt) extraDefUse.getUnit();
						if (extraDefUseStmt.containsInvokeExpr() && extraDefUseStmt.getInvokeExpr().getMethod().getName().equals("<init>")) {
							for (Value argValue : extraDefUseStmt.getInvokeExpr().getArgs()) {
								if (argValue instanceof StringConstant && ((StringConstant) argValue).value.equals("")) {
									sensitive = false;
									break;
								}
								if (argValue instanceof NullConstant) {
									sensitive = false;
									break;
								}
							}
						}
					}
				}
				
				if (sensitive == true && !newType.toString().endsWith("[]") && isBasicType(newType) == false && newTypeCheck(newType) == true) {
					SootClass newClass = Scene.v().getSootClass(newType.toString());
				
					System.out.println(String.format("\t\t\tExtra-Def-New: %s", newType)); // Debug
			
					// fill in putExtra2classMap
					if (!putExtra2classMap.containsKey(useUnit))
						putExtra2classMap.put(useUnit, new HashSet<SootClass>());
					putExtra2classMap.get(useUnit).add(newClass);
					// ----
					
					// fill in putExtra2actionMap
					if (!putExtra2actionMap.containsKey(useUnit))
						putExtra2actionMap.put(useUnit, new HashSet<String>());
					putExtra2actionMap.get(useUnit).add(actionName);
					// ----
				}
			}
		}
	}
	
	// copy from PermissionFinder
	private static List<Unit> handleListDefs(Stmt newListStmt, Local listLocal, HashSet<Unit> handledStmts, Unit useUnit, String actionName) {
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
				System.out.println("\t\t\tList-Copy: " + listUseUnit);
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
							
							System.out.println("\t\t\t\tList-Copy-Def: " + copyTargetDef);
							Stmt copyTargetStmt = (Stmt) copyTargetDef;
							if (!(copyTargetStmt instanceof AssignStmt))
								continue;
							Value copyListValue = ((AssignStmt) copyTargetStmt).getLeftOp();
							if (!(copyListValue instanceof Local))
								continue;
							
							HashSet<Unit> newHandledStmts = new HashSet<Unit>(handledStmts); // same as IntentAnalysis.java
							newHandledStmts.add(listUseStmt);
							findSensitiveExtraDefs(copyTargetDef, null, newHandledStmts, useUnit, actionName);
						}
					}
				}
			}
			
			// for add/append element
			if ((invokeExpr.getMethod().getName().equals("add")
			  || invokeExpr.getMethod().getName().equals("append")) 
			 && invokeExpr.getArgCount() == 1) {
				System.out.println("\t\t\tList-Use: " + listUseUnit);
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
				System.out.println("\t\t\tMap-Use: " + listUseUnit);
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
	
	private static boolean analyzeIntentSender(List<UnitValueBoxPair> intentUses) {
		boolean willSend = false;
		
		for (UnitValueBoxPair intentUse : intentUses) {
			Unit intentUseUnit = intentUse.unit;
			Stmt intentUseStmt = (Stmt) intentUseUnit;
			if (!intentUseStmt.containsInvokeExpr())
				continue;
			InvokeExpr intentUseExpr = intentUseStmt.getInvokeExpr();
			if (intentUseExpr.getMethod().getDeclaringClass().getName().equals("android.content.Intent"))
				continue;
			
			// heuristics
			if (intentUseExpr.getMethod().getReturnType().toString().equals("android.app.PendingIntent")) {
				willSend = true;
			}
			if (intentUseExpr.getMethod().getName().startsWith("start")
			 || (intentUseExpr.getMethod().getName().startsWith("send") && !intentUseExpr.getMethod().getName().contains("Order"))
			 || intentUseExpr.getMethod().getName().startsWith("broadcast")
			 || intentUseExpr.getMethod().getName().equals("<init>")) {
				willSend = true;
			}
			
			// handle LocalBroadcastManager
			if (intentUseExpr.getMethod().getDeclaringClass().getName().contains("LocalBroadcastManager"))
				willSend = false;
			
			// handle setResult
			if (willSend == false && intentUseExpr.getMethod().getName().startsWith("setResult")) {
				SootClass activityClass = SootEnvironment.Unit2MethodMap.get(intentUseUnit).getDeclaringClass();
				if (AppManifestAnalysis.exportedActivitySet.contains(activityClass)) {
					willSend = true;
				}
			}
			
			if (willSend) {
				// System.out.println(String.format("\tInter-Use: %s in %s", intentUseStmt, SootEnvironment.Unit2MethodMap.get(intentUseUnit))); // Debug
			} else {
				// System.err.println(String.format("\tInter-Use: %s in %s", intentUseStmt, SootEnvironment.Unit2MethodMap.get(intentUseUnit))); // Debug
			}
		}
		
		return willSend;
	}
	
	private static boolean isDefaultPackage(Unit setPackageUnit) {
		boolean result = false; // test
		
		CallGraph cg = Scene.v().getCallGraph();
		
		Stmt setPackageStmt = (Stmt) setPackageUnit;
		Value packageValue = setPackageStmt.getInvokeExpr().getArg(0);
		if (packageValue instanceof Local) {
			SootMethod sootMethod = SootEnvironment.Unit2MethodMap.get(setPackageUnit);
			Body body = sootMethod.retrieveActiveBody();
			List<Unit> packageDefs = IntraProcedureVariableAnalysis.findDefs(body, setPackageStmt, (Local) packageValue);
			for (Unit packageDef : packageDefs) {
				if (!((Stmt) packageDef).containsInvokeExpr())
					continue;
				// System.out.println("\tPackage-Def: " + packageDef); // Debug
				
				Iterator<Edge> callees = cg.edgesOutOf(packageDef);
				int calleeCount = 0;
				while (callees.hasNext()) {
					callees.next();
					calleeCount++;
				}
				if (calleeCount > 8) { // see InterProcedureVariableAnalysis.maxTgtNumber
					// do nothing
				} else {
					callees = cg.edgesOutOf(packageDef); // reset
				}
				
				// int pathIdx = 1; // Debug
				while (callees.hasNext()) {
					SootMethod callee = callees.next().tgt();
					HashSet<ArrayList<SootMethod>> paths = CallgraphAnalysis.cmpPathForward(null, callee, 6);
					// Debug
					// for (ArrayList<SootMethod> path : paths) {
						// for (SootMethod pathElement : path) {
							// System.out.println(String.format("\t\tPath-%d: %s", pathIdx, pathElement)); // Debug
						// }
						// pathIdx++;
					// }
					for (ArrayList<SootMethod> path : paths) {
						for (SootMethod pathElement : path) {
							if (pathElement.getName().equals("getRoleHoldersAsUser")
							 || pathElement.getName().equals("getRoleHolders")) {
								result = true;
								return result;
							}
						}
					}
				}
			}
		}
		
		return result;
	}
	
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
		if (typeRaw.equals("android.hardware.usb.ParcelableUsbPort"))
			return false;
		if (typeRaw.equals("android.net.ProxyInfo"))
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
	//
	
	// ---- //
	
	public static void main(String[] args) {
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
			
			try {
				SootEnvironment.initForAPK(apkPath);
			} catch (Exception e) {
				System.err.println(String.format("[%d/%d] Error: init Soot fail for APK %s????", apkIdx, apkFiles.length, apkPath));
				continue;
			}
			
			System.out.println(String.format("[%d/%d] Debug: analyzing APK %s", apkIdx, apkFiles.length, apkPath));
			SootEnvironment.buildApkCallgraph();
		
			analyzeInner();
			// printOutput();
		}
	}

}
