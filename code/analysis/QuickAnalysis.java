package ??.??.analysis;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;

import ??.??.configure.SootEnvironment;
import soot.Body;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.InvokeExpr;
import soot.jimple.NullConstant;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.toolkits.scalar.UnitValueBoxPair;

public class QuickAnalysis {
	
	// "void sendBroadcast(android.content.Intent)";
	// "void sendBroadcast(android.content.Intent,java.lang.String)";
	// "void sendBroadcast(android.content.Intent,java.lang.String,int)";
	// "void sendBroadcast(android.content.Intent,java.lang.String,android.os.Bundle)";
	// "void sendBroadcastMultiplePermissions(android.content.Intent,java.lang.String[])";
	// "void sendBroadcastWithMultiplePermissions(android.content.Intent,java.lang.String[])";
	
	// "void sendBroadcastAsUser(android.content.Intent,android.os.UserHandle)";
	// "void sendBroadcastAsUser(android.content.Intent,android.os.UserHandle,java.lang.String)";
	// "void sendBroadcastAsUser(android.content.Intent,android.os.UserHandle,java.lang.String,int)";
	// "void sendBroadcastAsUser(android.content.Intent,android.os.UserHandle,java.lang.String,android.os.Bundle)";
	// "void sendBroadcastAsUserMultiplePermissions(android.content.Intent,android.os.UserHandle,java.lang.String[])";
	// "void sendStickyBroadcastAsUser(android.content.Intent,android.os.UserHandle)";
	// "void sendStickyBroadcastAsUser(android.content.Intent,android.os.UserHandle,android.os.Bundle)";
	
	private static void findSendBroadcast() {
		ArrayList<String> callers = new ArrayList<String>();
		HashSet<String> sendBroadcastMethods = new HashSet<String>();
		
		for (SootClass sootClass : Scene.v().getClasses()) {
			if (!sootClass.isConcrete())
				continue;
			
			// System.out.println(sootClass.getName()); // Debug
			for (SootMethod sootMethod : new ArrayList<SootMethod>(sootClass.getMethods())) { // avoid ConcurrentModificationException
				boolean found = false;
				if (!sootMethod.isConcrete())
					continue;
				
				// System.out.println("\t" + sootMethod.getSignature()); // Debug
				try {
					sootMethod.retrieveActiveBody();
				} catch (Exception e) {
					System.err.println(String.format("[Error] cannot retrieve method body for %s", sootMethod.getSignature())); // rare cases
					continue;
				}
				
				Body body = sootMethod.getActiveBody();
				for (Unit unit : body.getUnits()) {
					Stmt stmt = (Stmt) unit;
					if (!stmt.containsInvokeExpr())
						continue;
					
					try {
						InvokeExpr invokeExpr = stmt.getInvokeExpr();
						SootMethod callee = invokeExpr.getMethod();
						
						// test
						// if (callee.getName().equals("showLogin"))
							// System.out.println(sootMethod);
						
						if (callee.getName().startsWith("sendBroadcast") || callee.getName().startsWith("sendStickyBroadcast")) {
							if (!callee.getName().contains("AsUser") && invokeExpr.getArgCount() >= 1) {
								if (!callee.getParameterType(0).toString().equals("android.content.Intent"))
									continue;
								sendBroadcastMethods.add(callee.getSignature());
								
								if (invokeExpr.getArgCount() == 1)
									found = true;
								if (invokeExpr.getArgCount() > 1) {
									Value permissionValue = invokeExpr.getArg(1);
									if (permissionValue instanceof StringConstant)
										if (((StringConstant) permissionValue).value.equals(""))
											found = true;
									if (permissionValue instanceof NullConstant)
										found = true;
								}
							} else if (callee.getName().contains("AsUser") && invokeExpr.getArgCount() >= 2) {
								if (!callee.getParameterType(0).toString().equals("android.content.Intent")
								 || !callee.getParameterType(1).toString().equals("android.os.UserHandle"))
									continue;
								sendBroadcastMethods.add(callee.getSignature());
								
								if (invokeExpr.getArgCount() == 2)
									found = true;
								if (invokeExpr.getArgCount() > 2) {
									Value permissionValue = invokeExpr.getArg(2);
									if (permissionValue instanceof StringConstant)
										if (((StringConstant) permissionValue).value.equals(""))
											found = true;
									if (permissionValue instanceof NullConstant)
										found = true;
								}
							}	
							
							// adjust
							if (found == true) {
								if (invokeExpr.getArg(0) instanceof Local) {
									boolean hasData = false;
									
									List<UnitValueBoxPair> usesPairs = IntraProcedureVariableAnalysis.findUsesBckward(body, stmt, (Local) invokeExpr.getArg(0));
									for (UnitValueBoxPair usePair : usesPairs) {
										Unit useUnit = usePair.unit;
										Stmt useStmt = (Stmt) useUnit;
										if (!useStmt.containsInvokeExpr())
											continue;
										if (useStmt.getInvokeExpr().getMethod().getName().equals("setClass")
										 || useStmt.getInvokeExpr().getMethod().getName().equals("setClassName")
										 || useStmt.getInvokeExpr().getMethod().getName().equals("setComponent")
										 || useStmt.getInvokeExpr().getMethod().getName().equals("setPackage"))
											found = false;
										if (useStmt.getInvokeExpr().getMethod().getName().startsWith("put")
										 && useStmt.getInvokeExpr().getMethod().getName().endsWith("Extra"))
											hasData = true;
									
										if (found == false)
											break;
									}
									
									if (hasData == false)
										found = false;
								} else {
									// TODO
								}
							}
						}
						
						if (found == true)
							break;
					} catch (Exception e) {
						System.err.println(e.getMessage()); // strange case
						continue;
					}
				}
				
				if (found) {
					// System.out.println(sootMethod.getSignature());
					if (!callers.contains(sootMethod.getSignature()))
						callers.add(sootMethod.getSignature());
				}
			}
		}
		
		// for (String sendBroadcastMethod : sendBroadcastMethods) {
			// System.out.println(sendBroadcastMethod);
		// }
		
		callers.sort(Comparator.naturalOrder());
		for (String caller : callers) {
			System.out.println(caller);
		}
	}
	
	// PendingIntent.getBroadcast/getBroadcastAsUser
	private static void findGetBroadcast() {
		ArrayList<String> callers = new ArrayList<String>();
		HashSet<String> getBroadcastMethods = new HashSet<String>();
		
		for (SootClass sootClass : Scene.v().getClasses()) {
			if (!sootClass.isConcrete())
				continue;
			
			for (SootMethod sootMethod : new ArrayList<SootMethod>(sootClass.getMethods())) { // avoid ConcurrentModificationException
				boolean found = false;
				if (!sootMethod.isConcrete())
					continue;
				
				try {
					sootMethod.retrieveActiveBody();
				} catch (Exception e) {
					System.err.println(String.format("[Error] cannot retrieve method body for %s", sootMethod.getSignature())); // rare cases
					continue;
				}
				
				Body body = sootMethod.getActiveBody();
				for (Unit unit : body.getUnits()) {
					Stmt stmt = (Stmt) unit;
					if (!stmt.containsInvokeExpr())
						continue;
					
					try {
						InvokeExpr invokeExpr = stmt.getInvokeExpr();
						SootMethod callee = invokeExpr.getMethod();
						
						// test
						// if (callee.getName().equals("showLogin"))
							// System.out.println(sootMethod);
						
						if (callee.getName().startsWith("getBroadcast") || callee.getName().startsWith("getBroadcastAsUser")) {
							if (invokeExpr.getArgCount() < 3)
								continue;
							if (!callee.getParameterType(2).toString().equals("android.content.Intent"))
								continue;
							getBroadcastMethods.add(callee.getSignature());
							found = true;
							
							// adjust
							if (found == true) {
								if (invokeExpr.getArg(2) instanceof Local) {
									boolean hasData = false;
									
									List<UnitValueBoxPair> usesPairs = IntraProcedureVariableAnalysis.findUsesBckward(body, stmt, (Local) invokeExpr.getArg(2));
									for (UnitValueBoxPair usePair : usesPairs) {
										Unit useUnit = usePair.unit;
										Stmt useStmt = (Stmt) useUnit;
										if (!useStmt.containsInvokeExpr())
											continue;
										if (useStmt.getInvokeExpr().getMethod().getName().equals("setClass")
										 || useStmt.getInvokeExpr().getMethod().getName().equals("setClassName")
										 || useStmt.getInvokeExpr().getMethod().getName().equals("setComponent")
										 || useStmt.getInvokeExpr().getMethod().getName().equals("setPackage"))
											found = false;
										if (useStmt.getInvokeExpr().getMethod().getName().startsWith("put")
										 && useStmt.getInvokeExpr().getMethod().getName().endsWith("Extra"))
											hasData = true;
									
										if (found == false)
											break;
									}
									
									if (hasData == false)
										found = false;
								} else {
									// TODO
								}
							}
						}
						
						if (found == true)
							break;
					} catch (Exception e) {
						System.err.println(e.getMessage()); // strange case
						continue;
					}
				}
				
				if (found) {
					// System.out.println(sootMethod.getSignature());
					if (!callers.contains(sootMethod.getSignature()))
						callers.add(sootMethod.getSignature());
				}
			}
		}
		
		// for (String getBroadcastMethod : getBroadcastMethods) {
			// System.out.println(sendBroadcastMethod);
		// }
		
		callers.sort(Comparator.naturalOrder());
		for (String caller : callers) {
			System.out.println(caller);
		}
	}
	
	// ---- //
	
	// module-test
	public static void main(String[] args) {
		SootEnvironment.init();
		
		findSendBroadcast();
		System.out.println("==== ==== ==== ==== ==== ==== ==== ====");
		findGetBroadcast();
	}

}
