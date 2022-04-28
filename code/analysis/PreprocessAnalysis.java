package ??.??.analysis;

import java.util.List;

import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Unit;
import soot.UnitPatchingChain;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.util.Chain;

public class PreprocessAnalysis {
	
	public static boolean needFurtherAnalysis() {
		boolean needAnalysis = false;
		
		Chain<SootClass> sootClasses = Scene.v().getClasses();
		// System.out.println(String.format("[Debug] [needFurtherAnalysis] total class number: %d", sootClasses.size()));
		// int classIdx = 1;
		for (SootClass sootClass : sootClasses) {
			// System.out.println(String.format("[Debug] [needFurtherAnalysis] Flag-0 (%d): %s, %d", classIdx++, sootClass.getName(), sootClass.getMethodCount()));
			if (needAnalysis == true)
				break;
			if (!sootClass.isConcrete())
				continue;
			
			List<SootMethod> sootMethods = sootClass.getMethods();
			for (SootMethod sootMethod : sootMethods) {
				// System.out.println(String.format("[Debug] [needFurtherAnalysis] Flag-1: %s", sootMethod.getSignature()));
				
				if (needAnalysis == true) {
					// System.out.println(String.format("[Debug] [needFurtherAnalysis] Flag-1-1"));
					break;
				}
				if (!sootMethod.isConcrete()) {
					// System.out.println(String.format("[Debug] [needFurtherAnalysis] Flag-1-2"));
					continue;
				}
				
				Body body = sootMethod.retrieveActiveBody();
				// System.out.println(String.format("[Debug] [needFurtherAnalysis] Flag-2"));
				UnitPatchingChain units = body.getUnits();
				for (Unit unit : units) {
					if (needAnalysis == true)
						break;
					
					Stmt stmt = (Stmt) unit;
					if (!stmt.containsInvokeExpr())
						continue;
					
					try {
						InvokeExpr invokeExpr = stmt.getInvokeExpr();
						SootMethodRef callee = invokeExpr.getMethodRef();
						if (callee.getName().startsWith("sendBroadcast") || callee.getName().startsWith("sendStickyBroadcast")) {
							if (!callee.getName().contains("AsUser") && invokeExpr.getArgCount() >= 1) {
								if (callee.getParameterType(0).toString().equals("android.content.Intent")) {
									needAnalysis = true;
									break;
								}
							} else if (callee.getName().contains("AsUser") && invokeExpr.getArgCount() >= 2) {
								if (callee.getParameterType(0).toString().equals("android.content.Intent")
								 && callee.getParameterType(1).toString().equals("android.os.UserHandle")) {
									needAnalysis = true;
									break;
								}
							}	
						} else if (callee.getName().startsWith("getBroadcast") || callee.getName().startsWith("getBroadcastAsUser")) {
							if (invokeExpr.getArgCount() >= 3) {
								if (callee.getParameterType(2).toString().equals("android.content.Intent")) {
									needAnalysis = true;
									break;
								}
							}
						}
					} catch (Exception e) {
						System.err.println(e.getMessage()); // strange case
						continue;
					}
				}
			}
		}
		
		// System.out.println(String.format("[Debug] [needFurtherAnalysis] return %s", needAnalysis ? "true" : "false"));
		return needAnalysis;
	}

}
