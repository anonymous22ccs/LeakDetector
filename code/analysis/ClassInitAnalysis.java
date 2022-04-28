package ??.??.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import ??.??.configure.SootEnvironment;
import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;

public class ClassInitAnalysis {
	
	private static void analyzeInner() {
		HashMap<SootClass, HashSet<SootClass>> object2initClass = new HashMap<SootClass, HashSet<SootClass>>();
		
		for (SootClass sootClass : new ArrayList<SootClass>(Scene.v().getClasses())) {
			if (sootClass.isPhantom())
				continue;
			for (SootMethod sootMethod : new ArrayList<SootMethod>(sootClass.getMethods())) {
				if (!sootMethod.isConcrete())
					continue;
				Body body = sootMethod.retrieveActiveBody();
				for (Unit unit : body.getUnits()) {
					Stmt stmt = (Stmt) unit;
					if (!stmt.containsInvokeExpr())
						continue;
					InvokeExpr invokeExpr = stmt.getInvokeExpr();
					SootMethod callee = invokeExpr.getMethod();
					if (callee.getName().equals("<init>")) {
						SootClass objectClass = callee.getDeclaringClass();
						if (!object2initClass.containsKey(objectClass))
							object2initClass.put(objectClass, new HashSet<SootClass>());
						object2initClass.get(objectClass).add(sootClass);
					}
				}
			}
		}
		
		// Debug
		for (SootClass objectClass : object2initClass.keySet()) {
			HashSet<SootClass> initClasses = object2initClass.get(objectClass);
			if (initClasses == null)
				initClasses = new HashSet<SootClass>();
			System.out.println(String.format("Object %s initialzed in %d Classes", objectClass, initClasses.size()));
		}
	}
	
	// ---- 
	
	// module-test
	
	public static void main(String[] args) {
		SootEnvironment.init();
		
		analyzeInner();
	}

}
