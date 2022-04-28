package ??.??.analysis;

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
import soot.jimple.AssignStmt;
import soot.jimple.EqExpr;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.NeExpr;
import soot.jimple.Stmt;
import soot.toolkits.scalar.UnitValueBoxPair;

public class UIDFinder {
	
	private static void innerAnalyze() {
		// collect methods to be analyzed
		HashSet<SootMethod> methodSet = new HashSet<SootMethod>();
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
				methodSet.add(sootMethod);
			}
		}
		
		// analyze each method
		for (SootMethod sootMethod : methodSet) {
			Body body = sootMethod.retrieveActiveBody();
			for (Unit unit : body.getUnits()) {
				Stmt stmt = (Stmt) unit;
				// case: xx = xx.getCallingUid*(*)
				if (!stmt.containsInvokeExpr())
					continue;
				if (!stmt.getInvokeExpr().getMethod().getName().contains("getCallingUid"))
					continue;
				if (!(stmt instanceof AssignStmt))
					continue;
				
				// System.out.println(String.format("[ %s ] in %s",stmt, sootMethod.getSignature())); // Debug
				Value lhsValue = ((AssignStmt) stmt).getLeftOp();
				if (!(lhsValue instanceof Local))
					continue; // conservatively
				List<UnitValueBoxPair> forwardUses = IntraProcedureVariableAnalysis.findUsesForward(body, stmt, (Local) lhsValue);
				for (UnitValueBoxPair forwardUse : forwardUses) {
					// System.out.println("\t" + forwardUse.unit); // Debug.
					Unit useUnit = forwardUse.unit;
					if (!(useUnit instanceof IfStmt))
						continue;
					Value conditionValue = ((IfStmt) useUnit).getCondition();
					if (conditionValue instanceof EqExpr) {
						Value op1Value = ((EqExpr) conditionValue).getOp1();
						Value op2Value = ((EqExpr) conditionValue).getOp2();
						if ((op1Value instanceof IntConstant) || (op2Value instanceof IntConstant)) {
							System.out.println(String.format("[ %s ] in %s", useUnit, sootMethod.getSignature())); // Debug
						}
					} else if (conditionValue instanceof NeExpr) {
						Value op1Value = ((NeExpr) conditionValue).getOp1();
						Value op2Value = ((NeExpr) conditionValue).getOp2();
						if ((op1Value instanceof IntConstant) || (op2Value instanceof IntConstant)) {
							System.out.println(String.format("[ %s ] in %s", useUnit, sootMethod.getSignature())); // Debug
						}
					} else {
						// System.err.println(String.format("[ %s ] %s", conditionValue, conditionValue.getClass())); // Debug
					}
				}
			}
		}
	}
	
	// ---- //
	
	// module-test
		
	public static void main(String[] args) {
		SootEnvironment.init();
		// SootEnvironment.buildCallgraph();
			
		innerAnalyze();
	}

}
