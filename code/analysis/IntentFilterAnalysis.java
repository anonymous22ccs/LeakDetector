package ??.??.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import soot.Body;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.NewExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.toolkits.scalar.UnitValueBoxPair;

public class IntentFilterAnalysis {
	// export
	public static HashSet<String> privilegedIntents = new HashSet<String>();
	
	private static HashSet<String> handledMethods = new HashSet<String>();
	
	public static void analyze() {
		for (SootClass sootClass : new ArrayList<SootClass>(Scene.v().getClasses())) {
			if (sootClass.isPhantom())
				continue;
			if (sootClass.getName().startsWith("android.content.IntentFilter")) // ignore itself
				continue;
			
			for (SootMethod sootMethod : new ArrayList<SootMethod>(sootClass.getMethods())) {
				if (!sootMethod.isConcrete())
					continue;
				if (handledMethods.contains(sootMethod.getSignature()))
					continue;
				
				handledMethods.add(sootMethod.getSignature()); // update
				
				Body body = sootMethod.retrieveActiveBody();
				for (Unit unit : body.getUnits()) {
					Stmt stmt = (Stmt) unit;
					if (!(stmt instanceof AssignStmt))
						continue;
					
					Value lhsValue = ((AssignStmt) stmt).getLeftOp();
					Value rhsValue = ((AssignStmt) stmt).getRightOp();
					
					if (!(lhsValue instanceof Local))
						continue;
					
					// new IntentFilter(*)
					if (rhsValue instanceof NewExpr) {
						if (!((NewExpr) rhsValue).getType().toString().equals("android.content.IntentFilter"))
							continue;
						
						HashSet<String> intentFilters = new HashSet<String>();
						
						List<UnitValueBoxPair> filterUses = InterProcedureVariableAnalysis.findUsesForward(body, stmt, (Local) lhsValue);
						boolean isPriority = false;
						
						for (UnitValueBoxPair filterUse : filterUses) {
							Unit filterUseUnit = filterUse.getUnit();
							Stmt filterUseStmt = (Stmt) filterUseUnit;
							if (!filterUseStmt.containsInvokeExpr())
								continue;
							
							SootMethod filterUseCallee = filterUseStmt.getInvokeExpr().getMethod();
							
							if (filterUseCallee.getName().equals("setPriority"))
								isPriority = true;
							
							if ((filterUseCallee.getName().equals("<init>") || filterUseCallee.getName().equals("addAction"))
							 && filterUseCallee.getParameterCount() > 0 && filterUseCallee.getParameterType(0).toString().equals("java.lang.String")) {
								Value filterValue = filterUseStmt.getInvokeExpr().getArg(0);
								if (filterValue instanceof StringConstant) {
									String actionName = ((StringConstant) filterValue).value;
									intentFilters.add(actionName);
								}
								if (filterValue instanceof Local) {
									for (Unit actionDefUnit : InterProcedureVariableAnalysis.findDefs(body, stmt, (Local) filterValue)) {
										Stmt actionDefStmt = (Stmt) actionDefUnit;
										if (!(actionDefStmt instanceof AssignStmt))
											continue;
										Value actionDefValue = ((AssignStmt) actionDefStmt).getRightOp();
										if (actionDefValue instanceof StringConstant) {
											String actionName = ((StringConstant) actionDefValue).value;
											intentFilters.add(actionName);
										}
									}
								}
							}
						}
						
						if (isPriority == true) {
							privilegedIntents.addAll(intentFilters);
						}
					}
					// IntentFilter.create
					if (rhsValue instanceof InvokeExpr) {
						SootMethod callee = ((InvokeExpr) rhsValue).getMethod();
						if (!callee.getName().equals("create") || !callee.getDeclaringClass().getName().equals("android.content.IntentFilter"))
							continue;
						
						HashSet<String> intentFilters = new HashSet<String>();
						
						if (callee.getParameterCount() > 0 && callee.getParameterType(0).toString().equals("java.lang.String")) {
							Value filterValue = ((InvokeExpr) rhsValue).getArg(0);
							if (filterValue instanceof StringConstant) {
								String actionName = ((StringConstant) filterValue).value;
								intentFilters.add(actionName);
							}
							if (filterValue instanceof Local) {
								for (Unit actionDefUnit : InterProcedureVariableAnalysis.findDefs(body, stmt, (Local) filterValue)) {
									Stmt actionDefStmt = (Stmt) actionDefUnit;
									if (!(actionDefStmt instanceof AssignStmt))
										continue;
									Value actionDefValue = ((AssignStmt) actionDefStmt).getRightOp();
									if (actionDefValue instanceof StringConstant) {
										String actionName = ((StringConstant) actionDefValue).value;
										intentFilters.add(actionName);
									}
								}
							}
						}
						
						// following is almost the same as handling new InternFilter(*)
						
						List<UnitValueBoxPair> filterUses = InterProcedureVariableAnalysis.findUsesForward(body, stmt, (Local) lhsValue);
						boolean isPriority = false;
						
						for (UnitValueBoxPair filterUse : filterUses) {
							Unit filterUseUnit = filterUse.getUnit();
							Stmt filterUseStmt = (Stmt) filterUseUnit;
							if (!filterUseStmt.containsInvokeExpr())
								continue;
							
							SootMethod filterUseCallee = filterUseStmt.getInvokeExpr().getMethod();
							
							if (filterUseCallee.getName().equals("setPriority"))
								isPriority = true;
							
							if (filterUseCallee.getName().equals("addAction") 
							 && filterUseCallee.getParameterType(0).toString().equals("java.lang.String")) {
								Value filterValue = filterUseStmt.getInvokeExpr().getArg(0);
								if (filterValue instanceof StringConstant) {
									String actionName = ((StringConstant) filterValue).value;
									intentFilters.add(actionName);
								}
								if (filterValue instanceof Local) {
									for (Unit actionDefUnit : InterProcedureVariableAnalysis.findDefs(body, stmt, (Local) filterValue)) {
										Stmt actionDefStmt = (Stmt) actionDefUnit;
										if (!(actionDefStmt instanceof AssignStmt))
											continue;
										Value actionDefValue = ((AssignStmt) actionDefStmt).getRightOp();
										if (actionDefValue instanceof StringConstant) {
											String actionName = ((StringConstant) actionDefValue).value;
											intentFilters.add(actionName);
										}
									}
								}
							}
						}
						
						if (isPriority == true) {
							privilegedIntents.addAll(intentFilters);
						}
					}
				}
			}
		}
	}

}
