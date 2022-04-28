package ??.??.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import soot.Body;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.SimpleLocalDefs;
import soot.toolkits.scalar.SimpleLocalUses;
import soot.toolkits.scalar.UnitValueBoxPair;

// local variable analysis
public class IntraProcedureVariableAnalysis {
	
	// ---- //
	
	public static List<Unit> findDefs(Body body, Stmt stmt, Local local) {
		UnitGraph cfg = new BriefUnitGraph(body);
		SimpleLocalDefs defsResolver = new SimpleLocalDefs(cfg);
		List<Unit> defs = defsResolver.getDefsOfAt(local, stmt);
		
		HashSet<Unit> defSet = new HashSet<Unit>();
		
		// check AssignStmt
		for (Unit def : defs) {
			Stmt defStmt = (Stmt) def;
			if (defStmt instanceof AssignStmt) {
				// Value defLhs = ((AssignStmt) defStmt).getLeftOp();
				Value defRhs = ((AssignStmt) defStmt).getRightOp();
				if ((defRhs instanceof Local)) {
					defSet.add(def);
					
					defSet.addAll(findDefsInternal(body, defStmt, (Local) defRhs, 4));
				} else if (defRhs instanceof CastExpr) {
					defSet.add(def);
					
					Value castValue = ((CastExpr) defRhs).getOp();
					if (castValue instanceof Local) {
						defSet.addAll(findDefsInternal(body, defStmt, (Local) castValue, 4));
					}
				} else if (defRhs instanceof InvokeExpr) {
					defSet.add(def);
					
					/*
					int argCount = ((InvokeExpr) defRhs).getArgCount();
					Type returnType = ((InvokeExpr) defRhs).getMethod().getReturnType();
					if (isBasicType(returnType) == false && argCount == 1) {
						SootClass paramClass = Scene.v().getSootClass(((InvokeExpr) defRhs).getMethod().getParameterType(0).toString());
						SootClass returnClass = Scene.v().getSootClass(returnType.toString());
						boolean possibleCopy = false;
						if (possibleCopy == false) {
							try {
								possibleCopy = Scene.v().getActiveHierarchy().isClassSubclassOfIncluding(paramClass, returnClass);
							} catch (Exception e) { possibleCopy = false; }
						}
						if (possibleCopy == false) {
							try {
								possibleCopy = Scene.v().getActiveHierarchy().isClassSubclassOfIncluding(returnClass, paramClass);
							} catch (Exception e) { possibleCopy = false; }
						}
						if (possibleCopy == false) {
							try {
								possibleCopy = Scene.v().getActiveHierarchy().isInterfaceSubinterfaceOf(paramClass, returnClass);
							} catch (Exception e) { possibleCopy = false; }
						}
						if (possibleCopy == false) {
							try {
								possibleCopy = Scene.v().getActiveHierarchy().isInterfaceSubinterfaceOf(returnClass, paramClass);
							} catch (Exception e) { possibleCopy = false; }
						}
						
						
						if (possibleCopy == true) {
							Value objValue = ((InvokeExpr) defRhs).getArg(0);
							if (objValue instanceof Local) {
								defSet.addAll(findDefsInternal(body, defStmt, (Local) objValue, 4));
							}
						}
					}
					*/
				} else {
					defSet.add(def); // other cases?
				}
			} else {
				defSet.add(def); // normal cases
			}
		}
		
		return new ArrayList<Unit>(defSet);
	}
	
	private static List<Unit> findDefsInternal(Body body, Stmt stmt, Local local, int deep) {
		UnitGraph cfg = new BriefUnitGraph(body);
		SimpleLocalDefs defsResolver = new SimpleLocalDefs(cfg);
		List<Unit> defs = defsResolver.getDefsOfAt(local, stmt);
		
		HashSet<Unit> defSet = new HashSet<Unit>();
		
		// check AssignStmt
		for (Unit def : defs) {
			Stmt defStmt = (Stmt) def;
			if (defStmt instanceof AssignStmt) {
				// Value defLhs = ((AssignStmt) defStmt).getLeftOp();
				Value defRhs = ((AssignStmt) defStmt).getRightOp();
				if ((defRhs instanceof Local)) {
					defSet.add(def);
					
					if (deep > 0) {
						defSet.addAll(findDefsInternal(body, defStmt, (Local) defRhs, deep - 1));
					}
				} else if (defRhs instanceof CastExpr) {
					defSet.add(def);
					
					Value castValue = ((CastExpr) defRhs).getOp();
					if (castValue instanceof Local) {
						if (deep > 0) {
							defSet.addAll(findDefsInternal(body, defStmt, (Local) castValue, deep - 1));
						}
					}
				} else if (defRhs instanceof InvokeExpr) {
					defSet.add(def);
					
					/*
					int argCount = ((InvokeExpr) defRhs).getArgCount();
					Type returnType = ((InvokeExpr) defRhs).getMethod().getReturnType();
					if (isBasicType(returnType) == false && argCount == 1) {
						SootClass paramClass = Scene.v().getSootClass(((InvokeExpr) defRhs).getMethod().getParameterType(0).toString());
						SootClass returnClass = Scene.v().getSootClass(returnType.toString());
						boolean possibleCopy = false;
						if (possibleCopy == false) {
							try {
								possibleCopy = Scene.v().getActiveHierarchy().isClassSubclassOfIncluding(paramClass, returnClass);
							} catch (Exception e) { possibleCopy = false; }
						}
						if (possibleCopy == false) {
							try {
								possibleCopy = Scene.v().getActiveHierarchy().isClassSubclassOfIncluding(returnClass, paramClass);
							} catch (Exception e) { possibleCopy = false; }
						}
						if (possibleCopy == false) {
							try {
								possibleCopy = Scene.v().getActiveHierarchy().isInterfaceSubinterfaceOf(paramClass, returnClass);
							} catch (Exception e) { possibleCopy = false; }
						}
						if (possibleCopy == false) {
							try {
								possibleCopy = Scene.v().getActiveHierarchy().isInterfaceSubinterfaceOf(returnClass, paramClass);
							} catch (Exception e) { possibleCopy = false; }
						}
						
						if (possibleCopy == true) {
							Value objValue = ((InvokeExpr) defRhs).getArg(0);
							if (objValue instanceof Local) {
								if (deep > 0) {
									defSet.addAll(findDefsInternal(body, defStmt, (Local) objValue, deep - 1));
								}
							}
						}
					}
					*/
				} else {
					defSet.add(def); // other cases?
				}
			} else {
				defSet.add(def); // normal cases
			}
		}
		
		return new ArrayList<Unit>(defSet);
	}
	
	// copy from PermissionFinder.java (or IntentAnalysis.java)
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
	
	// ---- //
	
	public static List<UnitValueBoxPair> findUses(Body body, Stmt stmt, Local local) {
		UnitGraph cfg = new BriefUnitGraph(body);
		SimpleLocalDefs defsResolver = new SimpleLocalDefs(cfg);
		List<Unit> defs = defsResolver.getDefsOfAt(local, stmt);
		SimpleLocalUses usesResolver = new SimpleLocalUses(cfg, defsResolver);
		List<UnitValueBoxPair> uses = new ArrayList<UnitValueBoxPair>();
		List<UnitValueBoxPair> useHistory = new ArrayList<UnitValueBoxPair>();
		for (Unit def : defs) {
			List<UnitValueBoxPair> pairs = usesResolver.getUsesOf(def);
			for (UnitValueBoxPair pair : pairs) {
				uses.add(pair);
				useHistory.add(pair);
			}
		}
		
		// handle variable propagation
		for (UnitValueBoxPair use : new ArrayList<UnitValueBoxPair>(uses)) {
			Unit useUnit = use.unit;
			if (useUnit == stmt)
				continue;
			if (!(useUnit instanceof AssignStmt))
				continue;
			Value assigneeValue = ((AssignStmt) useUnit).getLeftOp();
			if (!(assigneeValue instanceof Local))
				continue;
			if (assigneeValue == local)
				continue;
			Type assigneeType = ((Local) assigneeValue).getType();
			if (!local.getType().toString().equals(assigneeType.toString()))
				continue;
			if (machineTypes.contains(assigneeType.toString()))
				continue;
			
			// System.out.println("[findUses] -->> " + useUnit + " in " + SootEnvironment.Unit2MethodMap.get(useUnit)); // Debug
			List<UnitValueBoxPair> newHistory = new ArrayList<UnitValueBoxPair>(useHistory);
			for (UnitValueBoxPair aliasUse : findUsesForwardUtil(body, (Stmt) useUnit, (Local) assigneeValue, newHistory)) {
				if (!uses.contains(aliasUse)) {
					uses.add(aliasUse);
					useHistory.add(aliasUse); // redundant?
				}
			}
			// System.out.println("[findUses] <<-- " + useUnit); // Debug
		}
		
		return uses;
	}
	
	private static List<UnitValueBoxPair> findUsesUtil(Body body, Stmt stmt, Local local, List<UnitValueBoxPair> useHistory) {
		UnitGraph cfg = new BriefUnitGraph(body);
		SimpleLocalDefs defsResolver = new SimpleLocalDefs(cfg);
		List<Unit> defs = defsResolver.getDefsOfAt(local, stmt);
		SimpleLocalUses usesResolver = new SimpleLocalUses(cfg, defsResolver);
		List<UnitValueBoxPair> uses = new ArrayList<UnitValueBoxPair>();
		for (Unit def : defs) {
			List<UnitValueBoxPair> pairs = usesResolver.getUsesOf(def);
			for (UnitValueBoxPair pair : pairs) {
				if (useHistory.contains(pair))
					continue;
				uses.add(pair);
				useHistory.add(pair);
			}
		}
		
		// handle variable propagation
		for (UnitValueBoxPair use : new ArrayList<UnitValueBoxPair>(uses)) {
			Unit useUnit = use.unit;
			if (useUnit == stmt)
				continue;
			if (!(useUnit instanceof AssignStmt))
				continue;
			Value assigneeValue = ((AssignStmt) useUnit).getLeftOp();
			if (!(assigneeValue instanceof Local))
				continue;
			if (assigneeValue == local)
				continue;
			Type assigneeType = ((Local) assigneeValue).getType();
			if (!local.getType().toString().equals(assigneeType.toString()))
				continue;
			if (machineTypes.contains(assigneeType.toString()))
				continue;
			
			// System.out.println("[findUses] -->> " + useUnit + " in " + SootEnvironment.Unit2MethodMap.get(useUnit));
			List<UnitValueBoxPair> newHistory = new ArrayList<UnitValueBoxPair>(useHistory);
			for (UnitValueBoxPair aliasUse : findUsesForwardUtil(body, (Stmt) useUnit, (Local) assigneeValue, newHistory)) {
				if (!uses.contains(aliasUse)) {
					uses.add(aliasUse);
					useHistory.add(aliasUse); // redundant?
				}
			}
			// System.out.println("[findUses] <<-- " + useUnit);
		}
		
		return uses;
	}
	
	public static List<UnitValueBoxPair> findUsesBckward(Body body, Stmt stmt, Local local) {
		// collect units executed before the input "stmt"
		UnitGraph cfg = new BriefUnitGraph(body);
		HashSet<Unit> preUnits = new HashSet<Unit>();
		Queue<Unit> queue = new LinkedList<Unit>();
		queue.addAll(cfg.getPredsOf(stmt)); // <- 
		while (!queue.isEmpty()) {
			Unit curUnit = queue.poll();
			if (preUnits.contains(curUnit))
				continue;
			preUnits.add(curUnit);
			for (Unit preUnit : cfg.getPredsOf(curUnit))
				if (!preUnits.contains(preUnit) && !queue.contains(preUnit))
					queue.add(preUnit);
		}
		// filter out excluded uses
		List<UnitValueBoxPair> output = new ArrayList<UnitValueBoxPair>();
		List<UnitValueBoxPair> useHistory = new ArrayList<UnitValueBoxPair>();
		List<UnitValueBoxPair> uses = findUsesUtil(body, stmt, local, useHistory); // inaccurate uses
		for (UnitValueBoxPair use : uses) {
			if (preUnits.contains(use.unit)) {
				output.add(use);
				useHistory.add(use);
			}
		}

		// handle variable propagation
		for (UnitValueBoxPair use : new ArrayList<UnitValueBoxPair>(output)) {
			Unit useUnit = use.unit;
			if (useUnit == stmt)
				continue;
			if (!(useUnit instanceof AssignStmt))
				continue;
			Value assigneeValue = ((AssignStmt) useUnit).getLeftOp();
			if (!(assigneeValue instanceof Local))
				continue;
			if (assigneeValue == local)
				continue;
			Type assigneeType = ((Local) assigneeValue).getType();
			if (!local.getType().toString().equals(assigneeType.toString()))
				continue;
			if (machineTypes.contains(assigneeType.toString()))
				continue;
			
			List<UnitValueBoxPair> newHistory = new ArrayList<UnitValueBoxPair>(useHistory);
			for (UnitValueBoxPair aliasUse : findUsesBckwardUtil(body, (Stmt) useUnit, (Local) assigneeValue, newHistory)) {
				if (!output.contains(aliasUse)) {
					output.add(aliasUse);
					newHistory.add(aliasUse); // redundant?
				}
			}
		}
		
		return output;
	}
	
	private static List<UnitValueBoxPair> findUsesBckwardUtil(Body body, Stmt stmt, Local local, List<UnitValueBoxPair> useHistory) {
		// collect units executed before the input "stmt"
		UnitGraph cfg = new BriefUnitGraph(body);
		HashSet<Unit> preUnits = new HashSet<Unit>();
		Queue<Unit> queue = new LinkedList<Unit>();
		queue.addAll(cfg.getPredsOf(stmt)); // <- 
		while (!queue.isEmpty()) {
			Unit curUnit = queue.poll();
			if (preUnits.contains(curUnit))
				continue;
			preUnits.add(curUnit);
			for (Unit preUnit : cfg.getPredsOf(curUnit))
				if (!preUnits.contains(preUnit) && !queue.contains(preUnit))
					queue.add(preUnit);
		}
		// filter out excluded uses
		List<UnitValueBoxPair> output = new ArrayList<UnitValueBoxPair>();
		List<UnitValueBoxPair> newHistory = new ArrayList<UnitValueBoxPair>(useHistory);
		List<UnitValueBoxPair> uses = findUsesUtil(body, stmt, local, newHistory); // inaccurate uses
		for (UnitValueBoxPair use : uses) {
			if (preUnits.contains(use.unit)) {
				if (useHistory.contains(use))
					continue;
				output.add(use);
				useHistory.add(use);
			}
		}

		// handle variable propagation
		for (UnitValueBoxPair use : new ArrayList<UnitValueBoxPair>(output)) {
			Unit useUnit = use.unit;
			if (useUnit == stmt)
				continue;
			if (!(useUnit instanceof AssignStmt))
				continue;
			Value assigneeValue = ((AssignStmt) useUnit).getLeftOp();
			if (!(assigneeValue instanceof Local))
				continue;
			if (assigneeValue == local)
				continue;
			Type assigneeType = ((Local) assigneeValue).getType();
			if (!local.getType().toString().equals(assigneeType.toString()))
				continue;
			if (machineTypes.contains(assigneeType.toString()))
				continue;
			
			newHistory = new ArrayList<UnitValueBoxPair>(useHistory);
			for (UnitValueBoxPair aliasUse : findUsesBckwardUtil(body, (Stmt) useUnit, (Local) assigneeValue, newHistory)) {
				if (!output.contains(aliasUse)) {
					output.add(aliasUse);
					useHistory.add(aliasUse); // redundant?
				}
			}
		}
		
		return output;
	}
	
	public static List<UnitValueBoxPair> findUsesForward(Body body, Stmt stmt, Local local) {
		// collect units executed after the input "stmt"
		UnitGraph cfg = new BriefUnitGraph(body);
		HashSet<Unit> pstUnits = new HashSet<Unit>();
		Queue<Unit> queue = new LinkedList<Unit>();
		queue.addAll(cfg.getSuccsOf(stmt)); // <- 
		while (!queue.isEmpty()) {
			Unit curUnit = queue.poll();
			if (pstUnits.contains(curUnit))
				continue;
			pstUnits.add(curUnit);
			for (Unit pstUnit : cfg.getSuccsOf(curUnit))
				if (!pstUnits.contains(pstUnit) && !queue.contains(pstUnit))
					queue.add(pstUnit);
		}
		
		// filter out excluded uses
		List<UnitValueBoxPair> output = new ArrayList<UnitValueBoxPair>();
		List<UnitValueBoxPair> useHistory = new ArrayList<UnitValueBoxPair>();
		List<UnitValueBoxPair> uses = findUsesUtil(body, stmt, local, useHistory); // inaccurate uses
		
		// specially handle return-statement
		/*
		if ((stmt instanceof ReturnStmt) && ((ReturnStmt) stmt).getOp() instanceof Local) {
			pstUnits.add(stmt); // HashSet<Unit> pstUnits
			
			UnitValueBoxPair retPair = new UnitValueBoxPair(stmt, ((ReturnStmt) stmt).getOpBox());
			boolean noExist = true;
			for (UnitValueBoxPair use : uses) {
				if (use.unit == stmt) {
					noExist = false;
					break;
				}
			}
			if (noExist == true) {
				uses.add(retPair); // List<UnitValueBoxPair> uses
			}
		}
		*/
		
		for (UnitValueBoxPair use : uses) {
			if (pstUnits.contains(use.unit)) {
				output.add(use);
				useHistory.add(use);
			}
		}
		
		// handle variable propagation
		for (UnitValueBoxPair use : new ArrayList<UnitValueBoxPair>(output)) {
			Unit useUnit = use.unit;
			if (useUnit == stmt)
				continue;
			if (!(useUnit instanceof AssignStmt))
				continue;
			Value assigneeValue = ((AssignStmt) useUnit).getLeftOp();
			if (!(assigneeValue instanceof Local))
				continue;
			if (assigneeValue == local)
				continue;
			Type assigneeType = ((Local) assigneeValue).getType();
			if (!local.getType().toString().equals(assigneeType.toString()))
				continue;
			if (machineTypes.contains(assigneeType.toString()))
				continue;
			
			List<UnitValueBoxPair> newHistory = new ArrayList<UnitValueBoxPair>(useHistory);
			for (UnitValueBoxPair aliasUse : findUsesForwardUtil(body, (Stmt) useUnit, (Local) assigneeValue, newHistory)) {
				if (!output.contains(aliasUse)) {
					output.add(aliasUse);
					newHistory.add(aliasUse); // redundant?
				}
			}
		}
		
		return output;
	}
	
	private static List<UnitValueBoxPair> findUsesForwardUtil(Body body, Stmt stmt, Local local, List<UnitValueBoxPair> useHistory) {
		// collect units executed after the input "stmt"
		UnitGraph cfg = new BriefUnitGraph(body);
		HashSet<Unit> pstUnits = new HashSet<Unit>();
		Queue<Unit> queue = new LinkedList<Unit>();
		queue.addAll(cfg.getSuccsOf(stmt)); // <- 
		while (!queue.isEmpty()) {
			Unit curUnit = queue.poll();
			if (pstUnits.contains(curUnit))
				continue;
			pstUnits.add(curUnit);
			for (Unit pstUnit : cfg.getSuccsOf(curUnit))
				if (!pstUnits.contains(pstUnit) && !queue.contains(pstUnit))
					queue.add(pstUnit);
		}
		// filter out excluded uses
		List<UnitValueBoxPair> output = new ArrayList<UnitValueBoxPair>();
		List<UnitValueBoxPair> newHistory = new ArrayList<UnitValueBoxPair>(useHistory);
		List<UnitValueBoxPair> uses = findUsesUtil(body, stmt, local, newHistory); // inaccurate uses
		for (UnitValueBoxPair use : uses) {
			if (pstUnits.contains(use.unit)) {
				if (useHistory.contains(use))
					continue;
				output.add(use);
				useHistory.add(use);
			}
		}
		
		// handle variable propagation
		for (UnitValueBoxPair use : new ArrayList<UnitValueBoxPair>(output)) {
			Unit useUnit = use.unit;
			if (useUnit == stmt)
				continue;
			if (!(useUnit instanceof AssignStmt))
				continue;
			Value assigneeValue = ((AssignStmt) useUnit).getLeftOp();
			if (!(assigneeValue instanceof Local))
				continue;
			if (assigneeValue == local)
				continue;
			Type assigneeType = ((Local) assigneeValue).getType();
			if (!local.getType().toString().equals(assigneeType.toString()))
				continue;
			if (machineTypes.contains(assigneeType.toString()))
				continue;
			
			newHistory = new ArrayList<UnitValueBoxPair>(useHistory);
			for (UnitValueBoxPair aliasUse : findUsesForwardUtil(body, (Stmt) useUnit, (Local) assigneeValue, newHistory)) {
				if (!output.contains(aliasUse)) {
					output.add(aliasUse);
					useHistory.add(aliasUse); // redundant?
				}
			}
		}
		
		return output;
	}

	// ---- //
	
	private static ArrayList<String> machineTypes = new ArrayList<String>();
	static {
		machineTypes.add("byte");
		machineTypes.add("java.lang.Byte");
		machineTypes.add("short");
		machineTypes.add("java.lang.Short");
		machineTypes.add("int");
		machineTypes.add("java.lang.Integer");
		machineTypes.add("long");
		machineTypes.add("java.lang.Long");
		machineTypes.add("char");
		machineTypes.add("java.lang.Character");
		machineTypes.add("float");
		machineTypes.add("java.lang.Float");
		machineTypes.add("double");
		machineTypes.add("java.lang.Double");
		machineTypes.add("boolean");
		machineTypes.add("java.lang.Boolean");
		
		machineTypes.add("java.lang.String");
	}
	
}
