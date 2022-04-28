package ??.??.configure;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.ConcurrentModificationException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

import ??.??.analysis.IntraProcedureVariableAnalysis;
import soot.Body;
import soot.G;
import soot.Hierarchy;
import soot.Local;
import soot.PackManager;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.NewExpr;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.ClinitElimTransformer;
import soot.jimple.toolkits.callgraph.Edge;
import soot.options.Options;
import soot.toolkits.scalar.UnitValueBoxPair;

public class SootEnvironment {
	public static HashMap<Unit, SootMethod> Unit2MethodMap = new HashMap<>();
	
	private static String[] packageWhitelist = new String[] {
			/* Google   */ "android.", "com.android.", "com.google.android.", 
			/* Samsung  */ "com.samsung.", "com.knox.", "com.sec.", "com.sem.", 
			/* Xiaomi   */ "com.miui.", "miui.", "com.xiaomi.", 
			/* Huawei   */ "cn.honor.", "com.hihonor.", "com.huawei.", 
			/* OnePlus  */ "cn.oneplus.", "com.oneplus.", "com.oplus.", "net.oneplus.", 
			/* OPPO     */ "com.coloros.", "com.heytap.", "com.oppo.", 
			/* Vivo     */ "com.bbk.", "com.iqoo.", "com.vivo.", 
			/* Meizu    */ "com.flyme.", "com.meizu.", 
			// /* Qualcomm */ "com.qualcomm.", 
	};
	
	public static boolean inWhitelist(String packageName /* or className */) {
		boolean result = false;
		for (String prefix : packageWhitelist) {
			if (packageName.startsWith(prefix)) {
				result = true;
				break;
			}
		}
		return result;
	}
	
	public static void init() {
		// clean up
		G.reset();
		
		Long startTime = System.currentTimeMillis();
		
		// set soot environment
		Options.v().set_src_prec(Options.src_prec_class);
		Options.v().set_process_dir(Collections.singletonList(Configure.classesOutputDir));
		Options.v().set_allow_phantom_refs(true);
		Options.v().set_allow_phantom_elms(true);
		Options.v().set_whole_program(true);
		Options.v().set_keep_line_number(false);
		Options.v().set_keep_offset(false);
		Options.v().set_ignore_resolving_levels(true);
		Options.v().set_ignore_resolution_errors(true);
		Options.v().set_wrong_staticness(Options.v().wrong_staticness_fix);
		Options.v().set_output_format(Options.output_format_none);
		        
		// exclude certain packages for better performance
		List<String> excludeList = new ArrayList<String>();
		// excludeList.add("java.");
		// excludeList.add("javax.");
		// excludeList.add("sun.");
		// excludeList.add("androidx.");
		// excludeList.add("kotlin.");
		Options.v().set_exclude(excludeList);
		Options.v().set_no_bodies_for_excluded(true);
		        
		Scene.v().loadNecessaryClasses();
		
		Long midTime = System.currentTimeMillis();
		System.out.println(String.format("[Debug] load class finish, spend %d seconds", (midTime - startTime) / 1000)); // Debug
				
		// ensure every SootClass instance has been resolved
		while (true) {
			try {
				// Scene.v().getClasses() may throw ConcurrentModificationException
				for (SootClass sootClass : Scene.v().getClasses()) {
					if (sootClass.isPhantom())
						continue;
					
					for (SootMethod sootMethod : sootClass.getMethods()) {
						if (!sootMethod.isConcrete())
							continue;
							
						try {
							// System.out.println(String.format("[Debug] %s", sootMethod.getSignature())); // Debug
							// check-1
							sootMethod.retrieveActiveBody();
						} catch (Exception e) {
							// System.out.println(e);
							sootMethod.setPhantom(true);
						}
					}
				}
				break;
			} catch (ConcurrentModificationException e) {
				e.printStackTrace();
			}
		}
		
		// we are only interested in methods of classes in white list
		for (SootClass sootClass : Scene.v().getClasses()) {
			if (!inWhitelist(sootClass.getName())) {
				sootClass.setPhantomClass();
				for (SootMethod sootMethod : sootClass.getMethods()) {
					sootMethod.setPhantom(true);
				}
			}
			// black-list
			if (sootClass.getName().startsWith("android.util.")
			 || sootClass.getName().startsWith("android.support.")
			 || sootClass.getName().startsWith("miui.util.")
			 || sootClass.getName().startsWith("miui.support.")
			 || sootClass.getName().startsWith("com.miui.maml.")) {
				sootClass.setPhantomClass();
				for (SootMethod sootMethod : sootClass.getMethods()) {
					sootMethod.setPhantom(true);
				}
			}
		}
		
		// patch for Supplier
		for (SootClass sootClass : Scene.v().getClasses()) {
			if (sootClass.isPhantom())
				continue;
			for (SootMethod sootMethod : sootClass.getMethods()) {
				if (!sootMethod.isConcrete())
					continue;
				Body body = null;
				try {
					body = sootMethod.retrieveActiveBody();
				} catch (Exception e) {
					sootMethod.setPhantom(true);
					continue;
				}
				if (body == null)
					continue;
					
				for (Unit unit : new ArrayList<Unit>(body.getUnits())) {
					Stmt stmt = (Stmt) unit;
					if (!stmt.containsInvokeExpr())
						continue;
					if (!(stmt instanceof AssignStmt))
						continue;
					Value lhsValue = ((AssignStmt) stmt).getLeftOp();
					if (!(lhsValue instanceof Local))
						continue;
					Local lhsLocal = (Local) lhsValue;
					
					InvokeExpr invokeExpr = stmt.getInvokeExpr();
					SootMethod tgtMethod = invokeExpr.getMethod();
					if (tgtMethod.getParameterCount() < 1)
						continue;
					if (!tgtMethod.getParameterType(0).toString().equals("java.util.function.Supplier"))
						continue;
					Value supplierValue = invokeExpr.getArg(0);
					if (!(supplierValue instanceof Local))
						continue;
					Local supplierLocal = (Local) supplierValue;
					List<Unit> supplierDefs = IntraProcedureVariableAnalysis.findDefs(body, stmt, supplierLocal);
					for (Unit supplierDef : supplierDefs) {
						Stmt supplierDefStmt = (Stmt) supplierDef;
						if (!(supplierDefStmt instanceof AssignStmt))
							continue;
						Value supplierDefRhs = ((AssignStmt) supplierDefStmt).getRightOp();
						if (!(supplierDefRhs instanceof NewExpr))
							continue;
						String typeName = ((NewExpr) supplierDefRhs).getType().toString();
						SootClass supplierClass = Scene.v().getSootClass(typeName);
						// System.out.println(supplierClass);
						// for (SootMethod supplierMethod : supplierClass.getMethods())
							// System.out.println("\t" + supplierMethod.getSignature());
						try {
							SootMethod supplierGetMethod = supplierClass.getMethodByName("get");
							
							InvokeExpr newRhs = Jimple.v().newVirtualInvokeExpr(supplierLocal, supplierGetMethod.makeRef());
							AssignStmt newStmt = Jimple.v().newAssignStmt(lhsLocal, newRhs);
							body.getUnits().insertAfter(newStmt, stmt);
						} catch (Exception e) {}
					}
				}
			}
		}
		
		// Test
		//
		for (SootClass sootClass : new ArrayList<SootClass>(Scene.v().getClasses())) {
			if (sootClass.isPhantom())
				continue;
			for (SootMethod sootMethod : new ArrayList<SootMethod>(sootClass.getMethods())) {
				if (!sootMethod.isConcrete())
					continue;
				Body body = sootMethod.retrieveActiveBody();
				// if (!sootMethod.getSignature().equals("ndroid.app.ContentProviderHolder getContentProviderImpl(android.app.IApplicationThread,java.lang.String,android.os.IBinder,int,java.lang.String,java.lang.String,boolean,int)>"))
				if (!sootMethod.getName().equals("getWifiEnabledState"))
					continue;
				// System.out.println(sootMethod.getSignature());
				// System.out.println(body);
				/*
				for (Unit unit : body.getUnits()) {
					if (!unit.toString().contains("$i2 = virtualinvoke $r25"))
						continue;
					System.out.println(unit);
					List<UnitValueBoxPair> useValues = IntraProcedureVariableAnalysis.findUsesForward(body, (Stmt) unit, (Local) ((AssignStmt) unit).getLeftOp());
					for (UnitValueBoxPair useValue : useValues) {
						System.out.println("\t" + useValue.unit);
					}
				}
				*/
			}
		}
		// System.exit(0);
		//
		
		Long endTime = System.currentTimeMillis();
		
		System.out.println(String.format("[Debug] init soot finish, spend %d seconds", (endTime - startTime) / 1000)); // Debug
	}
	
	public static void buildCallgraph() {
		Long startTime = System.currentTimeMillis();
		
		Options.v().setPhaseOption("cg", "enabled:true");
		Options.v().setPhaseOption("cg.cha", "enabled:true");
		Options.v().setPhaseOption("cg.cha", "string-constants:true");
		// Options.v().setPhaseOption("cg", "enabled:true");
		// Options.v().setPhaseOption("cg.spark", "enabled:true");
		// Options.v().setPhaseOption("cg.spark", "string-constants:true");
		
		HashSet<SootMethod> entryPoints = new HashSet<SootMethod>();
		for (SootClass sootClass : Scene.v().getClasses()) {
			if (sootClass.isPhantom())
				continue;
			for (SootMethod sootMethod : sootClass.getMethods()) {
				if (!sootMethod.isConcrete())
					continue;
				entryPoints.add(sootMethod);
			}
		}
		Scene.v().setEntryPoints(new ArrayList<SootMethod>(entryPoints));
		PackManager.v().runPacks();
		
		Long midTime = System.currentTimeMillis();
		
		System.out.println(String.format("[Debug] build cg finish, spend %d seconds", (midTime - startTime) / 1000)); // Debug
		
		/*
		{
			HashMap<SootMethod, Integer> ingreeMap = new HashMap<SootMethod, Integer>();
			
			CallGraph cg = Scene.v().getCallGraph();
			Iterator<Edge> edges = cg.iterator();
			while (edges.hasNext()) {
				Edge edge = edges.next();
				// SootMethod src = edge.src();
				SootMethod tgt = edge.tgt();
				if (!ingreeMap.containsKey(tgt))
					ingreeMap.put(tgt, 0);
				int ingree = ingreeMap.get(tgt) + 1;
				ingreeMap.put(tgt, ingree);
			}
			
			for (SootMethod tgt : ingreeMap.keySet()) {
				int ingree = ingreeMap.get(tgt);
				// System.out.println(String.format("%d: %s", ingree, tgt.getSignature()));
			}
			
			// System.exit(0);
		}
		*/
		
		/*
		Hierarchy hierarchy = Scene.v().getActiveHierarchy();
		SootClass listClass = Scene.v().getSootClass("java.util.List");
		SootClass arrayListClass = Scene.v().getSootClass("java.util.ArrayList");
		System.out.println("" + hierarchy.isClassSubclassOf(arrayListClass, listClass));
		System.exit(0);
		*/
		
		// prune
		boolean isStable = false;
		while (!isStable) {
			HashSet<Edge> removeEdges = new HashSet<Edge>();
			
			CallGraph cg = Scene.v().getCallGraph();
			Iterator<Edge> edgeIterator = cg.iterator();
			while (edgeIterator.hasNext()) {
				Edge edge = edgeIterator.next();
				if (edge.src().getName().equals("onTransact")
				 || edge.tgt().getName().equals("execute")
				 || edge.tgt().getName().equals("run")
				 || edge.tgt().getName().equals("handleMessage")
				 || edge.tgt().getName().equals("doWork")
				) {
					removeEdges.add(edge);
				}
				if (edge.src().getName().equals("onCommand")
				 || edge.src().getName().contains("print")
				 || edge.src().getName().contains("dump")) {
					removeEdges.add(edge);
				}
				if (edge.src().getDeclaringClass().getName().contains("ShellCommand")
				 || edge.src().getDeclaringClass().getName().equals("android.os.Binder")
				 || edge.src().getDeclaringClass().getName().equals("android.content.ContentResolver")) {
					removeEdges.add(edge);
				}
			}
		
			for (Edge removeEdge : removeEdges) {
				cg.removeEdge(removeEdge);
			}
			Scene.v().setCallGraph(cg);
			
			if (removeEdges.size() == 0)
				isStable = true;
		}
		
		Long endTime = System.currentTimeMillis();
		
		System.out.println(String.format("[Debug] prune cg finish, spend %d seconds", (endTime - midTime) / 1000)); // Debug
	
		// 
		for (SootClass sootClass : new ArrayList<SootClass>(Scene.v().getClasses())) {
			if (sootClass.isPhantom())
				continue;
			for (SootMethod sootMethod : new ArrayList<SootMethod>(sootClass.getMethods())) {
				if (!sootMethod.isConcrete())
					continue;
				Body body = sootMethod.retrieveActiveBody();
				for (Unit unit : body.getUnits()) {
					assert !Unit2MethodMap.containsKey(unit);
					Unit2MethodMap.put(unit, sootMethod);
				}
			}
		}
	}
	
	// ---- //
	
	public static void initForPreprocess(String dexPath) {
		// clean up
		G.reset();
				
		// set soot environment
		Options.v().set_src_prec(Options.src_prec_apk);
		Options.v().set_process_dir(Collections.singletonList(dexPath));
		// Options.v().set_android_jars(Configure.androidJars);
		Options.v().set_force_android_jar(Configure.androidJars + File.separator + "android-31" + File.separator + "android.jar");
		Options.v().set_allow_phantom_refs(true);
		Options.v().set_whole_program(true);
		Options.v().set_process_multiple_dex(true);
		Options.v().set_keep_line_number(false);
		Options.v().set_keep_offset(false);
		Options.v().set_ignore_resolving_levels(true);
		// Options.v().set_ignore_resolution_errors(true);
		Options.v().set_output_format(Options.output_format_class);
		Options.v().set_output_dir(Configure.classesOutputDir);
		
		// exclude certain packages for better performance
		List<String> excludeList = new ArrayList<String>();
		// excludeList.add("java.");
		// excludeList.add("javax.");
		// excludeList.add("sun.");
		// excludeList.add("androidx.");
		// excludeList.add("kotlin.");
		Options.v().set_exclude(excludeList);
		Options.v().set_no_bodies_for_excluded(true);
		
		Scene.v().loadNecessaryClasses();
				
		// ensure every SootClass instance has been resolved
		while (true) {
			try {
				// Scene.v().getClasses() may throw ConcurrentModificationException
				for (SootClass sootClass : Scene.v().getClasses()) {
					if (sootClass.isPhantom())
						continue;
					
					for (SootMethod sootMethod : sootClass.getMethods()) {
						if (!sootMethod.isConcrete())
							continue;

						try {
							// System.out.println(sootMethod.getSignature());
							sootMethod.retrieveActiveBody();
						} catch (Exception e) {
							Body emptyBody = Jimple.v().newBody(sootMethod);
							sootMethod.setActiveBody(emptyBody);
						}
					}
				}
				break;
			} catch (ConcurrentModificationException e) {
				e.printStackTrace();
			}
		}
		
		// we are only interested in methods of classes in white list
		for (SootClass sootClass : Scene.v().getClasses()) {
			if (!inWhitelist(sootClass.getName())) {
				sootClass.setPhantomClass();
				for (SootMethod sootMethod : sootClass.getMethods()) {
					sootMethod.setPhantom(true);
				}
			}
			// black-list
			if (sootClass.getName().startsWith("com.miui.maml")) {
				sootClass.setPhantomClass();
				for (SootMethod sootMethod : sootClass.getMethods()) {
					sootMethod.setPhantom(true);
				}
			}
		}
		
		// System.out.println("[Debug] init soot finish"); // Debug
	}
	
	// ---- //
	
	public static void initForAPK(String apkPath) {
		// clean up
		G.reset();
		Scene.v().releaseActiveHierarchy();
		Scene.v().releaseFastHierarchy();
		Scene.v().releaseCallGraph();
		System.gc();
		Unit2MethodMap = new HashMap<>();
				
		// set soot environment
		Options.v().set_src_prec(Options.src_prec_apk);
		Options.v().set_process_dir(Collections.singletonList(apkPath));
		// Options.v().set_android_jars(Configure.androidJars);
		Options.v().set_force_android_jar(Configure.androidJars + File.separator + "android-31" + File.separator + "android.jar");
		Options.v().set_allow_phantom_refs(true);
		Options.v().set_whole_program(true);
		Options.v().set_process_multiple_dex(true);
		Options.v().set_keep_line_number(false);
		Options.v().set_keep_offset(false);
		Options.v().set_ignore_resolving_levels(true);
		// Options.v().set_ignore_resolution_errors(true);
		Options.v().set_wrong_staticness(Options.wrong_staticness_fix);
		// Options.v().set_output_format(Options.output_format_class);
		// Options.v().set_output_dir(Configure.classesOutputDir);
		
		// exclude certain packages for better performance
		List<String> excludeList = new ArrayList<String>();
		excludeList.add("java.");
		excludeList.add("javax.");
		excludeList.add("sun.");
		excludeList.add("androidx.");
		excludeList.add("kotlin.");
		Options.v().set_exclude(excludeList);
		Options.v().set_no_bodies_for_excluded(true);
		
		Scene.v().loadNecessaryClasses();
				
		// ensure every SootClass instance has been resolved
		while (true) {
			try {
				// Scene.v().getClasses() may throw ConcurrentModificationException
				for (SootClass sootClass : Scene.v().getClasses()) {
					if (sootClass.isPhantom())
						continue;
					
					for (SootMethod sootMethod : sootClass.getMethods()) {
						if (!sootMethod.isConcrete())
							continue;

						try {
							// System.out.println(sootMethod.getSignature());
							sootMethod.retrieveActiveBody();
						} catch (Exception e) {
							Body emptyBody = Jimple.v().newBody(sootMethod);
							sootMethod.setActiveBody(emptyBody);
						}
					}
				}
				break;
			} catch (ConcurrentModificationException e) {
				e.printStackTrace();
			}
		}
		
		// we are only interested in methods of classes in white list
		for (SootClass sootClass : Scene.v().getClasses()) {
			if (!inWhitelist(sootClass.getName())) {
				sootClass.setPhantomClass();
				for (SootMethod sootMethod : sootClass.getMethods()) {
					sootMethod.setPhantom(true);
				}
			}
			// black-list
			if (sootClass.getName().startsWith("com.miui.maml")) {
				sootClass.setPhantomClass();
				for (SootMethod sootMethod : sootClass.getMethods()) {
					sootMethod.setPhantom(true);
				}
			}
			if (sootClass.getName().startsWith("android.support")) {
				sootClass.setPhantomClass();
				for (SootMethod sootMethod : sootClass.getMethods()) {
					sootMethod.setPhantom(true);
				}
			}
		}
		
		System.out.println("[Debug] init soot finish"); // Debug
	}
	
	public static void buildApkCallgraph() {
		Long startTime = System.currentTimeMillis();
		
		Options.v().setPhaseOption("cg", "enabled:true");
		Options.v().setPhaseOption("cg.cha", "enabled:true");
		Options.v().setPhaseOption("cg.cha", "string-constants:true");
		// Options.v().setPhaseOption("cg", "enabled:true");
		// Options.v().setPhaseOption("cg.spark", "enabled:true");
		// Options.v().setPhaseOption("cg.spark", "string-constants:true");
		
		HashSet<SootMethod> entryPoints = new HashSet<SootMethod>();
		for (SootClass sootClass : Scene.v().getClasses()) {
			if (sootClass.isPhantom())
				continue;
			for (SootMethod sootMethod : sootClass.getMethods()) {
				if (!sootMethod.isConcrete())
					continue;
				entryPoints.add(sootMethod);
			}
		}
		Scene.v().setEntryPoints(new ArrayList<SootMethod>(entryPoints));
		// PackManager.v().runPacks();
		PackManager.v().getPack("cg").apply();
		PackManager.v().getPack("wjtp").apply();
		
		Long midTime = System.currentTimeMillis();
		
		System.out.println(String.format("[Debug] build cg finish, spend %d seconds", (midTime - startTime) / 1000)); // Debug
		
		// prune
		/*
		boolean isStable = false;
		while (!isStable) {
			HashSet<Edge> removeEdges = new HashSet<Edge>();
			
			CallGraph cg = Scene.v().getCallGraph();
			Iterator<Edge> edgeIterator = cg.iterator();
			while (edgeIterator.hasNext()) {
				Edge edge = edgeIterator.next();
				if (edge.src().getName().equals("onTransact")
				 || edge.tgt().getName().equals("execute")
				 || edge.tgt().getName().equals("run")
				 || edge.tgt().getName().equals("handleMessage")) {
					removeEdges.add(edge);
				}
				if (edge.src().getName().equals("onCommand")
				 || edge.src().getName().contains("print")
				 || edge.src().getName().contains("dump")) {
					removeEdges.add(edge);
				}
				if (edge.src().getDeclaringClass().getName().contains("ShellCommand")) {
					removeEdges.add(edge);
				}
			}
		
			for (Edge removeEdge : removeEdges) {
				cg.removeEdge(removeEdge);
			}
			Scene.v().setCallGraph(cg);
			
			if (removeEdges.size() == 0)
				isStable = true;
		}
		
		Long endTime = System.currentTimeMillis();
		
		System.out.println(String.format("[Debug] prune cg finish, spend %d seconds", (endTime - midTime) / 1000)); // Debug
		*/
		
		// 
		for (SootClass sootClass : new ArrayList<SootClass>(Scene.v().getClasses())) {
			if (sootClass.isPhantom())
				continue;
			for (SootMethod sootMethod : new ArrayList<SootMethod>(sootClass.getMethods())) {
				if (!sootMethod.isConcrete())
					continue;
				Body body = sootMethod.retrieveActiveBody();
				for (Unit unit : body.getUnits()) {
					assert !Unit2MethodMap.containsKey(unit);
					Unit2MethodMap.put(unit, sootMethod);
				}
			}
		}
	}

}
