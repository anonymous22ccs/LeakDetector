package ??.??.analysis.app;

import java.util.HashSet;
import java.util.Iterator;

import ??.??.analysis.IntentFilterAnalysis;
import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ClassConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.infoflow.android.axml.AXmlNode;
import soot.jimple.infoflow.android.manifest.ProcessManifest;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;

public class AppManifestAnalysis {
	// exported
	public static HashSet<SootClass> exportedActivitySet;
	
	public static void analyze(String apkPath) {
		exportedActivitySet = new HashSet<SootClass>(); // clean and init
		
		ProcessManifest manifest = null;
		try {
			manifest = new ProcessManifest(apkPath);
			
			String packageName = manifest.getPackageName();
			for (AXmlNode activityNode : manifest.getAXml().getNodesWithTag("activity")) {
				if (!activityNode.hasAttribute("name"))
					continue;
				String activityName = activityNode.getAttribute("name").getValue().toString();
				activityName = adjustComponentName(packageName, activityName);
				
				// 1-exported
				boolean isExported = false;
				if (activityNode.hasAttribute("exported")) {
					String exported = activityNode.getAttribute("exported").getValue().toString();
					if (exported.equals("true"))
						isExported = true;
				} else {
					if (!activityNode.getChildrenWithTag("intent-filter").isEmpty())
						isExported = true;
				}
				// 2-permission
				boolean hasPermission = false;
				if (activityNode.hasAttribute("permission")) {
					String permission = activityNode.getAttribute("permission").getValue().toString();
					if (!permission.equals(""))
						hasPermission = true;
				}
				// 3-fragment
				HashSet<SootClass> fragmentSet = new HashSet<SootClass>();
				for (AXmlNode metaNode : activityNode.getChildrenWithTag("meta-data")) {
					if (metaNode.getAttribute("name").getValue().toString().contains("FRAGMENT")
					 || metaNode.getAttribute("name").getValue().toString().contains("fragment")
					 || metaNode.getAttribute("name").getValue().toString().contains("Fragment")) {
						String fragmentName = metaNode.getAttribute("value").getValue().toString();
						fragmentName = adjustComponentName(packageName, fragmentName);
						SootClass fragmentClass = Scene.v().getSootClass(fragmentName);
						fragmentSet.add(fragmentClass);
					}
				}
				
				if (isExported == true && hasPermission == false) {
					SootClass activityClass = Scene.v().getSootClass(activityName);
					exportedActivitySet.add(activityClass);
					exportedActivitySet.addAll(fragmentSet);
				}
			}
			
			// find privileged Intents
			for (AXmlNode activityNode : manifest.getAXml().getNodesWithTag("activity")) {
				for (AXmlNode filterNode : activityNode.getChildrenWithTag("intent-filter")) {
					if (filterNode.hasAttribute("priority")) {
						for (AXmlNode actionNode : filterNode.getChildrenWithTag("action")) {
							if (actionNode.hasAttribute("name")) {
								String actionName = actionNode.getAttribute("name").getValue().toString();
								IntentFilterAnalysis.privilegedIntents.add(actionName);
							}
						}
					}
				}
			}
			for (AXmlNode receiverNode : manifest.getAXml().getNodesWithTag("receiver")) {
				for (AXmlNode filterNode : receiverNode.getChildrenWithTag("intent-filter")) {
					if (filterNode.hasAttribute("priority")) {
						for (AXmlNode actionNode : filterNode.getChildrenWithTag("action")) {
							if (actionNode.hasAttribute("name")) {
								String actionName = actionNode.getAttribute("name").getValue().toString();
								IntentFilterAnalysis.privilegedIntents.add(actionName);
							}
						}
					}
				}
			}
		} catch(Exception e) {
			if (manifest != null) {
				manifest.close();
			}
		}
		
		// find Fragment
		for (SootClass activityClass : new HashSet<SootClass>(exportedActivitySet)) {
			analyzeFragment(activityClass);
		}
	}
	
	private static void analyzeFragment(SootClass activityClass) {
		// System.err.println(activityClass.toString()); // Debug
		
		CallGraph cg = Scene.v().getCallGraph();
		
		SootClass activityClass1 = Scene.v().getSootClassUnsafe("android.app.Activity", true);
		SootClass activityClass2 = Scene.v().getSootClassUnsafe("android.support.v4.app.AppCompatActivity", true);
		SootClass activityClass3 = Scene.v().getSootClassUnsafe("android.support.v7.app.AppCompatActivity", true);
		SootClass activityClass4 = Scene.v().getSootClassUnsafe("androidx.appcompat.app.AppCompatActivity", true);
		
		SootClass fragmentClass1 = Scene.v().getSootClassUnsafe("android.app.Fragment", true);
		SootClass fragmentClass2 = Scene.v().getSootClassUnsafe("android.support.v4.app.Fragment", true);
		SootClass fragmentClass3 = Scene.v().getSootClassUnsafe("androidx.fragment.app.Fragment", true);
		
		for (SootMethod activityMethod : activityClass.getMethods()) {
			if (!activityMethod.isConcrete())
				continue;
			Body body = activityMethod.retrieveActiveBody();
			// System.err.println(activityMethod.getSignature()); // Debug
			for (Unit unit : body.getUnits()) {
				// System.err.println("\t" + unit); // Debug
				Stmt stmt = (Stmt) unit;
				
				for (ValueBox valueBox : stmt.getUseAndDefBoxes()) {
					Value value = valueBox.getValue();
					// System.err.println("\t\t" + value); // Debug
					if (value instanceof StringConstant || value instanceof ClassConstant) {
						String valueRaw = "";
						if (value instanceof StringConstant)
							valueRaw = ((StringConstant) value).value;
						if (value instanceof ClassConstant)
							valueRaw = ((ClassConstant) value).value;
						// System.err.println("\t\t\t" + valueRaw); // Debug
						
						if (valueRaw.startsWith("L") && valueRaw.endsWith(";")) {
							valueRaw = valueRaw.substring(1);
							valueRaw = valueRaw.replace(";", "").replace("/", ".");
						}
						
						try {
							SootClass candidateClass = Scene.v().getSootClass(valueRaw);
							if (!candidateClass.isConcrete())
								continue;
							
							HashSet<SootClass> superClasses = new HashSet<SootClass>();
							SootClass superClass = candidateClass;
							while ((superClass = superClass.getSuperclassUnsafe()) != null) {
								superClasses.add(superClass);
							}
							
							if ((superClasses.contains(fragmentClass1) || superClasses.contains(fragmentClass2) || superClasses.contains(fragmentClass3))
							 && (!superClasses.contains(activityClass1) && !superClasses.contains(activityClass2) && !superClasses.contains(activityClass3) && !superClasses.contains(activityClass4))) {
								exportedActivitySet.add(candidateClass);
								// System.err.println("\t" + candidateClass.toString()); // Debug
							}
						} catch(Exception e) {}
					}
					if (value instanceof InvokeExpr) {
						Iterator<Edge> edges = cg.edgesOutOf(unit);
						while (edges.hasNext()) {
							SootClass candidateClass = edges.next().tgt().getDeclaringClass();
							if (!candidateClass.isConcrete())
								continue;
							
							HashSet<SootClass> superClasses = new HashSet<SootClass>();
							SootClass superClass = candidateClass;
							while ((superClass = superClass.getSuperclassUnsafe()) != null) {
								superClasses.add(superClass);
							}
							
							if ((superClasses.contains(fragmentClass1) || superClasses.contains(fragmentClass2) || superClasses.contains(fragmentClass3))
							 && (!superClasses.contains(activityClass1) && !superClasses.contains(activityClass2) && !superClasses.contains(activityClass3) && !superClasses.contains(activityClass4))) {
								exportedActivitySet.add(candidateClass);
								// System.err.println("\t" + candidateClass.toString()); // Debug
							}
						}
					}
				}
			}
		}
	}
	
	private static String adjustComponentName(String packageName, String componentName) {
		String realName = null;
		SootClass componentClass = Scene.v().getSootClassUnsafe(componentName);
		if (componentClass == null || componentClass.isPhantom()) {
			if (componentClass.getName().startsWith("."))
				componentName = packageName + componentName;
			else
				componentName = packageName + "." + componentName;
			
			componentClass = Scene.v().getSootClassUnsafe(componentName);
			assert componentClass.isApplicationClass();
			
			realName = componentName;
		} else
			realName = componentName;
		
		return realName;
	}

}
