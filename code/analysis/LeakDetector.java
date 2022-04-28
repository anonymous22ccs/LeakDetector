package ??.??.analysis;

import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashSet;

import ??.??.analysis.app.AppIntentAnalysis;
import ??.??.configure.SootEnvironment;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;

public class LeakDetector {
	
	private static void redirectSysOutput() {
		try {
			PrintStream ps = new PrintStream(new FileOutputStream("output.log"));
			System.setOut(ps);
		} catch(Exception e) {
			e.printStackTrace();
		}
	}
	
	public static long time4Process1 = 0;
	public static long time4Process2 = 0;
	public static long time4Process3 = 0;
	public static long time4Process4 = 0;
	
	public static HashSet<String> classSet = new HashSet<String>();
	public static HashSet<String> methodSet = new HashSet<String>();
	
	public static void main(String[] args) {
		redirectSysOutput();
		
		Long startProcess1 = System.nanoTime();
		
		SootEnvironment.init();
		SootEnvironment.buildCallgraph();
		
		Long endProcess1 = System.nanoTime();
		time4Process1 += (endProcess1 - startProcess1);
		// System.err.println(String.format("[Output] Process-1, spend %f seconds", (endProcess1 - startProcess1) * 1.0 / 1000000000)); // Debug
		
		PermissionFinder.analyze();
		
		Long endProcess2 = System.nanoTime();
		time4Process2 += (endProcess2 - endProcess1);
		// System.err.println(String.format("[Output] Process-2, spend %f seconds", (endProcess2 - endProcess1) * 1.0 / 1000000000)); // Debug
		
		IntentAnalysis.analyze();
		
		Long endProcess3 = System.nanoTime();
		time4Process3 += (endProcess3 - endProcess2);
		// System.err.println(String.format("[Output] Process-3, spend %f seconds", (endProcess3 - endProcess2) * 1.0 / 1000000000)); // Debug
		
		// collect leaked fields
		HashSet<SootField> leakedFields = new HashSet<SootField>();
		for (Unit putExtraUnit : IntentAnalysis.putExtra2fieldMap.keySet()) {
			leakedFields.addAll(IntentAnalysis.putExtra2fieldMap.get(putExtraUnit));
		}
		for (SootField leakedField : leakedFields) {
			if (PermissionFinder.field2paths.containsKey(leakedField)) {
				System.out.println("Leaked Field: " + leakedField);
				// details about leaked Intent
				for (Unit putExtraUnit : IntentAnalysis.putExtra2fieldMap.keySet()) {
					if (IntentAnalysis.putExtra2fieldMap.get(putExtraUnit).contains(leakedField)) {
						for (String actionName : IntentAnalysis.putExtra2actionMap.get(putExtraUnit))
							System.out.println("\tIntent: " + putExtraUnit + ", Action: " + actionName + " in [ " + SootEnvironment.Unit2MethodMap.get(putExtraUnit).getSignature() + "]");
					}
				}
				// details about leaked Field
				HashSet<ArrayList<SootMethod>> paths = PermissionFinder.field2paths.get(leakedField);
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
			}
		}
		
		// collect leaked src methods
		// HashSet<SootMethod> leakedMethods = new HashSet<SootMethod>();
		// for (Unit putExtraUnit : IntentAnalysis.putExtra2srcMethodMap.keySet()) {
			// leakedMethods.addAll(IntentAnalysis.putExtra2srcMethodMap.get(putExtraUnit));
		// }
		// for (SootMethod leakedMethod : leakedMethods) {
			// if (PermissionFinder.srcMethod2paths.containsKey(leakedMethod)) {
				// System.out.println("Leaked Method: " + leakedMethod);
			// }
		// }
		
		// collect leaked classes 
		HashSet<SootClass> leakedClasses = new HashSet<SootClass>();
		for (Unit putExtraUnit : IntentAnalysis.putExtra2classMap.keySet()) {
			leakedClasses.addAll(IntentAnalysis.putExtra2classMap.get(putExtraUnit));
		}
		for (SootClass leakedClass : leakedClasses) {
			if (PermissionFinder.class2paths.containsKey(leakedClass)) {
				System.out.println("Leaked Class: " + leakedClass);
				// details about leaked Intent
				for (Unit putExtraUnit : IntentAnalysis.putExtra2classMap.keySet()) {
					if (IntentAnalysis.putExtra2classMap.get(putExtraUnit).contains(leakedClass)) {
						for (String actionName : IntentAnalysis.putExtra2actionMap.get(putExtraUnit))
							System.out.println("\tIntent: " + putExtraUnit + ", Action: " + actionName + " in [ " + SootEnvironment.Unit2MethodMap.get(putExtraUnit).getSignature() + "]");
					}
				}
				// details about leaked Class
				HashSet<ArrayList<SootMethod>> paths = PermissionFinder.class2paths.get(leakedClass);
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
			}
		}
		
		Long endProcess4 = System.nanoTime();
		time4Process4 += (endProcess4 - endProcess3);
		// System.err.println(String.format("[Output] Process-4, spend %f seconds", (endProcess4 - endProcess3) * 1.0 / 1000000000)); // Debug
		
		// find privileged Intent
		IntentFilterAnalysis.analyze();
		
		//
		for (SootClass sootClass : Scene.v().getClasses()) {
			classSet.add(sootClass.getName());
			for (SootMethod sootMethod : sootClass.getMethods()) {
				methodSet.add(sootMethod.getSignature());
			}
		}
		
		// ---- //
		
		AppIntentAnalysis.analyze();
		
		// ---- //
		
		System.out.println(String.format("[Output] Process-1, spend %f seconds", time4Process1 * 1.0 / 1000000000)); // Debug
		System.out.println(String.format("[Output] Process-2, spend %f seconds", time4Process2 * 1.0 / 1000000000)); // Debug
		System.out.println(String.format("[Output] Process-3, spend %f seconds", (time4Process3 + time4Process4) * 1.0 / 1000000000)); // Debug
		// System.out.println(String.format("[Output] Process-4, spend %f seconds", time4Process4 * 1.0 / 1000000000)); // Debug
		
		System.out.println(String.format("[Output] Framework Class: %d", classSet.size())); // Debug
		System.out.println(String.format("[Output] Framework Method: %d", methodSet.size())); // Debug
		
		System.out.println(String.format("[Output] Sensitive Field: %d", PermissionFinder.field2paths.keySet().size())); // Debug
		System.out.println(String.format("[Output] Sensitive Class: %d", PermissionFinder.class2paths.keySet().size())); // Debug
		
		System.out.println();
		
		for (SootField sensitiveField : PermissionFinder.field2paths.keySet()) {
			System.out.println("[Sensitive Field] " + sensitiveField.getSignature());
			HashSet<ArrayList<SootMethod>> paths = PermissionFinder.field2paths.get(sensitiveField);
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
		}
		
		for (SootClass sensitiveClass : PermissionFinder.class2paths.keySet()) {
			System.out.println("[Sensitive Class] " + sensitiveClass.getName());
			HashSet<ArrayList<SootMethod>> paths = PermissionFinder.class2paths.get(sensitiveClass);
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
		}
		
		// privileged Intent
		for (String privilegedIntent : IntentFilterAnalysis.privilegedIntents) {
			System.out.println(String.format("[Privileged Intent] %s", privilegedIntent));
		}
	}

}
