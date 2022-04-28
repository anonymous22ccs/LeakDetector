package ??.??.analysis;

import java.util.HashMap;
import java.util.HashSet;

import ??.??.configure.SootEnvironment;
import soot.Scene;
import soot.SootClass;

public class SysServiceAnalysis {
	// global
	public static HashSet<SootClass> sysServiceSet = new HashSet<SootClass>();
	
	public static void findServices() {
		for (SootClass sootClass : Scene.v().getClasses()) {
			System.out.println(String.format("%s", sootClass.getName()));
			if (sootClass.hasSuperclass())
				System.out.println(String.format("\tsuper: %s", sootClass.getSuperclass().getName()));
			for (SootClass interfaceClass : sootClass.getInterfaces())
				System.out.println(String.format("\tinterface: %s", interfaceClass.getName()));
		}
		
		HashSet<SootClass> stubClassSet = new HashSet<SootClass>();
		for (SootClass sootClass : Scene.v().getClasses()) {
			// system service's Stub class commonly extends android.os.Binder and has at least one interface class
			if (!sootClass.hasSuperclass())
				continue;
			if (!sootClass.getSuperclass().getName().equals("android.os.Binder"))
				continue;
			if (sootClass.getInterfaceCount() <= 0)
				continue;
			stubClassSet.add(sootClass);
			System.out.println(String.format("stub class: %s", sootClass.getName()));
			for (SootClass interfaceClass : sootClass.getInterfaces())
				System.out.println(String.format("\tinterface class: %s", interfaceClass.getName()));
		}
		
		// 
		HashMap<SootClass, SootClass> stub2serviceMap = new HashMap<SootClass, SootClass>();
		for (SootClass stubClass : stubClassSet)
			stub2serviceMap.put(stubClass, null);
		
		HashSet<SootClass> serviceClassSet = new HashSet<SootClass>();
		for (SootClass sootClass : Scene.v().getClasses()) {
			// system service's class commonly extends its Stub class
			if (!sootClass.hasSuperclass())
				continue;
			if (stubClassSet.contains(sootClass.getSuperclass())) {
				serviceClassSet.add(sootClass);
				stub2serviceMap.put(sootClass.getSuperclass(), sootClass);
			}
		}
		
		for (SootClass stubClass : stub2serviceMap.keySet()) {
			SootClass serviceClass = stub2serviceMap.get(stubClass);
			if (serviceClass != null)
				System.out.println(String.format("service class: %s", serviceClass.getName())); // Debug
			else
				System.out.println(String.format("service class: null")); // Debug
			System.out.println(String.format("\tstub class: %s", stubClass.getName())); // Debug
		}
		//
	}
	
	// ---- //
	
	// module-test
	public static void main(String[] args) {
		SootEnvironment.init();
		
		findServices();
	}
	
}
