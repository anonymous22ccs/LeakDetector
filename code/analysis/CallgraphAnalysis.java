package ??.??.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

import soot.Body;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;

public class CallgraphAnalysis {
	
	private static int maxInvokeDeep = 8; // "deep" refers to the number of edges
	private static int maxTgtNumber = 8;
	
	// ---- //
	
	// get Callgraph paths from (Non-Nullable) leaf to (Nullable) root
	
	public static HashSet<ArrayList<SootMethod>> cmpPathBackward(SootMethod leaf, SootMethod root, int deepLimit) {
		HashSet<ArrayList<SootMethod>> paths = new HashSet<ArrayList<SootMethod>>(); // result
		
		// check
		if (deepLimit >= maxInvokeDeep)
			deepLimit = maxInvokeDeep;
		
		// compute
		ArrayList<SootMethod> curPath = new ArrayList<SootMethod>();
		curPath.add(leaf);
		
		if ((root != null && leaf.getSignature().equals(root.getSignature()))
		 || deepLimit == 0) {
			paths.add(curPath);
			return paths;
		}
		
		CallGraph cg = Scene.v().getCallGraph();
		
		if (cg.edgesInto(leaf).hasNext() == false) { // no caller
			paths.add(curPath);
			return paths;
		}
		
		Iterator<Edge> edgeIterator = cg.edgesInto(leaf);
		int callerCount = 0;
		while (edgeIterator.hasNext()) {
			Edge edge = edgeIterator.next();
			String edgeSrcClassName = edge.src().getDeclaringClass().getName();
			String edgeTgtClassName = edge.tgt().getDeclaringClass().getName();
			if (!edgeSrcClassName.equals(edgeTgtClassName))
				callerCount++;
		}
		if (callerCount > maxTgtNumber) {
			paths.add(curPath);
			System.err.println(String.format("callerCount %d exceeds %d", callerCount, maxTgtNumber)); // Debug
			return paths;
		} else {
			edgeIterator = cg.edgesInto(leaf); // reset
		}
		
		while (edgeIterator.hasNext()) {
			Edge edge = edgeIterator.next();
			// System.out.println(edge); // Debug
			SootMethod src = edge.src();
			if ((root != null && src.getSignature().equals(root.getSignature()))
			 || deepLimit == 1) {
				ArrayList<SootMethod> newPath = new ArrayList<SootMethod>(curPath);
				newPath.add(src);
				paths.add(newPath);
			} else {
				if (cg.edgesInto(src).hasNext()) {
					cmpPathBackwardInner(src, root, curPath, deepLimit, paths);
				} else {
					ArrayList<SootMethod> newPath = new ArrayList<SootMethod>(curPath);
					newPath.add(src);
					paths.add(newPath);
				}
			}
		}
		
		// output
		return paths;
	}
	private static void cmpPathBackwardInner(SootMethod leaf, SootMethod root, ArrayList<SootMethod> path, int deepLimit, /* output */ HashSet<ArrayList<SootMethod>> paths) {
		assert !leaf.getSignature().equals(root.getSignature()); // leaf != root
		if (path.contains(leaf)) { // recursive invocation
			ArrayList<SootMethod> newPath = new ArrayList<SootMethod>(path);
			paths.add(newPath);
			return;
		}
		
		// check
		if (deepLimit >= maxInvokeDeep)
			deepLimit = maxInvokeDeep;
		
		// compute
		ArrayList<SootMethod> curPath = new ArrayList<SootMethod>(path);
		curPath.add(leaf);
		
		if (curPath.size() > maxInvokeDeep || curPath.size() > deepLimit)
			return; // conservative
		
		CallGraph cg = Scene.v().getCallGraph();
		
		if (cg.edgesInto(leaf).hasNext() == false) { // no caller
			paths.add(curPath);
			return;
		}
		
		Iterator<Edge> edgeIterator = cg.edgesInto(leaf);
		int callerCount = 0;
		while (edgeIterator.hasNext()) {
			edgeIterator.next();
			Edge edge = edgeIterator.next();
			String edgeSrcClassName = edge.src().getDeclaringClass().getName();
			String edgeTgtClassName = edge.tgt().getDeclaringClass().getName();
			if (!edgeSrcClassName.equals(edgeTgtClassName))
				callerCount++;
		}
		if (callerCount > maxTgtNumber) {
			paths.add(curPath);
			System.err.println(String.format("callerCount %d exceeds %d", callerCount, maxTgtNumber)); // Debug
			return;
		} else {
			edgeIterator = cg.edgesInto(leaf); // reset
		}
		
		while (edgeIterator.hasNext()) {
			Edge edge = edgeIterator.next();
			// System.out.println(edge); // Debug
			SootMethod src = edge.src();
			if ((root != null && src.getSignature().equals(root.getSignature()))
			 || curPath.size() == deepLimit) {
				ArrayList<SootMethod> newPath = new ArrayList<SootMethod>(curPath);
				newPath.add(src);
				paths.add(newPath);
			} else {
				if (cg.edgesInto(src).hasNext()) {
					cmpPathBackwardInner(src, root, curPath, deepLimit, paths);
				} else {
					ArrayList<SootMethod> newPath = new ArrayList<SootMethod>(curPath);
					newPath.add(src);
					paths.add(newPath);
				}
			}
		}
	}
	
	// ---- //
	
	// get Callgraph paths from (Non-Nullable) root to (Nullable) leaf
	
	public static HashSet<ArrayList<SootMethod>> cmpPathForward(SootMethod leaf, SootMethod root, int deepLimit) {
		HashSet<ArrayList<SootMethod>> paths = new HashSet<ArrayList<SootMethod>>(); // result
		
		// check
		if (deepLimit >= maxInvokeDeep)
			deepLimit = maxInvokeDeep;
		
		// compute
		ArrayList<SootMethod> curPath = new ArrayList<SootMethod>();
		curPath.add(root);
		
		if ((leaf != null && root.getSignature().equals(leaf.getSignature()))
		 || deepLimit == 0) {
			paths.add(curPath);
			return paths;
		}
		
		CallGraph cg = Scene.v().getCallGraph();
		
		if (cg.edgesOutOf(root).hasNext() == false) { // no callee
			paths.add(curPath);
			return paths;
		}
		
		HashSet<Unit> filterUnits = new HashSet<Unit>();
		if (root.isConcrete()) {
			Body body = root.retrieveActiveBody();
			for (Unit unit : body.getUnits()) {
				Iterator<Edge> callees = cg.edgesOutOf(unit);
				int calleeCount = 0;
				while (callees.hasNext()) {
					callees.next();
					calleeCount++;
				}
				if (calleeCount > maxTgtNumber) {
					filterUnits.add(unit);
				}
			}
		}
		
		Iterator<Edge> edgeIterator = cg.edgesOutOf(root);
		while (edgeIterator.hasNext()) {
			Edge edge = edgeIterator.next();
			if (edge.srcUnit() != null && filterUnits.contains(edge.srcUnit()))
				continue;
			
			SootMethod tgt = edge.tgt();
			if ((leaf != null && tgt.getSignature().equals(leaf.getSignature()))
			 || deepLimit == 1) {
				ArrayList<SootMethod> newPath = new ArrayList<SootMethod>(curPath);
				newPath.add(tgt);
				paths.add(newPath);
			} else {
				if (cg.edgesOutOf(tgt).hasNext()) {
					cmpPathForwardInner(leaf, tgt, curPath, deepLimit, paths);
				} else {
					ArrayList<SootMethod> newPath = new ArrayList<SootMethod>(curPath);
					newPath.add(tgt);
					paths.add(newPath);
				}
			}
		}
		
		// output
		return paths;
	}
	private static void cmpPathForwardInner(SootMethod leaf, SootMethod root, ArrayList<SootMethod> path, int deepLimit, /* output */ HashSet<ArrayList<SootMethod>> paths) {
		assert !root.getSignature().equals(leaf.getSignature()); // leaf != root
		if (path.contains(root)) { // recursive invocation
			ArrayList<SootMethod> newPath = new ArrayList<SootMethod>(path);
			paths.add(newPath);
			return;
		}
		
		// check
		if (deepLimit >= maxInvokeDeep)
			deepLimit = maxInvokeDeep;
		
		// compute
		ArrayList<SootMethod> curPath = new ArrayList<SootMethod>(path);
		curPath.add(root);
		
		if (curPath.size() > maxInvokeDeep || curPath.size() > deepLimit)
			return; // conservative
		
		CallGraph cg = Scene.v().getCallGraph();
		
		if (cg.edgesOutOf(root).hasNext() == false) { // no callee
			paths.add(curPath);
			return;
		}
		
		HashSet<Unit> filterUnits = new HashSet<Unit>();
		if (root.isConcrete()) {
			Body body = root.retrieveActiveBody();
			for (Unit unit : body.getUnits()) {
				Iterator<Edge> callees = cg.edgesOutOf(unit);
				int calleeCount = 0;
				while (callees.hasNext()) {
					callees.next();
					calleeCount++;
				}
				if (calleeCount > maxTgtNumber) {
					filterUnits.add(unit);
				}
			}
		}
		
		Iterator<Edge> edgeIterator = cg.edgesOutOf(root);
		while (edgeIterator.hasNext()) {
			Edge edge = edgeIterator.next();
			if (edge.srcUnit() != null && filterUnits.contains(edge.srcUnit()))
				continue;
			
			SootMethod tgt = edge.tgt();
			if ((leaf != null && tgt.getSignature().equals(leaf.getSignature()))
			 || curPath.size() == deepLimit) {
				ArrayList<SootMethod> newPath = new ArrayList<SootMethod>(curPath);
				newPath.add(tgt);
				paths.add(newPath);
			} else {
				if (cg.edgesOutOf(tgt).hasNext()) {
					cmpPathForwardInner(leaf, tgt, curPath, deepLimit, paths);
				} else {
					ArrayList<SootMethod> newPath = new ArrayList<SootMethod>(curPath);
					newPath.add(tgt);
					paths.add(newPath);
				}
			}
		}
	}

}
