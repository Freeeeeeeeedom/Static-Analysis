/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.graph.callgraph;

import fj.Hash;
import org.checkerframework.checker.units.qual.A;
import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me

        Deque<JMethod> WL = new ArrayDeque<>();

        WL.push(entry);
        while(!WL.isEmpty()){
            JMethod method = WL.pop();
            if(callGraph.reachableMethods.contains(method)) continue;

            callGraph.addReachableMethod(method);
            for(Invoke callsite : callGraph.getCallSitesIn(method)){
                Set<JMethod> T = resolve(callsite);
                for(JMethod targetmethod : T){
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callsite), callsite, targetmethod));
                    WL.push(targetmethod);
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T = new HashSet<>();
        Subsignature method_signature = callSite.getMethodRef().getSubsignature();
        JClass method_class = callSite.getMethodRef().getDeclaringClass();

        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC, SPECIAL -> T.add(dispatch(method_class, method_signature));
            case VIRTUAL -> {
                T.add(dispatch(method_class, method_signature));
                Deque<JClass> dq = new ArrayDeque<>();
//                dq.addAll(hierarchy.getDirectSubinterfacesOf(method_class));
//                dq.addAll(hierarchy.getDirectImplementorsOf(method_class));
                dq.addAll(hierarchy.getDirectSubclassesOf(method_class));
                while(!dq.isEmpty()){
                    JClass c = dq.poll();
                    T.add(dispatch(c,method_signature));
                    dq.addAll(hierarchy.getDirectSubclassesOf(c));
//                    dq.addAll(hierarchy.getDirectSubinterfacesOf(c));
//                    dq.addAll(hierarchy.getDirectImplementorsOf(c));
                }
            }
            case INTERFACE -> {
                T.add(dispatch(method_class, method_signature));
                Deque<JClass> dq = new ArrayDeque<>();
                dq.addAll(hierarchy.getDirectSubinterfacesOf(method_class));
                dq.addAll(hierarchy.getDirectImplementorsOf(method_class));
//                dq.addAll(hierarchy.getDirectSubclassesOf(method_class));
                while(!dq.isEmpty()){
                    JClass c = dq.poll();
                    T.add(dispatch(c,method_signature));
                    dq.addAll(hierarchy.getDirectSubclassesOf(c));
                    dq.addAll(hierarchy.getDirectSubinterfacesOf(c));
                    dq.addAll(hierarchy.getDirectImplementorsOf(c));
                }
            }
        }
        T.remove(null);
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if(jclass==null) return null;
        if(jclass.getDeclaredMethod(subsignature)==null || jclass.getDeclaredMethod(subsignature).isAbstract()) return dispatch(jclass.getSuperClass(),subsignature);
        return jclass.getDeclaredMethod(subsignature);
    }
}
