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

package pascal.taie.analysis.pta.ci;

import fj.P;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.checkerframework.checker.units.qual.C;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;
import java.util.Stack;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if(!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            for (Stmt stmt : method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            VarPtr p =  pointerFlowGraph.getVarPtr(stmt.getLValue());
            workList.addEntry(p,new PointsToSet(heapModel.getObj(stmt)));

            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            VarPtr p = pointerFlowGraph.getVarPtr(stmt.getLValue());
            VarPtr q = pointerFlowGraph.getVarPtr(stmt.getRValue());
            addPFGEdge(q,p);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()){
                JField field = stmt.getFieldRef().resolve();
                //获取load的字段 y = T.f
                StaticField f = pointerFlowGraph.getStaticField(field);
                VarPtr y = pointerFlowGraph.getVarPtr(stmt.getLValue());
                addPFGEdge(f,y);

            }

            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()){
                // T.f = y
                StaticField f = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                VarPtr y = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(y,f);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()){
                JMethod method = resolveCallee(null,stmt);

                Edge<Invoke,JMethod> edge = new Edge<>(CallKind.STATIC, stmt,method);
                if(callGraph.addEdge(edge)){
                    addReachable(method);
                    for(int i=0;i<method.getParamCount();i++){
                        addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue().getArg(i)),pointerFlowGraph.getVarPtr(method.getIR().getParam(i)));
                    }
                    for (Var returnVar : method.getIR().getReturnVars()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(returnVar),pointerFlowGraph.getVarPtr(stmt.getLValue()));
                    }
                }
            }
            return StmtVisitor.super.visit(stmt);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(!pointerFlowGraph.addEdge(source,target)){
            return;
        }
        if(!source.getPointsToSet().isEmpty()){
            workList.addEntry(target,source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();

            PointsToSet delta = propagate(entry.pointer(),entry.pointsToSet());
            //propage返回delta

            if(entry.pointer() instanceof VarPtr){
                Var var =  ((VarPtr) entry.pointer()).getVar();
                for(Obj obj : delta){
                    List<LoadArray> loadarrays   = var.getLoadArrays();
                    List<StoreArray> storearrays = var.getStoreArrays();
                    List<LoadField>  loadfields  = var.getLoadFields();
                    List<StoreField>  storefileds =var.getStoreFields();

                    loadarrays.forEach(stmt  -> addPFGEdge(pointerFlowGraph.getArrayIndex(obj),pointerFlowGraph.getVarPtr(stmt.getLValue())));
                    storearrays.forEach(stmt -> addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),pointerFlowGraph.getArrayIndex(obj)));
                    loadfields.forEach(stmt  -> addPFGEdge(pointerFlowGraph.getInstanceField(obj,stmt.getFieldAccess().getFieldRef().resolve()),pointerFlowGraph.getVarPtr(stmt.getLValue())));
                    storefileds.forEach(stmt -> addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),pointerFlowGraph.getInstanceField(obj,stmt.getFieldAccess().getFieldRef().resolve())));

                    processCall(var,obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me

        PointsToSet delta = new PointsToSet();
        pointsToSet.forEach(p ->{
            if(pointer.getPointsToSet().addObject(p)) delta.addObject(p);
        });
        if(!delta.isEmpty()){
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ->{
                workList.addEntry(succ,delta);
            });
        }

//        if(!pointsToSet.isEmpty()){
//            for (Obj obj : pointsToSet) {
//                pointer.getPointsToSet().addObject(obj);
//            }
//            for (Pointer pointer1 : pointerFlowGraph.getSuccsOf(pointer)) {
//                workList.addEntry(pointer1,pointsToSet);
//            }
//        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        var.getInvokes().forEach(invoke->{
            JMethod method = resolveCallee(recv,invoke);
            workList.addEntry(pointerFlowGraph.getVarPtr(method.getIR().getThis()),new PointsToSet(recv));

            CallKind callkind = null;
            if(invoke.isStatic()) callkind = CallKind.STATIC;
            if(invoke.isInterface()) callkind = CallKind.INTERFACE;
            if(invoke.isSpecial()) callkind = CallKind.SPECIAL;
            if(invoke.isVirtual()) callkind = CallKind.VIRTUAL;

            Edge<Invoke,JMethod> edge = new Edge<>(callkind,invoke,method);
            if(callGraph.addEdge(edge)){
                addReachable(method);
                for(int i=0;i<method.getParamCount();i++){
                    addPFGEdge(pointerFlowGraph.getVarPtr(invoke.getRValue().getArg(i)),pointerFlowGraph.getVarPtr(method.getIR().getParam(i)));
                }
                if(invoke.getLValue()!=null){
                    for (Var returnVar : method.getIR().getReturnVars()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(returnVar),pointerFlowGraph.getVarPtr(invoke.getLValue()));
                    }
                }
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
