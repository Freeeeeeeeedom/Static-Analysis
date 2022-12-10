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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if(callGraph.contains(csMethod)) return;
        callGraph.addReachableMethod(csMethod);
        csMethod.getMethod().getIR().getStmts().forEach(stmt -> {
            stmt.accept(new StmtProcessor(csMethod));
        });

    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);

            Context objContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(objContext, obj);

            PointsToSet pointsToSet = PointsToSetFactory.make(csObj);
            Pointer pointer = csManager.getCSVar(context, stmt.getLValue());

            workList.addEntry(pointer, pointsToSet);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            CSVar left  = csManager.getCSVar(context,stmt.getLValue());
            CSVar right = csManager.getCSVar(context,stmt.getRValue());
            addPFGEdge(right,left);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if(!stmt.isStatic()) return StmtVisitor.super.visit(stmt);
            JField field = stmt.getFieldRef().resolve();
            StaticField f = csManager.getStaticField(field);
            CSVar var = csManager.getCSVar(context,stmt.getLValue());
            addPFGEdge(f,var);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if(!stmt.isStatic()) return StmtVisitor.super.visit(stmt);
            JField field = stmt.getFieldRef().resolve();
            StaticField f = csManager.getStaticField(field);
            CSVar var = csManager.getCSVar(context,stmt.getRValue());
            addPFGEdge(var,f);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if(!stmt.isStatic()) return StmtVisitor.super.visit(stmt);

//            CSMethod csm = csManager.getCSMethod(context,stmt.getMethodRef().resolve());
//            CSCallSite callsite = csManager.getCSCallSite(context,stmt);
//
//            Context ct = contextSelector.selectContext(callsite,csm.getMethod());
////            System.out.println(ct);
//            Edge<CSCallSite,CSMethod> edge = new Edge<>(CallKind.STATIC,callsite,csm);
//            if(callGraph.addEdge(edge)){
//                addReachable(csm);
//                for(int i=0;i<csm.getMethod().getParamCount();i++){
//                    addPFGEdge(csManager.getCSVar(context,stmt.getRValue().getArg(i)),csManager.getCSVar(ct,csm.getMethod().getIR().getParam(i)));
//                }
//                if(stmt.getLValue()!=null) {
//                    for(Var returnvar : csm.getMethod().getIR().getReturnVars()){
//                        addPFGEdge(csManager.getCSVar(ct,returnvar),csManager.getCSVar(context,stmt.getLValue()));
//                    }
//                }
//            }

            JMethod Jmethod = stmt.getMethodRef().resolve();
            CSCallSite Cscallsite = csManager.getCSCallSite(context,stmt);
            Context Ct = contextSelector.selectContext(Cscallsite,Jmethod);
            CSMethod Csmethod = csManager.getCSMethod(Ct,Jmethod);

            Edge<CSCallSite,CSMethod> edge = new Edge<>(CallKind.STATIC,Cscallsite,Csmethod);
            if(callGraph.addEdge(edge)){
                addReachable(Csmethod);

                for(int i=0;i<Jmethod.getParamCount();i++){
                    addPFGEdge(csManager.getCSVar(context,stmt.getRValue().getArg(i)),csManager.getCSVar(Ct,Jmethod.getIR().getVar(i)));
                }
                if(stmt.getLValue()!=null){
                    for(Var returnvar : Jmethod.getIR().getReturnVars()){
                        addPFGEdge(csManager.getCSVar(Ct,returnvar),csManager.getCSVar(context,stmt.getLValue()));
                    }
                }
            }
            return StmtVisitor.super.visit(stmt);
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(!pointerFlowGraph.addEdge(source,target)) return;
        if(!source.getPointsToSet().isEmpty()) workList.addEntry(target,source.getPointsToSet());
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(),entry.pointsToSet());
            if(entry.pointer() instanceof CSVar csvar){
                Var var = csvar.getVar();
                for(CSObj csobj : delta){
                    var.getStoreFields().forEach(stmt -> addPFGEdge(csManager.getCSVar(csvar.getContext(),stmt.getRValue()),csManager.getInstanceField(csobj,stmt.getFieldAccess().getFieldRef().resolve())));
                    var.getLoadFields().forEach(stmt -> addPFGEdge(csManager.getInstanceField(csobj,stmt.getFieldAccess().getFieldRef().resolve()),csManager.getCSVar(csvar.getContext(),stmt.getLValue())));
                    var.getStoreArrays().forEach(stmt -> addPFGEdge(csManager.getCSVar(csvar.getContext(),stmt.getRValue()),csManager.getArrayIndex(csobj)));
                    var.getLoadArrays().forEach(stmt -> addPFGEdge(csManager.getArrayIndex(csobj),csManager.getCSVar(csvar.getContext(),stmt.getLValue())));

                    processCall(csvar,csobj);
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
        PointsToSet delta = PointsToSetFactory.make();
        pointsToSet.forEach(p ->{
            if(pointer.getPointsToSet().addObject(p)) delta.addObject(p);
        });
        if(!delta.isEmpty()){
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ->{
                workList.addEntry(succ,delta);
            });
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        for (Invoke invoke : recv.getVar().getInvokes()) {

            JMethod m = resolveCallee(recvObj,invoke);

            Context ct = contextSelector.selectContext(csManager.getCSCallSite(recv.getContext(),invoke), recvObj,m);

            workList.addEntry(csManager.getCSVar(ct,m.getIR().getThis()),PointsToSetFactory.make(recvObj));

            CallKind callkind = null;
            if(invoke.isInterface()) callkind = CallKind.INTERFACE;
            else if(invoke.isSpecial()) callkind = CallKind.SPECIAL;
            else if(invoke.isVirtual()) callkind = CallKind.VIRTUAL;
            else callkind = CallKind.OTHER;

            Edge<CSCallSite,CSMethod> edge = new Edge<>(callkind,csManager.getCSCallSite(recv.getContext(),invoke),csManager.getCSMethod(ct,m));
            if(callGraph.addEdge(edge)){
                addReachable(csManager.getCSMethod(ct,m));
                for(int i=0;i<csManager.getCSMethod(ct,m).getMethod().getParamCount();i++){
                    addPFGEdge(csManager.getCSVar(recv.getContext(),invoke.getRValue().getArg(i)),csManager.getCSVar(ct,csManager.getCSMethod(ct,m).getMethod().getIR().getParam(i)));
                }
                if(invoke.getLValue()==null) continue;
                for(Var returnvar : csManager.getCSMethod(ct,m).getMethod().getIR().getReturnVars()){
                    addPFGEdge(csManager.getCSVar(ct,returnvar),csManager.getCSVar(recv.getContext(),invoke.getLValue()));
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}