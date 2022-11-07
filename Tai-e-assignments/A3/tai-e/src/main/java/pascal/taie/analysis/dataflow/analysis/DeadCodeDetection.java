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

package pascal.taie.analysis.dataflow.analysis;

import org.checkerframework.checker.units.qual.C;
import pascal.taie.Assignment;
import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        HashMap<Stmt, Boolean> map = new HashMap<Stmt, Boolean>();
        Stmt start = cfg.getEntry();

        //control-flow-unreachable and branch-unreachable
        for(Stmt stmt : cfg) map.put(stmt,false);
        Set<Stmt> unreachable = new HashSet<>(cfg.getNodes());

        DFScfg(unreachable,cfg,constants,start,map);
        deadCode.addAll(unreachable);

        //dead assignment
        Set<Stmt> deads = deadAssignment(liveVars,cfg);
        deadCode.addAll(deads);

        // Your task is to recognize dead code in ir and add it to deadCode
        deadCode.remove(cfg.getExit());
        deadCode.remove(cfg.getEntry());
        return deadCode;
    }

    public void DFScfg(Set<Stmt> unreachable, CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants,Stmt cur,HashMap<Stmt, Boolean> map){
        if(map.get(cur)) return;
        map.put(cur,true);
        unreachable.remove(cur);

        Set<Stmt> succ = new HashSet<>();
        if(cur instanceof If){
            Value condition = ConstantPropagation.evaluate(((If) cur).getCondition(),constants.getInFact(cur));
            if(!condition.isConstant()) succ.addAll(cfg.getSuccsOf(cur));
            else{
                Set<Edge<Stmt>> edges = cfg.getOutEdgesOf(cur);
                for(Edge<Stmt> e : edges){
                    if(e.getKind() == Edge.Kind.IF_TRUE && condition.getConstant()==1) succ.add(e.getTarget());
                    if(e.getKind() == Edge.Kind.IF_FALSE && condition.getConstant()==0) succ.add(e.getTarget());
                }
            }
        }
        else if(cur instanceof SwitchStmt){
            List<Integer> values = ((SwitchStmt) cur).getCaseValues();
            Value val = ConstantPropagation.evaluate(((SwitchStmt) cur).getVar(),constants.getInFact(cur));
            if(!val.isConstant()) succ.addAll(cfg.getSuccsOf(cur));
            else if(val.isConstant() && !values.contains(val.getConstant())) succ.add(((SwitchStmt) cur).getDefaultTarget());
            else {
                Set<Edge<Stmt>> edges = cfg.getOutEdgesOf(cur);
                for(Edge<Stmt> e : edges){
                    if(e.getKind() == Edge.Kind.SWITCH_CASE)if(val.getConstant() == e.getCaseValue()) succ.add(e.getTarget());
                }
            }
        }
        else{
            cfg.getOutEdgesOf(cur).forEach(e->{
                succ.add(e.getTarget());
            });
        }
        for(Stmt stmt : succ) DFScfg(unreachable,cfg,constants,stmt,map);
    }

    public Set<Stmt> deadAssignment (DataflowResult<Stmt, SetFact<Var>> liveVars,CFG<Stmt> cfg){
        Set<Stmt> deads = new HashSet<>();
        for(Stmt stmt : cfg){
            if(stmt instanceof AssignStmt<?,?>){
            SetFact<Var> vars = liveVars.getOutFact(stmt);
            stmt.getDef().ifPresent(l -> {
                if(l instanceof Var)if(!vars.contains((Var) l) && hasNoSideEffect(((AssignStmt<?, ?>) stmt).getRValue())) deads.add(stmt);
            });
            }
        }
        return deads;
    }
    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
