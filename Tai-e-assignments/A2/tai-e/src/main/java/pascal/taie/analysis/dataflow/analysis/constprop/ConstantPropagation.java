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

package pascal.taie.analysis.dataflow.analysis.constprop;

import fj.data.vector.V2;
import jas.CP;
import org.checkerframework.checker.units.qual.A;
import org.checkerframework.checker.units.qual.C;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Stream;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        //需要将每个block初始化为NAC
        CPFact fact = new CPFact();
        cfg.getIR().getParams().forEach(var -> {
            if(canHoldInt(var)) {
                //判断是否在本次的分析范围内
                fact.update(var, Value.getNAC());
            }
        });
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((var, value) -> {
            target.update(var,meetValue(value,target.get(var)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC() || v2.isNAC()) return Value.getNAC();

        if(v1.isConstant() && v2.isConstant()){
            if(v1.getConstant()==v2.getConstant()) return Value.makeConstant(v1.getConstant());
            else return Value.getNAC();
        }
        if(v1.isUndef()){
            if(v2.isConstant()) return Value.makeConstant(v2.getConstant());
            else return Value.getUndef();
        };
        if(v2.isUndef()){
            if(v1.isConstant()) return Value.makeConstant(v1.getConstant());
            else return Value.getUndef();
        }
        return Value.getUndef();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact Copy = out.copy();

        for (Var key : in.keySet()) {
            out.update(key, in.get(key));
        }
        DefinitionStmt<?,?> ds;
        if(stmt instanceof DefinitionStmt<?,?>){
            ds = (DefinitionStmt<?, ?>) stmt;
        }
        else return !out.equals(Copy);
        //非赋值语句

        LValue L = ds.getLValue();
        RValue R = ds.getRValue();

        Value v = evaluate(R,in);
        if (L != null)
            if (L instanceof Var && canHoldInt((Var) L)) {
                out.update((Var) L, v);
            }
        return !out.equals(Copy);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if(exp instanceof Var){
            return in.get((Var)exp);
        }
        else if(exp instanceof IntLiteral){
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        else if(exp instanceof BinaryExp){
            Value op1,op2;
            op1 = in.get(((BinaryExp) exp).getOperand1());
            op2 = in.get(((BinaryExp) exp).getOperand2());

            BinaryExp.Op op = ((BinaryExp) exp).getOperator();

            Value ans = Value.getUndef();
            if(op.toString().equals("/") || op.toString().equals("%")){
                if(op2.isConstant() && op2.getConstant() == 0) return Value.getUndef();
            }
            if(op1.isNAC() || op2.isNAC()) return Value.getNAC();
            //处理NAC的情况
            if(op1.isConstant() && op2.isConstant()){
                if(exp instanceof ArithmeticExp){
                    ans = Arith_compute(op1,op2,op.toString());
                }
                else if(exp instanceof ConditionExp){
                    ans = Condi_compute(op1,op2,op.toString());
                }
                else if(exp instanceof ShiftExp){
                    ans = Shift_compute(op1,op2,op.toString());
                }
                else if(exp instanceof BitwiseExp){
                    ans = Bitwise_compute(op1,op2,op.toString());
                }
                return ans;
            }
            return Value.getUndef();
        }
        return Value.getNAC();
    }
    public static Value Arith_compute(Value op1,Value op2,String op){
            int v1 = op1.getConstant(), v2 = op2.getConstant(), ans = 0;
            switch (op) {
                case "+" -> ans = v1 + v2;
                case "-" -> ans = v1 - v2;
                case "*" -> ans = v1 * v2;
                case "/" -> ans = v1 / v2;
                case "%" -> ans = v1 % v2;
            }
            return Value.makeConstant(ans);
    }
    public static Value Condi_compute(Value op1,Value op2,String op){
            int v1 = op1.getConstant(), v2 = op2.getConstant(), ans = 0;
            switch (op) {
                case "==":
                    if (v1 == v2) ans = 1;
                    break;
                case "!=":
                    if (v1 != v2) ans = 1;
                    break;
                case ">":
                    if (v1 > v2) ans = 1;
                    break;
                case "<":
                    if (v1 < v2) ans = 1;
                    break;
                case ">=":
                    if (v1 >= v2) ans = 1;
                    break;
                case "<=":
                    if (v1 <= v2) ans = 1;
                    break;
            }
            return Value.makeConstant(ans);
    }
    public static Value Shift_compute(Value op1,Value op2,String op){
            int v1 = op1.getConstant(), v2 = op2.getConstant(), ans = 0;
            if(op.equals("<<"))  ans = v1 << v2;
            if(op.equals(">>"))  ans = v1 >> v2;
            if(op.equals(">>>")) ans = v1 >>> v2;
            return Value.makeConstant(ans);
    }
    public static Value Bitwise_compute(Value op1,Value op2,String op){
            int v1 = op1.getConstant(), v2 = op2.getConstant(), ans = 0;
            if(op.equals("|")) ans = v1 | v2;
            if(op.equals("&")) ans = v1 & v2;
            if(op.equals("^")) ans = v1 ^ v2;
            return Value.makeConstant(ans);
    }
}
