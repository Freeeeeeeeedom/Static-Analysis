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

package pascal.taie.analysis.pta;

import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.Collection;
import java.util.Set;

public interface PointerAnalysisResult {

    /**
     * @return all reachable variables in the program.
     */
    Collection<Var> getVars();

    /**
     * @return all reachable objects in the program.
     */
    Collection<Obj> getObjects();

    /**
     * @return set of Obj pointed to by var.
     */
    Set<Obj> getPointsToSet(Var var);

    /**
     * @return set of Obj pointed to by base.field.
     */
    Set<Obj> getPointsToSet(Var base, JField field);

    /**
     * @return points-to set of given field. The field is supposed to be static.
     */
    Set<Obj> getPointsToSet(JField field);

    /**
     * @return the resulting call graph (without contexts).
     */
    CallGraph<Invoke, JMethod> getCallGraph();
}
