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

package pascal.taie.ir.stmt;

import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.Var;

/**
 * Representation of following load field statements:
 * <ul>
 *     <li>load instance field: x = o.f
 *     <li>load static field: x = T.f
 * </ul>
 */
public class LoadField extends FieldStmt<Var, FieldAccess> {

    public LoadField(Var lvalue, FieldAccess rvalue) {
        super(lvalue, rvalue);
        if (rvalue instanceof InstanceFieldAccess) {
            Var base = ((InstanceFieldAccess) rvalue).getBase();
            base.addLoadField(this);
        }
    }

    @Override
    public FieldAccess getFieldAccess() {
        return getRValue();
    }

    @Override
    public <T> T accept(StmtVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
