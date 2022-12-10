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

import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.language.classes.JField;
import pascal.taie.util.Hashes;

/**
 * Represents instance field pointers in PFG.
 */
class InstanceField extends Pointer {

    private final Obj base;

    private final JField field;

    InstanceField(Obj base, JField field) {
        this.base = base;
        this.field = field;
    }

    /**
     * @return the base object.
     */
    Obj getBase() {
        return base;
    }

    /**
     * @return the corresponding instance field of the InstanceField pointer.
     */
    JField getField() {
        return field;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        InstanceField fieldPtr = (InstanceField) o;
        return base.equals(fieldPtr.base) && field.equals(fieldPtr.field);
    }

    @Override
    public int hashCode() {
        return Hashes.hash(base, field);
    }

    @Override
    public String toString() {
        return base + "." + field.getName();
    }
}
