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

package pascal.taie.analysis.pta.core.heap;

import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Optional;

/**
 * Represents of abstract objects in pointer analysis.
 *
 * @see HeapModel
 */
public interface Obj {

    /**
     * @return the type of the object.
     */
    Type getType();

    /**
     * @return the allocation of the object.
     */
    Object getAllocation();

    /**
     * @return the method containing the allocation site of this object.
     * For some special objects, e.g., string constants, which are not
     * allocated in any method, this API returns an empty Optional.
     */
    Optional<JMethod> getContainerMethod();

    /**
     * This method is useful for type sensitivity.
     *
     * @return the type containing the allocation site of this object.
     * For special objects, the return values of this method are also special.
     */
    Type getContainerType();
}
