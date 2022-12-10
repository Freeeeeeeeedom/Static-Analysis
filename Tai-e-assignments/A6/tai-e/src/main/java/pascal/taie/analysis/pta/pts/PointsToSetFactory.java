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

package pascal.taie.analysis.pta.pts;

import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.util.collection.Sets;

import java.util.Set;
import java.util.function.Supplier;

/**
 * Provides static factory methods for {@link PointsToSet}.
 */
public class PointsToSetFactory {

    private static final Supplier<Set<CSObj>> setFactory = Sets::newHybridSet;

    public static PointsToSet make() {
        return new DelegatePointsToSet(setFactory.get());
    }

    /**
     * Convenient method for making one-element points-to set.
     */
    public static PointsToSet make(CSObj obj) {
        PointsToSet set = make();
        set.addObject(obj);
        return set;
    }
}
