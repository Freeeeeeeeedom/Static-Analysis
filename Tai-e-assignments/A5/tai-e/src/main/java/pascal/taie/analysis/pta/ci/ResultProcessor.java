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

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.Streams;
import pascal.taie.util.collection.Views;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.function.ToIntFunction;

import static pascal.taie.util.collection.CollectionUtils.sum;

class ResultProcessor {

    private static final Logger logger = LogManager.getLogger(ResultProcessor.class);

    private static final String HEADER = "Points-to sets of all ";

    /**
     * Separator between pointer and its points-to set.
     */
    private static final String SEP = " -> ";

    private static final DecimalFormat formatter = new DecimalFormat("#,###");

    private final AnalysisOptions options;

    public ResultProcessor(AnalysisOptions options) {
        this.options = options;
    }

    void process(CIPTAResult result) {
        logStatistics(result);
        String action = options.getString("action");
        if (action == null) {
            return;
        }
        String file = options.getString("file");
        switch (action) {
            case "dump" -> dumpPointsToSet(result, file);
            case "compare" -> comparePointsToSet(result, file);
        }
    }

    private static void logStatistics(CIPTAResult result) {
        int vars = result.getVars().size();
        ToIntFunction<Pointer> getSize = p -> p.getPointsToSet().size();
        int vptSize = sum(getPointers(result, VarPtr.class), getSize);
        int sfptSize = sum(getPointers(result, StaticField.class), getSize);
        int ifptSize = sum(getPointers(result, InstanceField.class), getSize);
        int aptSize = sum(getPointers(result, ArrayIndex.class), getSize);
        int reachable = result.getCallGraph().getNumberOfMethods();
        int callEdges = result.getCallGraph().getNumberOfEdges();
        logger.info("-------------- Pointer analysis statistics: --------------");
        logger.info(String.format("%-30s%s", "#var pointers:", format(vars)));
        logger.info(String.format("%-30s%s", "#var points-to:", format(vptSize)));
        logger.info(String.format("%-30s%s", "#static field points-to:", format(sfptSize)));
        logger.info(String.format("%-30s%s", "#instance field points-to:", format(ifptSize)));
        logger.info(String.format("%-30s%s", "#array indexes points-to:", format(aptSize)));
        logger.info(String.format("%-30s%s", "#reachable methods:", format(reachable)));
        logger.info(String.format("%-30s%s", "#call graph edges:", format(callEdges)));
        logger.info("----------------------------------------");
    }

    private static String format(int i) {
        return formatter.format(i);
    }

    private static void dumpPointsToSet(CIPTAResult result, String output) {
        PrintStream out;
        if (output != null) {  // if output file is given, then dump to the file
            File outFile = new File(output);
            try {
                out = new PrintStream(new FileOutputStream(outFile));
                logger.info("Dumping points-to set to {} ...", outFile);
            } catch (FileNotFoundException e) {
                throw new RuntimeException("Failed to open output file", e);
            }
        } else {  // otherwise, dump to System.out
            out = System.out;
        }
        dumpPointers(out, getPointers(result, VarPtr.class), "variables");
        dumpPointers(out, getPointers(result, StaticField.class), "static fields");
        dumpPointers(out, getPointers(result, InstanceField.class), "instance fields");
        dumpPointers(out, getPointers(result, ArrayIndex.class), "array indexes");
        if (out != System.out) {
            out.close();
        }
    }

    private static Collection<Pointer> getPointers(
            CIPTAResult result, Class<? extends Pointer> klass) {
        return Views.toFilteredCollection(
                result.getPointerFlowGraph().getPointers(),
                klass::isInstance);
    }

    private static void dumpPointers(
            PrintStream out, Collection<? extends Pointer> pointers, String desc) {
        out.println(HEADER + desc);
        pointers.stream()
                .sorted(Comparator.comparing(Pointer::toString))
                .forEach(p -> out.println(p + SEP + toString(p.getPointsToSet())));
        out.println();
    }

    private static String toString(PointsToSet pts) {
        return Streams.toString(pts.objects());
    }

    private void comparePointsToSet(CIPTAResult result, String input) {
        logger.info("Comparing points-to set with {} ...", input);
        var inputs = readPointsToSets(input);
        Map<String, Pointer> pointers = new LinkedHashMap<>();
        addPointers(pointers, getPointers(result, VarPtr.class));
        addPointers(pointers, getPointers(result, StaticField.class));
        addPointers(pointers, getPointers(result, InstanceField.class));
        addPointers(pointers, getPointers(result, ArrayIndex.class));
        List<String> mismatches = new ArrayList<>();
        pointers.forEach((pointerStr, pointer) -> {
            String given = toString(pointer.getPointsToSet());
            String expected = inputs.get(pointerStr);
            if (!given.equals(expected)) {
                mismatches.add(String.format("%s, expected: %s, given: %s",
                        pointerStr, expected, given));
            }
        });
        inputs.keySet()
                .stream()
                .filter(Predicate.not(pointers::containsKey))
                .forEach(pointerStr -> {
                    String expected = inputs.get(pointerStr);
                    mismatches.add(String.format("%s, expected: %s, given: null",
                            pointerStr, expected));
                });
        if (!mismatches.isEmpty()) {
            throw new AnalysisException("Mismatches of points-to set\n" +
                    String.join("\n", mismatches));
        }
    }

    private static Map<String, String> readPointsToSets(String input) {
        try {
            Map<String, String> result = new LinkedHashMap<>();
            Files.lines(Path.of(input))
                    .filter(line -> line.contains(SEP))
                    .map(line -> line.split(SEP))
                    .forEach(s -> result.put(s[0], s[1]));
            return result;
        } catch (IOException e) {
            throw new AnalysisException(
                    "Failed to read points-to set from " + input, e);
        }
    }

    private static void addPointers(Map<String, Pointer> map,
                                    Collection<? extends Pointer> pointers) {
        pointers.stream()
                .sorted(Comparator.comparing(Pointer::toString))
                .forEach(p -> map.put(p.toString(), p));
    }
}
