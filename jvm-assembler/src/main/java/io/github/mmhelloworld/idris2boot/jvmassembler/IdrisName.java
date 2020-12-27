package io.github.mmhelloworld.idris2boot.jvmassembler;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.AbstractMap.SimpleImmutableEntry;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static java.util.stream.Collectors.toCollection;

public final class IdrisName {

    public static final String CLASS_NAME_FUNCTION_NAME_SEPARATOR = ",";
    public static final String CLASS_NAME_INNER_CLASS_NAME_SEPARATOR = "$";
    private static final Map<Character, String> replacements = new HashMap<>();

    static {
        replacements.put(' ', "$spc");
        replacements.put('.', "$dot");
        replacements.put(';', "$scol");
        replacements.put('[', "$lsq");
        replacements.put('/', "$div");
        replacements.put('<', "$lt");
        replacements.put('>', "$gt");
        replacements.put(':', "$col");
        replacements.put(',', "$cma");
    }

    private IdrisName() {
    }

    public static String getIdrisFunctionName(String idrisNamespace, String fileName, String idrisFunctionName) {
        return getIdrisName(idrisNamespace, fileName, idrisFunctionName, CLASS_NAME_FUNCTION_NAME_SEPARATOR);
    }

    public static String getIdrisConstructorClassName(String idrisNamespace, String fileName,
                                                      String idrisFunctionName) {
        return getIdrisName(idrisNamespace, fileName, idrisFunctionName, CLASS_NAME_INNER_CLASS_NAME_SEPARATOR);
    }

    private static String getIdrisName(String idrisNamespace, String fileName, String memberName, String separator) {
        Entry<String, String> classAndMemberName = getClassAndMemberName(idrisNamespace, fileName, memberName);
        return join(classAndMemberName.getKey(), classAndMemberName.getValue(), separator);
    }

    private static String join(String value1, String value2, String separator) {
        return value1 + separator + value2;
    }

    private static Entry<String, String> getClassAndMemberName(String idrisNamespace, String fileName,
                                                               String memberName) {
        LinkedList<String> moduleParts = Stream.of(idrisNamespace.split("/")).collect(toCollection(LinkedList::new));
        LinkedList<String> fileParts = getIdrisModuleNameFromFileName(fileName).collect(toCollection(LinkedList::new));
        Entry<LinkedList<String>, LinkedList<String>> nameParts = lcs(new LinkedList<>(), moduleParts, fileParts);
        String className = String.join("/", nameParts.getKey().isEmpty() ? fileParts : nameParts.getKey());
        String jvmMemberName = String.join("$", add(nameParts.getValue(), memberName))
            .chars()
            .flatMap(c -> replacements.getOrDefault((char) c, String.valueOf((char) c)).chars())
            .collect(StringBuilder::new, StringBuilder::appendCodePoint, StringBuilder::append)
            .toString();
        return new SimpleImmutableEntry<>(className, jvmMemberName);
    }

    private static Entry<LinkedList<String>, LinkedList<String>> lcs(LinkedList<String> acc,
                                                                     LinkedList<String> xs,
                                                                     LinkedList<String> ys) {
        if (xs.isEmpty() || ys.isEmpty()) {
            return xs.isEmpty() ? new SimpleImmutableEntry<>(acc, ys) : new SimpleImmutableEntry<>(acc, xs);
        } else {
            String x = xs.getFirst();
            if (x.equals(ys.getFirst())) {
                return lcs(add(acc, x), tail(xs), tail(ys));
            } else {
                Entry<LinkedList<String>, LinkedList<String>> lcs1 = lcs(new LinkedList<>(), tail(xs), ys);
                Entry<LinkedList<String>, LinkedList<String>> lcs2 = lcs(new LinkedList<>(), xs, tail(ys));
                return lcs1.getKey().size() > lcs2.getKey().size() ? lcs1 : lcs2;
            }
        }
    }

    private static <T> LinkedList<T> add(LinkedList<T> items, T item) {
        items.add(item);
        return items;
    }

    private static <T> LinkedList<T> tail(LinkedList<T> items) {
        return new LinkedList<>(items.subList(1, items.size()));
    }

    private static Stream<String> getIdrisModuleNameFromFileName(String fileName) {
        Path path = Paths.get(fileName.replaceAll("^\\.+|\\.idr$", ""));
        Path module = path.normalize();
        return IntStream.range(0, module.getNameCount())
            .mapToObj(module::getName)
            .map(Path::toString);
    }

}
