package io.github.mmhelloworld.idris2boot.jvmassembler;

import io.vavr.Tuple;
import io.vavr.Tuple2;
import io.vavr.collection.Stream;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

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
        return getClassAndMemberName(idrisNamespace, fileName, memberName)
            .apply((className, functionName) -> join(className, functionName, separator));
    }

    private static String join(String value1, String value2, String separator) {
        return value1 + separator + value2;
    }

    private static Tuple2<String, String> getClassAndMemberName(String idrisNamespace, String fileName,
                                                                String memberName) {
        Stream<String> moduleParts = Stream.of(idrisNamespace.split("/"));
        Stream<String> fileParts = getIdrisModuleNameFromFileName(fileName);
        Tuple2<Stream<String>, Stream<String>> nameParts = lcs(Stream.empty(), moduleParts, fileParts);
        String className = (nameParts._1.isEmpty() ? fileParts : nameParts._1).mkString("/");
        String jvmMemberName = nameParts._2
            .append(memberName)
            .mkString("$")
            .chars()
            .flatMap(c -> replacements.getOrDefault((char) c, String.valueOf((char) c)).chars())
            .collect(StringBuilder::new, StringBuilder::appendCodePoint, StringBuilder::append)
            .toString();
        return Tuple.of(className, jvmMemberName);
    }

    private static Tuple2<Stream<String>, Stream<String>> lcs(Stream<String> acc, Stream<String> xs,
                                                              Stream<String> ys) {
        if (xs.isEmpty() || ys.isEmpty()) {
            return xs.isEmpty() ? Tuple.of(acc, ys) : Tuple.of(acc, xs);
        } else {
            String x = xs.head();
            if (x.equals(ys.head())) {
                return lcs(acc.append(x), xs.tail(), ys.tail());
            } else {
                Tuple2<Stream<String>, Stream<String>> lcs1 = lcs(Stream.empty(), xs.tail(), ys);
                Tuple2<Stream<String>, Stream<String>> lcs2 = lcs(Stream.empty(), xs, ys.tail());
                return lcs1._1.size() > lcs2._1.size() ? lcs1 : lcs2;
            }
        }
    }

    private static Stream<String> getIdrisModuleNameFromFileName(String fileName) {
        Path path = Paths.get(fileName.replaceAll("^\\.+|\\.idr$", ""));
        Path module = path.normalize();
        return Stream.range(0, module.getNameCount())
            .map(module::getName)
            .map(Path::toString);
    }

}
