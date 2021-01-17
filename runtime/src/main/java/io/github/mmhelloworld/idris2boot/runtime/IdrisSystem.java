package io.github.mmhelloworld.idris2boot.runtime;

import java.io.File;
import java.io.IOException;
import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.concurrent.TimeUnit;
import java.util.stream.Stream;

import static java.lang.System.currentTimeMillis;

public final class IdrisSystem {
    private static final Map<String, String> environmentVariables;
    private static final List<String> environmentVariableNames;
    public static final String OS_NAME;

    static {
        environmentVariables = new LinkedHashMap<>(System.getenv());
        environmentVariables.putAll((Map) System.getProperties());
        environmentVariableNames = new ArrayList<>(environmentVariables.keySet());

        // To conform to support/chez/support.ss
        String osNameProperty = getOsNameProperty();
        if (osNameProperty.startsWith("windows")) {
            OS_NAME = "windows";
        } else if (osNameProperty.startsWith("mac")) {
            OS_NAME = "darwin";
        } else if (Stream.of("linux", "aix", "solaris", "sunos", "freebsd", "openbsd", "netbsd")
            .anyMatch(osNameProperty::startsWith)) {
            OS_NAME = "unix";
        } else {
            OS_NAME = "unknown";
        }
    }

    private static String getOsNameProperty() {
        try {
            return System.getProperty("os.name").toLowerCase(Locale.ROOT);
        } catch (SecurityException exception) {
            return "";
        }
    }

    private IdrisSystem() {
    }

    public static int time() {
        return (int) Duration.ofMillis(currentTimeMillis()).getSeconds();
    }

    public static int runCommand(String command) throws IOException, InterruptedException {
        String[] cmdarray = parseCommand(command).toArray(new String[0]);
        ProcessBuilder processBuilder = new ProcessBuilder(cmdarray)
            .inheritIO()
            .directory(new File(Directories.workingDir));
        return processBuilder.start().waitFor();
    }

    public static void usleep(int microseconds) throws InterruptedException {
        TimeUnit.MICROSECONDS.sleep(microseconds);
    }

    public static void sleep(int seconds) throws InterruptedException {
        TimeUnit.SECONDS.sleep(seconds);
    }

    public static String getEnv(String name) {
        return System.getProperty(name, System.getenv(name));
    }

    public static int clearEnv(String name) {
        System.clearProperty(name);
        return 0;
    }

    public static int setEnv(String name, String value, int shouldOverwrite) {
        System.setProperty(name, value);
        return 0;
    }

    public static String getEnvPair(int index) {
        if (index >= environmentVariableNames.size()) {
            return null;
        } else {
            String name = environmentVariableNames.get(index);
            return name + "=" + environmentVariables.get(name);
        }
    }

    public static void exit(int exitCode) {
        System.exit(exitCode);
    }

    public static String getOsName() {
        return OS_NAME;
    }

    // This may not be adequate but simple enough for basic cases
    private static List<String> parseCommand(final String command) {
        List<String> commandWithArgs = new ArrayList<>();
        int start = 0;
        boolean inQuotes = false;
        for (int current = 0; current < command.length(); current++) {
            if (isUnescapedDoubleQuotes(command, current)) {
                inQuotes = !inQuotes;
            }

            boolean atLastChar = current == command.length() - 1;
            if (atLastChar) {
                commandWithArgs.add(unescapeDoubleQuotes(trimDoubleQuotes(command.substring(start))));
            } else if (command.charAt(current) == ' ' && !inQuotes) {
                commandWithArgs.add(unescapeDoubleQuotes(trimDoubleQuotes(command.substring(start, current))));
                start = current + 1;
            }
        }
        return commandWithArgs;
    }

    private static boolean isUnescapedDoubleQuotes(final String str, final int index) {
        return str.charAt(index) == '"' && (index == 0 || str.charAt(index - 1) != '\\');
    }

    private static String unescapeDoubleQuotes(String str) {
        return str.replaceAll("\\\\\"", "\"");
    }

    private static String trimDoubleQuotes(String str) {
        if (str.startsWith("\"") && str.endsWith("\"")) {
            return str.substring(1, str.length() - 1);
        } else {
            return str;
        }
    }
}
