package io.github.mmhelloworld.idris2boot.runtime;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import static java.nio.charset.StandardCharsets.UTF_8;

public final class Console {
    private static BufferedReader stdin = new BufferedReader(new InputStreamReader(System.in, UTF_8));

    private static boolean isStdinEof = false;

    private Console() {
    }

    public static void printString(String string) {
        System.out.print(string);
        System.out.flush();
    }

    public static String getString() throws IOException {
        String line = stdin.readLine();
        isStdinEof = line == null;
        return isStdinEof ? "" : line;
    }
}
