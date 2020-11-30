package io.github.mmhelloworld.idris2boot.runtime;

public final class Strings {
    private Strings() {
    }

    public static String substring(int offset, int length, String str) {
        // Mimics Idris scheme backend
        int strLength = str.length();
        int start = Math.max(0, offset);
        int nonNegativeLength = Math.max(0, length);
        int end = Math.min(strLength, start + nonNegativeLength);
        return start > strLength ? "" : str.substring(start, end);
    }
}
