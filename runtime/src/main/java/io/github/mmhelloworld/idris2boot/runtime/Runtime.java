package io.github.mmhelloworld.idris2boot.runtime;

import java.nio.channels.Channels;
import java.util.List;
import java.util.stream.Stream;

import static java.util.stream.Collectors.toList;

public final class Runtime {
    private static final ChannelIo stdin = new ChannelIo(null, Channels.newChannel(System.in));
    private static final ChannelIo stdout = new ChannelIo(null, Channels.newChannel(System.out));
    private static final ChannelIo stderr = new ChannelIo(null, Channels.newChannel(System.err));
    private static final ThreadLocal<Integer> ERROR_NUMBER = ThreadLocal.withInitial(() -> 0);
    private static List<String> programArgs;

    private Runtime() {
    }

    public static List<String> getProgramArgs() {
        return programArgs;
    }

    public static void setProgramArgs(String[] args) {
        // "java" as the executable name for the first argument to conform to Idris' getArgs function
        programArgs = Stream.concat(Stream.of("java"), Stream.of(args))
            .collect(toList());
    }

    public static ChannelIo getStdin() {
        return stdin;
    }

    public static ChannelIo getStdout() {
        return stdout;
    }

    public static ChannelIo getStderr() {
        return stderr;
    }

    public static <T> T crash(String message) {
        throw new RuntimeException(message);
    }

    public static int getErrorNumber() {
        return ERROR_NUMBER.get();
    }

    static void setErrorNumber(int errorNumber) {
        ERROR_NUMBER.set(errorNumber);
    }

    public static IntThunk createThunk(int value) {
        return new IntThunkResult(value);
    }

    public static IntThunk unboxToIntThunk(Thunk value) {
        return () -> value;
    }

    public static DoubleThunk unboxToDoubleThunk(Thunk value) {
        return () -> value;
    }

    public static DoubleThunk createThunk(double value) {
        return new DoubleThunkResult(value);
    }

    public static Thunk createThunk(Object value) {
        return value instanceof Thunk ? (Thunk) value : new ObjectThunkResult(value);
    }

    public static Object unwrap(Object possibleThunk) {
        if (possibleThunk instanceof Thunk) {
            return ((Thunk) possibleThunk).getObject();
        } else {
            return possibleThunk;
        }
    }

    public static Object force(Object delayed) {
        return unwrap(((Delayed) unwrap(delayed)).evaluate());
    }

    public static int unwrapIntThunk(Object possibleThunk) {
        if (possibleThunk instanceof Thunk) {
            return ((Thunk) possibleThunk).getInt();
        } else {
            return (int) possibleThunk;
        }
    }

    public static double unwrapDoubleThunk(Object possibleThunk) {
        if (possibleThunk instanceof Thunk) {
            return ((Thunk) possibleThunk).getDouble();
        } else {
            return (double) possibleThunk;
        }
    }
}
