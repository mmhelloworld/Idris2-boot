package io.github.mmhelloworld.idris2boot.runtime;

@FunctionalInterface
public interface Thunk {
    Thunk evaluate();

    default boolean isRedex() {
        return true;
    }

    default Object getObject() {
        Thunk resultThunk = unwrap();
        return resultThunk == null ? null : resultThunk.getObject();
    }

    default int getInt() {
        return unwrap().getInt();
    }

    default double getDouble() {
        return unwrap().getDouble();
    }

    default Thunk unwrap() {
        Thunk thunk = this;
        while (thunk != null && thunk.isRedex()) {
            thunk = thunk.evaluate();
        }
        return thunk;
    }
}
