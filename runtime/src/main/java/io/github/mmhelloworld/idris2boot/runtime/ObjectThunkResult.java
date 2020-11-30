package io.github.mmhelloworld.idris2boot.runtime;

public final class ObjectThunkResult implements Thunk {
    public final Object result;

    public ObjectThunkResult(Object result) {
        this.result = result;
    }

    @Override
    public Thunk evaluate() {
        return this;
    }

    @Override
    public boolean isRedex() {
        return false;
    }

    @Override
    public Object getObject() {
        return result;
    }

    @Override
    public int getInt() {
        return (int) result;
    }

    @Override
    public double getDouble() {
        return (double) result;
    }
}

