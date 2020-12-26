package io.github.mmhelloworld.idris2boot.runtime;

@FunctionalInterface
public interface IntSupplierE<E extends Exception> {
    int get() throws E;
}
