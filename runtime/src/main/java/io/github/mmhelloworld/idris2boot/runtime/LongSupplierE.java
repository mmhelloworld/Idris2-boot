package io.github.mmhelloworld.idris2boot.runtime;

@FunctionalInterface
public interface LongSupplierE<E extends Exception> {
    long get() throws E;
}
