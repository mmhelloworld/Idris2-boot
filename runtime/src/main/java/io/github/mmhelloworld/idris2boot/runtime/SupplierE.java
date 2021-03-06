package io.github.mmhelloworld.idris2boot.runtime;

@FunctionalInterface
public interface SupplierE<T, E extends Exception> {
    T get() throws E;
}
