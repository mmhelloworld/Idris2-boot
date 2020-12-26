package io.github.mmhelloworld.idris2boot.runtime;

@FunctionalInterface
public interface BooleanSupplierE<E extends Exception> {
    boolean get() throws E;
}
