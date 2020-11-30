package io.github.mmhelloworld.idris2boot.runtime;

public interface IdrisObject {
    int getConstructorId();
    Object getProperty(int index);
}
