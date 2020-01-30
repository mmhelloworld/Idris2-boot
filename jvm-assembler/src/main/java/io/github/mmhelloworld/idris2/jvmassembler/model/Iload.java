package io.github.mmhelloworld.idris2.jvmassembler.model;

public class Iload implements Bytecode {
    private final int index;

    public Iload(int index) {
        this.index = index;
    }

    public int getIndex() {
        return index;
    }
}
