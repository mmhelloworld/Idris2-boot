package io.github.mmhelloworld.idris2.jvmassembler.model;

public class Aload implements Bytecode {
    private final int index;

    public Aload(int index) {
        this.index = index;
    }

    public int getIndex() {
        return index;
    }
}
