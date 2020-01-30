package io.github.mmhelloworld.idris2.jvmassembler.model;

import java.util.Collection;

public class CreateMethod implements Bytecode {
    private final String className;
    private final String name;
    private final int access;
    private final Collection<String> argumentTypes;
    private final String returnType;

    public CreateMethod(String className, String name, int access, Collection<String> argumentTypes, String returnType) {
        this.className = className;
        this.name = name;
        this.access = access;
        this.argumentTypes = argumentTypes;
        this.returnType = returnType;
    }

    public String getClassName() {
        return className;
    }

    public String getName() {
        return name;
    }

    public Collection<String> getArgumentTypes() {
        return argumentTypes;
    }

    public String getReturnType() {
        return returnType;
    }

    public int getAccess() {
        return access;
    }
}
