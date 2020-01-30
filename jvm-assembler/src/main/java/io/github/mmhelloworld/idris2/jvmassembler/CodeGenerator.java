package io.github.mmhelloworld.idris2.jvmassembler;

import io.github.mmhelloworld.idris2.jvmassembler.model.Aload;
import io.github.mmhelloworld.idris2.jvmassembler.model.Iload;
import org.objectweb.asm.MethodVisitor;

import static org.objectweb.asm.Opcodes.ALOAD;
import static org.objectweb.asm.Opcodes.ILOAD;

public class CodeGenerator {

    private final MethodVisitor methodVisitor;

    public CodeGenerator(MethodVisitor methodVisitor) {
        this.methodVisitor = methodVisitor;
    }

    public CodeGenerator generate(Iload iload) {
        methodVisitor.visitVarInsn(ILOAD, iload.getIndex());
        return this;
    }

    public CodeGenerator generate(Aload aload) {
        methodVisitor.visitVarInsn(ALOAD, aload.getIndex());
        return this;
    }

}
