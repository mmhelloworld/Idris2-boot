package io.github.mmhelloworld.idris2.jvmassembler;

import io.github.mmhelloworld.idris2.jvmassembler.model.Aload;
import io.github.mmhelloworld.idris2.jvmassembler.model.Bytecode;
import io.github.mmhelloworld.idris2.jvmassembler.model.CreateMethod;
import io.github.mmhelloworld.idris2.jvmassembler.model.Iload;
import io.vavr.collection.Stream;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;

import static io.vavr.API.$;
import static io.vavr.API.Case;
import static io.vavr.API.Match;
import static io.vavr.Predicates.instanceOf;
import static java.lang.String.format;
import static org.objectweb.asm.ClassWriter.COMPUTE_MAXS;
import static org.objectweb.asm.Opcodes.ACC_PUBLIC;
import static org.objectweb.asm.Opcodes.ACC_STATIC;
import static org.objectweb.asm.Opcodes.ACC_SUPER;
import static org.objectweb.asm.Opcodes.V1_8;

public class Assembler {

    private Deque<Collection<Bytecode>> methodInstructions;
    private Collection<Bytecode> blockInstructions;
    private Map<String, ClassWriter> classWriters = new HashMap<>();
    private CreateMethod method;

    public void aload(int index) {
        blockInstructions.add(new Aload(index));
    }

    public void startMethodCode(String className,
                                String methodName,
                                Collection<String> argumentTypes,
                                String returnType) {
        blockInstructions = new ArrayList<>();
        methodInstructions = new ArrayDeque<>();
        methodInstructions.addFirst(blockInstructions);
        method = new CreateMethod(className, methodName, ACC_PUBLIC + ACC_STATIC, argumentTypes, returnType);
    }

    public void endMethodCode() {
        generateMethod();
    }

    private void generateMethod() {
        ClassWriter classWriter = classWriters.computeIfAbsent(method.getClassName(), this::createClassWriter);
        String methodDescriptor = getMethodDescriptor(method.getArgumentTypes(), method.getReturnType());
        MethodVisitor methodVisitor = classWriter.visitMethod(method.getAccess(), method.getName(), methodDescriptor,
            null, null);
        CodeGenerator codeGenerator = new CodeGenerator(methodVisitor);
        blockInstructions.forEach(instruction -> generateInstruction(instruction, codeGenerator));
    }

    private void generateInstruction(Bytecode bytecode, CodeGenerator codeGenerator) {
        Match(bytecode).of(
            Case($(instanceOf(Aload.class)), codeGenerator::generate),
            Case($(instanceOf(Iload.class)), codeGenerator::generate),
            Case($(), instruction -> { throw new RuntimeException("Invalid bytecode: " + instruction); })
        );
    }

    private String getMethodDescriptor(Collection<String> argumentTypes, String returnType) {
        String argumentsDesc = Stream.ofAll(argumentTypes)
            .mkString();
        return format("(%s)%s", argumentsDesc, returnType);
    }

    private ClassWriter createClassWriter(String className) {
        ClassWriter classWriter = new ClassWriter(COMPUTE_MAXS);
        classWriter.visit(V1_8, ACC_PUBLIC + ACC_SUPER, className, null, "java/lang/Object", null);
        return classWriter;
    }
}
