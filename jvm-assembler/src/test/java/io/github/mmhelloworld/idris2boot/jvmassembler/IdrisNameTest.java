package io.github.mmhelloworld.idris2boot.jvmassembler;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

public class IdrisNameTest {
    @Test
    void getFunctionName() {
        assertThat(IdrisName.getIdrisFunctionName("Data/List", "Data/List.idr", "take"))
            .isEqualTo("Data/List,take");
        assertThat(IdrisName.getIdrisFunctionName("Prelude/Strings", "Prelude.idr", "++"))
            .isEqualTo("Prelude,Strings$++");
        assertThat(IdrisName.getIdrisFunctionName("Main", "../src/./../foo/Test.idr", "bar"))
            .isEqualTo("foo/Test,Main$bar");
        assertThat(IdrisName.getIdrisFunctionName("Foo", "../src/./../main/Main/Foo.idr", "bar"))
            .isEqualTo("Foo,bar");
        assertThat(IdrisName.getIdrisFunctionName("Main/Foo", "../src/./../main/Main/Foo.idr", "bar"))
            .isEqualTo("Main/Foo,bar");
        assertThat(IdrisName.getIdrisFunctionName("Main/Foo", "../src/./../main/Main.idr", "bar"))
            .isEqualTo("Main,Foo$bar");
        assertThat(IdrisName.getIdrisFunctionName("Main/Foo/Bar/Baz", "../src/./../main/Main/Foo.idr", "bar"))
            .isEqualTo("Main/Foo,Bar$Baz$bar");
        assertThat(IdrisName.getIdrisFunctionName("Prelude", "Prelude.idr", "_n_(6546, 7008)_getAt"))
            .isEqualTo("Prelude,_n_(6546$cma$spc7008)_getAt");
    }

    @Test
    void getConstructorClassName() {
        assertThat(IdrisName.getIdrisConstructorClassName("Data/List", "Data/List.idr", "Take"))
            .isEqualTo("Data/List$Take");
        assertThat(IdrisName.getIdrisConstructorClassName("Prelude/Strings", "Prelude.idr", "->"))
            .isEqualTo("Prelude$Strings$-$gt");
        assertThat(IdrisName.getIdrisConstructorClassName("Main", "../src/./../foo/Test.idr", "Bar"))
            .isEqualTo("foo/Test$Main$Bar");
        assertThat(IdrisName.getIdrisConstructorClassName("Foo", "../src/./../main/Main/Foo.idr", "Bar"))
            .isEqualTo("Foo$Bar");
        assertThat(IdrisName.getIdrisConstructorClassName("Main/Foo", "../src/./../main/Main/Foo.idr", "Bar"))
            .isEqualTo("Main/Foo$Bar");
        assertThat(IdrisName.getIdrisConstructorClassName("Main/Foo", "../src/./../main/Main.idr", "Bar"))
            .isEqualTo("Main$Foo$Bar");
        assertThat(IdrisName.getIdrisConstructorClassName("Main/Foo/Bar/Baz", "../src/./../main/Main/Foo.idr", "Bar"))
            .isEqualTo("Main/Foo$Bar$Baz$Bar");
    }
}
