package io.github.mmhelloworld.idris2boot.runtime;

import java.math.BigInteger;

public interface IdrisClock {
    BigInteger getSeconds();
    BigInteger getNanoSeconds();
}
