package io.github.mmhelloworld.idris2boot.runtime;

import java.math.BigInteger;
import java.time.Clock;
import java.time.Instant;

public final class IdrisUtcClock implements IdrisClock {
    private final Instant instant;

    public IdrisUtcClock() {
        instant = Clock.systemUTC().instant();
    }

    @Override
    public BigInteger getSeconds() {
        return BigInteger.valueOf(instant.getEpochSecond());
    }

    @Override
    public BigInteger getNanoSeconds() {
        return BigInteger.valueOf(instant.getNano() % 1000000000L);
    }
}
