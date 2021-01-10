package io.github.mmhelloworld.idris2boot.runtime;

import java.math.BigInteger;

import static java.util.concurrent.TimeUnit.NANOSECONDS;
import static java.util.concurrent.TimeUnit.SECONDS;

public final class IdrisMonotonicClock implements IdrisClock {
    private final long time;

    public IdrisMonotonicClock() {
        this.time = System.nanoTime();
    }

    @Override
    public BigInteger getSeconds() {
        return BigInteger.valueOf(SECONDS.convert(time, NANOSECONDS));
    }

    @Override
    public BigInteger getNanoSeconds() {
        return BigInteger.valueOf(time % 1000000000L);
    }
}
