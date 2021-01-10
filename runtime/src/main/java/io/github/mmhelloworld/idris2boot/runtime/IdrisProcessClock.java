package io.github.mmhelloworld.idris2boot.runtime;

import java.math.BigInteger;

import static java.util.concurrent.TimeUnit.NANOSECONDS;
import static java.util.concurrent.TimeUnit.SECONDS;

public final class IdrisProcessClock implements IdrisClock {
    private final long time;

    public IdrisProcessClock() {
        this.time = System.nanoTime();
    }

    @Override
    public BigInteger getSeconds() {
        return BigInteger.valueOf(SECONDS.convert(time - Runtime.START_TIME, NANOSECONDS));
    }

    @Override
    public BigInteger getNanoSeconds() {
        return BigInteger.valueOf((time - Runtime.START_TIME) % 1000000000L);
    }
}
