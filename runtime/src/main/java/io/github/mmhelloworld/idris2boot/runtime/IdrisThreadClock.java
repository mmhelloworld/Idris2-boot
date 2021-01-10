package io.github.mmhelloworld.idris2boot.runtime;

import java.math.BigInteger;

import static java.util.concurrent.TimeUnit.NANOSECONDS;
import static java.util.concurrent.TimeUnit.SECONDS;

public class IdrisThreadClock implements IdrisClock {
    private static final ThreadLocal<IdrisThreadClock> THREAD_INSTANCE =
        ThreadLocal.withInitial(() -> new IdrisThreadClock(System.nanoTime()));

    private final long time;

    private IdrisThreadClock(long time) {
        this.time = time;
    }

    public static IdrisThreadClock getInstance() {
        return THREAD_INSTANCE.get();
    }

    @Override
    public BigInteger getSeconds() {
        return BigInteger.valueOf(SECONDS.convert(time - Runtime.START_TIME, NANOSECONDS));
    }

    @Override
    public BigInteger getNanoSeconds() {
        return BigInteger.valueOf(time - Runtime.START_TIME % 1000000000L);
    }
}
