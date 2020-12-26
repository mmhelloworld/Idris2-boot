package io.github.mmhelloworld.idris2boot.runtime;

import java.io.Closeable;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.Channel;
import java.nio.channels.FileChannel;
import java.nio.channels.ReadableByteChannel;
import java.nio.channels.SeekableByteChannel;
import java.nio.channels.WritableByteChannel;
import java.nio.file.AccessDeniedException;
import java.nio.file.FileAlreadyExistsException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.OpenOption;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.nio.file.attribute.BasicFileAttributes;
import java.nio.file.attribute.FileTime;
import java.nio.file.attribute.PosixFilePermission;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.IntStream;

import static io.github.mmhelloworld.idris2boot.runtime.Paths.createPath;
import static io.github.mmhelloworld.idris2boot.runtime.Runtime.setErrorNumber;
import static java.nio.charset.StandardCharsets.UTF_8;
import static java.nio.file.attribute.PosixFilePermission.GROUP_EXECUTE;
import static java.nio.file.attribute.PosixFilePermission.GROUP_READ;
import static java.nio.file.attribute.PosixFilePermission.GROUP_WRITE;
import static java.nio.file.attribute.PosixFilePermission.OTHERS_EXECUTE;
import static java.nio.file.attribute.PosixFilePermission.OTHERS_READ;
import static java.nio.file.attribute.PosixFilePermission.OTHERS_WRITE;
import static java.nio.file.attribute.PosixFilePermission.OWNER_EXECUTE;
import static java.nio.file.attribute.PosixFilePermission.OWNER_READ;
import static java.nio.file.attribute.PosixFilePermission.OWNER_WRITE;
import static java.util.Arrays.asList;
import static java.util.Collections.singletonList;
import static java.util.concurrent.TimeUnit.SECONDS;
import static java.util.stream.Collectors.toSet;

public class ChannelIo implements ReadableByteChannel, WritableByteChannel, Closeable {
    private static final boolean IS_POSIX = FileSystems.getDefault().supportedFileAttributeViews().contains("posix");
    private static final Map<Integer, PosixFilePermission> modeToPermissions = new HashMap<>();

    static {
        modeToPermissions.put(256, OWNER_READ);
        modeToPermissions.put(128, OWNER_WRITE);
        modeToPermissions.put(64, OWNER_EXECUTE);
        modeToPermissions.put(32, GROUP_READ);
        modeToPermissions.put(16, GROUP_WRITE);
        modeToPermissions.put(8, GROUP_EXECUTE);
        modeToPermissions.put(4, OTHERS_READ);
        modeToPermissions.put(2, OTHERS_WRITE);
        modeToPermissions.put(1, OTHERS_EXECUTE);
    }

    private final Path path;
    private final Channel channel;
    private final ByteBufferIo byteBufferIo;
    private Exception exception;

    ChannelIo(Path path, Channel channel) {
        this.path = path;
        this.channel = channel;
        FunctionE<ByteBuffer, Integer, IOException> reader = channel instanceof ReadableByteChannel ?
            ((ReadableByteChannel) channel)::read : buffer -> {
            throw new IOException("File is not readable");
        };
        FunctionE<ByteBuffer, Integer, IOException> writer = channel instanceof WritableByteChannel ?
            ((WritableByteChannel) channel)::write : buffer -> {
            throw new IOException("File is not writable");
        };
        this.byteBufferIo = new ByteBufferIo(reader, writer);
    }

    public ChannelIo(Path path) {
        this(path, null);
    }

    public static char getChar(ChannelIo file) {
        return file.getChar();
    }

    public static String getChars(int count, ChannelIo file) {
        return file.getChars(count);
    }

    public static String getLine(ChannelIo file) {
        return file.getLine();
    }

    public static int writeString(ChannelIo file, String str) {
        file.writeString(str);
        return file.exception != null ? 0 : 1;
    }

    public static int isEof(ChannelIo file) {
        return file.isEof() || file.exception != null ? 1 : 0;
    }

    public static ChannelIo open(Path path, OpenOption... openOptions) throws IOException {
        if (path.getParent() != null) {
            Files.createDirectories(path.getParent());
        }
        return new ChannelIo(path, FileChannel.open(path, openOptions));
    }

    public static ChannelIo open(String name, String mode) {
        Path path = createPath(name);
        try {
            if (!isReadOnlyMode(mode)) {
                ensureParentDirectory(path);
            }
            return open(path, getOpenOptions(mode).toArray(new OpenOption[]{}));
        } catch (Exception exception) {
            setErrorNumber(getErrorNumber(exception));
            return null;
        }
    }

    public static void close(ChannelIo file) {
        file.close();
    }

    public static int chmod(String file, int mode) {
        return new ChannelIo(createPath(file))
            .chmod(mode);
    }

    public static void createDirectories(Path dirPath) throws IOException {
        if (dirPath != null) {
            java.nio.file.Files.createDirectories(dirPath);
        }
    }

    public static void writeFile(String pathString, String content) throws IOException {
        Path path = createPath(pathString);
        byte[] bytes = content.getBytes(UTF_8);
        createDirectories(path.getParent());
        Files.write(path, bytes);
    }

    public static int flush(ChannelIo file) {
        file.flush();
        return file.exception == null ? 0 : 1;
    }

    public static int size(ChannelIo file) {
        return (int) file.size();
    }

    public static int delete(ChannelIo file) {
        return file.delete();
    }

    public static int getFileModifiedTime(ChannelIo file) {
        return (int) file.getFileModifiedTime();
    }

    public static int getFileAccessTime(ChannelIo file) {
        return (int) file.getFileAccessTime();
    }

    public static int getFileStatusTime(ChannelIo file) {
        return (int) file.getFileStatusTime();
    }

    public static int getErrorNumber(ChannelIo file) {
        return getErrorNumber(file.exception);
    }

    public char getChar() {
        return (char) withExceptionHandling(byteBufferIo::getChar);
    }

    public String getChars(int count) {
        return withExceptionHandling(() -> {
            String result = IntStream.range(0, count)
                .map(index -> getChar())
                .collect(StringBuilder::new, StringBuilder::append, StringBuilder::append)
                .toString();
            return exception != null ? result : null;
        });
    }

    public String getLine() {
        return withExceptionHandling(byteBufferIo::getLine);
    }

    public void handleException(Exception e) {
        this.exception = e;
        Runtime.setErrorNumber(getErrorNumber(e));
    }

    public void writeString(String str) {
        withExceptionHandling(() -> {
            byteBufferIo.writeString(str);
            flush();
            return null;
        });
    }

    public int chmod(int mode) {
        return withExceptionHandling(() -> {
            if (IS_POSIX) {
                Files.setPosixFilePermissions(path, createPosixFilePermissions(mode));
            }
            return 0;
        }, -1);
    }

    public void flush() {
        withExceptionHandling(() -> {
            if (channel instanceof FileChannel) {
                ((FileChannel) channel).force(true);
            }
            return null;
        });
    }

    public boolean isEof() {
        return withExceptionHandling(() -> !byteBufferIo.hasChar(), true);
    }

    public long size() {
        return withExceptionHandling(() -> {
            if (channel instanceof SeekableByteChannel) {
                return ((SeekableByteChannel) channel).size();
            } else {
                return -1;
            }
        }, -1);
    }

    @Override
    public boolean isOpen() {
        return channel.isOpen();
    }

    @Override
    public void close() {
        withExceptionHandling(() -> {
            if (channel != null) {
                channel.close();
            }
            return null;
        });
    }

    public int delete() {
        return withExceptionHandling(() -> {
            Files.delete(path);
            return 0;
        }, -1);
    }

    public long getFileModifiedTime() {
        return getTimeAttribute(BasicFileAttributes::lastModifiedTime);
    }

    public long getFileAccessTime() {
        return getTimeAttribute(BasicFileAttributes::lastAccessTime);
    }

    public long getFileStatusTime() {
        return getTimeAttribute(BasicFileAttributes::creationTime);
    }

    public long getTimeAttribute(Function<BasicFileAttributes, FileTime> attributeGetter) {
        return withExceptionHandling(() -> attributeGetter.apply(Files.readAttributes(path, BasicFileAttributes.class))
            .to(SECONDS), -1);
    }

    @Override
    public int read(ByteBuffer dst) throws IOException {
        return ((ReadableByteChannel) channel).read(dst);
    }

    @Override
    public int write(ByteBuffer src) throws IOException {
        return ((WritableByteChannel) channel).write(src);
    }

    static int getErrorNumber(Exception exception) {
        if (exception == null) {
            return 0;
        } else if (exception instanceof FileNotFoundException || exception instanceof NoSuchFileException) {
            return 2; // To return error codes to conform to Idris functions with C FFIs
        } else if (exception instanceof AccessDeniedException || exception instanceof SecurityException) {
            return 3;
        } else if (exception instanceof FileAlreadyExistsException) {
            return 4;
        } else {
            return 10;
        }
    }

    private <T> T withExceptionHandling(SupplierE<T, ? extends Exception> action) {
        exception = null;
        Runtime.setErrorNumber(0);
        try {
            return action.get();
        } catch (Exception e) {
            handleException(e);
            return null;
        }
    }

    private int withExceptionHandling(IntSupplierE<? extends Exception> action) {
        return withExceptionHandling(action, 0);
    }

    private int withExceptionHandling(IntSupplierE<? extends Exception> action, int fallback) {
        exception = null;
        Runtime.setErrorNumber(0);
        try {
            return action.get();
        } catch (Exception exception) {
            handleException(exception);
            return fallback;
        }
    }

    private boolean withExceptionHandling(BooleanSupplierE<? extends Exception> action, boolean fallback) {
        exception = null;
        Runtime.setErrorNumber(0);
        try {
            return action.get();
        } catch (Exception exception) {
            handleException(exception);
            return fallback;
        }
    }

    private long withExceptionHandling(LongSupplierE<? extends Exception> action, long fallback) {
        exception = null;
        Runtime.setErrorNumber(0);
        try {
            return action.get();
        } catch (Exception exception) {
            handleException(exception);
            return fallback;
        }
    }

    private static Set<PosixFilePermission> createPosixFilePermissions(int mode) {
        return modeToPermissions.entrySet().stream()
            .filter(modeAndPermission -> (mode & modeAndPermission.getKey()) == modeAndPermission.getKey())
            .map(Map.Entry::getValue)
            .collect(toSet());
    }

    private static void ensureParentDirectory(Path path) throws IOException {
        Path parent = path.getParent();
        if (parent != null) {
            createDirectories(parent);
        }
    }

    private static boolean isReadOnlyMode(String mode) {
        return "r".equalsIgnoreCase(mode);
    }

    private static Collection<OpenOption> getOpenOptions(String mode) {
        switch (mode.toLowerCase()) {
            case "r":
                return singletonList(StandardOpenOption.READ);
            case "w":
                return asList(StandardOpenOption.CREATE, StandardOpenOption.WRITE,
                    StandardOpenOption.TRUNCATE_EXISTING);
            case "a":
                return asList(StandardOpenOption.CREATE, StandardOpenOption.APPEND);
            case "r+":
                return asList(StandardOpenOption.READ, StandardOpenOption.WRITE);
            case "w+":
                return asList(StandardOpenOption.CREATE, StandardOpenOption.READ, StandardOpenOption.WRITE);
            case "a+":
                return asList(StandardOpenOption.CREATE, StandardOpenOption.READ, StandardOpenOption.APPEND);
            default:
                throw new IllegalArgumentException("Unknown file mode " + mode);
        }
    }
}
