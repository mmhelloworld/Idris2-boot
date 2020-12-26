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
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.OpenOption;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.nio.file.attribute.BasicFileAttributes;
import java.nio.file.attribute.PosixFilePermission;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.IntStream;

import static io.github.mmhelloworld.idris2boot.runtime.Paths.createPath;
import static io.github.mmhelloworld.idris2boot.runtime.Runtime.IS_POSIX;
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
    private static final Map<Integer, PosixFilePermission> modeToPermissions = new HashMap<>();
    private static final String WORKING_DIR = System.getProperty("user.dir");

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
    private IOException exception;

    private ChannelIo(Path path, Channel channel, IOException exception) {
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
        handleException(exception);
    }

    public ChannelIo(Path path, Channel channel) {
        this(path, channel, null);
    }

    public ChannelIo(Path path, IOException exception) {
        this(path, null, exception);
    }

    public char getChar() {
        exception = null;
        try {
            return byteBufferIo.getChar();
        } catch (IOException e) {
            handleException(e);
            return 0;
        }
    }

    public static char getChar(ChannelIo file) {
        return file.getChar();
    }

    public String getChars(int count) {
        exception = null;
        String result = IntStream.range(0, count)
            .map(index -> getChar())
            .collect(StringBuilder::new, StringBuilder::append, StringBuilder::append)
            .toString();
        return exception != null ? result : null;
    }

    public static String getChars(int count, ChannelIo file) {
        return file.getChars(count);
    }

    public String getLine() {
        exception = null;
        try {
            return byteBufferIo.getLine();
        } catch (IOException e) {
            handleException(e);
            return null;
        }
    }

    public void handleException(IOException e) {
        this.exception = e;
        if (e != null) {
            e.printStackTrace();
        }
        Runtime.setErrorNumber(getErrorNumber(e));
    }

    public static String getLine(ChannelIo file) {
        return file.getLine();
    }

    public void writeString(String str) {
        exception = null;
        try {
            byteBufferIo.writeString(str);
            flush();
        } catch (IOException e) {
            handleException(e);
        }
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
        } catch (IOException exception) {
            setErrorNumber(getErrorNumber(exception));
            return null;
        }
    }

    public static void close(ChannelIo file) {
        file.close();
    }

    public int chmod(int mode) {
        this.exception = null;
        if (IS_POSIX) {
            try {
                Files.setPosixFilePermissions(path, createPosixFilePermissions(mode));
            } catch (IOException e) {
                handleException(e);
                return -1;
            }
        }
        return 0;
    }

    public static int chmod(String file, int mode) {
        return open(file, "r").chmod(mode);
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

    public void flush() {
        exception = null;
        try {
            if (channel instanceof FileChannel) {
                ((FileChannel) channel).force(true);
            }
        } catch (IOException e) {
            handleException(e);
        }
    }

    public static int flush(ChannelIo file) {
        file.flush();
        return file.exception == null ? 0 : 1;
    }

    public boolean isEof() {
        exception = null;
        try {
            return !byteBufferIo.hasChar();
        } catch (IOException e) {
            handleException(e);
            return true;
        }
    }

    public long size() {
        exception = null;
        try {
            if (channel instanceof SeekableByteChannel) {
                return ((SeekableByteChannel) channel).size();
            } else {
                return -1;
            }
        } catch (IOException e) {
            handleException(e);
            return -1;
        }
    }

    public static int size(ChannelIo file) {
        return (int) file.size();
    }

    @Override
    public boolean isOpen() {
        return channel.isOpen();
    }

    @Override
    public void close() {
        try {
            if (channel != null) {
                channel.close();
            }
        } catch (IOException exception) {
            this.exception = exception;
        }
    }

    public Path getPath() {
        return path;
    }

    public int delete() {
        exception = null;
        try {
            Files.delete(path);
            return 0;
        } catch (IOException e) {
            handleException(e);
            return -1;
        }
    }

    public static int delete(ChannelIo file) {
        return file.delete();
    }

    public long getFileModifiedTime() {
        exception = null;
        try {
            return Files.readAttributes(path, BasicFileAttributes.class)
                .lastModifiedTime()
                .to(SECONDS);
        } catch (IOException e) {
            handleException(e);
            return -1;
        }
    }

    public static int getFileModifiedTime(ChannelIo file) {
        return (int) file.getFileModifiedTime();
    }

    public long getFileAccessTime() {
        exception = null;
        try {
            return Files.readAttributes(path, BasicFileAttributes.class)
                .lastAccessTime()
                .to(SECONDS);
        } catch (IOException e) {
            handleException(e);
            return -1;
        }
    }

    public static int getFileAccessTime(ChannelIo file) {
        return (int) file.getFileAccessTime();
    }

    public long getFileStatusTime() {
        try {
            return Files.readAttributes(path, BasicFileAttributes.class)
                .creationTime()
                .to(SECONDS);
        } catch (IOException e) {
            handleException(e);
            return -1;
        }
    }

    public static int getFileStatusTime(ChannelIo file) {
        return (int) file.getFileStatusTime();
    }

    @Override
    public int read(ByteBuffer dst) throws IOException {
        return ((ReadableByteChannel) channel).read(dst);
    }

    @Override
    public int write(ByteBuffer src) throws IOException {
        return ((WritableByteChannel) channel).write(src);
    }

    public IOException getException() {
        return exception;
    }

    public static int getErrorNumber(ChannelIo file) {
        IOException exception = file.getException();
        return getErrorNumber(exception);
    }

    private static int getErrorNumber(IOException exception) {
        if (exception == null) {
            return 0;
        } else if (exception instanceof FileNotFoundException || exception instanceof NoSuchFileException) {
            return 2; // To return error codes to conform to Idris functions with C FFIs
        } else if (exception instanceof AccessDeniedException) {
            return 3;
        } else if (exception instanceof FileAlreadyExistsException) {
            return 4;
        } else {
            return 10;
        }
    }
}
