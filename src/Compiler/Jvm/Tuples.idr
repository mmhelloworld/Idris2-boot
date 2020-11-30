module Compiler.Jvm.Tuples

public export
second : (a, b, c) -> b
second (_, value, _) = value

public export
third : (a, b, c) -> c
third (_, _, value) = value