module Compiler.Jvm.Label

ifLabelName : Nat -> Nat -> String
ifLabelName ifIndex labelIndex = "$if" ++ show ifIndex ++ "$label" ++ show labelIndex

lineNumberLabelName : Nat -> String
lineNumberLabelName labelIndex = "L" ++ show labelIndex