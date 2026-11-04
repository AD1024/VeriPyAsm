import VeriPyAsm.CPython.V314.Stack.Certificate

namespace VeriPyAsm.Tests.StackCertificate

open CPython.V314 CPython.V314.Stack

private def small : Code := ⟨[
  ⟨0, 2, 128, 0, .resume⟩,
  ⟨2, 4, 94, 1, .loadSmallInt 1⟩,
  ⟨4, 6, 35, 0, .returnValue⟩]⟩

private def table : Heights := [(0, 0), (2, 0), (4, 1)]

example : Valid small 1 table := by decide
example : ¬ Valid small 0 table := by decide
example : ¬ Valid small 1 [(0, 0), (2, 0)] := by decide
example : ¬ Valid small 1 [(2, 0), (4, 1)] := by decide
example : ¬ Valid small 1 [(0, 0), (2, 0), (4, 0)] := by decide
example : ¬ Valid small 1 (table ++ [(4, 1)]) := by decide
example : ¬ Valid small 1 (table ++ [(3, 0)]) := by decide
example : ¬ (Instruction.mk 0 2 39 0 .toBool).StackReady 0 := by decide
example : ¬ (Instruction.mk 0 2 35 0 .returnValue).StackReady 2 := by decide

end VeriPyAsm.Tests.StackCertificate
