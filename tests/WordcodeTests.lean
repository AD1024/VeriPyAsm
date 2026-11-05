import VeriPyAsm.CPython.V314.Wordcode

namespace VeriPyAsm.Tests.Wordcode

open CPython.V314 CPython.V314.Wordcode

private def success (start : Nat) (bytes : List Nat) : Option (Header × List Nat) :=
  match read start bytes with
  | .ok result => some result
  | .error _ => none

private def failure (start : Nat) (bytes : List Nat) : Option DecodeError :=
  match read start bytes with
  | .ok _ => none
  | .error error => some error

-- No prefix: operands retain all eight bits, and the physical offset is unchanged.
example : success 0 [82, 0] = some (⟨0, 0, 82, 0, []⟩, []) := by decide
example : success 8 [82, 255] = some (⟨8, 8, 82, 255, []⟩, []) := by decide

-- Smallest and largest operands for each admitted prefix count.
example : success 0 [69, 1, 82, 0] =
    some (⟨0, 2, 82, 256, [1]⟩, []) := by decide
example : success 0 [69, 255, 82, 255] =
    some (⟨0, 2, 82, 65535, [255]⟩, []) := by decide
example : success 0 [69, 1, 69, 0, 82, 0] =
    some (⟨0, 4, 82, 65536, [1, 0]⟩, []) := by decide
example : success 0 [69, 255, 69, 255, 82, 255] =
    some (⟨0, 4, 82, 16777215, [255, 255]⟩, []) := by decide
example : success 0 [69, 1, 69, 0, 69, 0, 82, 0] =
    some (⟨0, 6, 82, 16777216, [1, 0, 0]⟩, []) := by decide
example : success 0 [69, 127, 69, 255, 69, 255, 82, 255] =
    some (⟨0, 6, 82, 2147483647, [127, 255, 255]⟩, []) := by decide

-- Prefixes preserve their order and physical offset; cache and trailing bytes
-- are returned unchanged, including bytes this header parser has not validated.
example : success 10 [69, 1, 69, 2, 44, 3, 0, 0, 999] =
    some (⟨10, 14, 44, 66051, [1, 2]⟩, [0, 0, 999]) := by decide

-- The header parser intentionally leaves opcode-specific checks to Decode.
example : success 0 [69, 1, 35, 0] =
    some (⟨0, 2, 35, 256, [1]⟩, []) := by decide
example : success 0 [69, 1, 87, 0] =
    some (⟨0, 2, 87, 256, [1]⟩, []) := by decide

-- Empty, incomplete, dangling, nonminimal, and overlong encodings.
example : failure 4 [] = some ⟨4, "missing instruction"⟩ := by decide
example : failure 4 [82] = some ⟨4, "truncated code unit"⟩ := by decide
example : failure 4 [69, 1] = some ⟨4, "dangling EXTENDED_ARG"⟩ := by decide
example : failure 4 [69, 1, 69, 0] = some ⟨4, "dangling EXTENDED_ARG"⟩ := by decide
example : failure 4 [69, 1, 82] = some ⟨6, "truncated code unit"⟩ := by decide
example : failure 4 [69, 0, 82, 0] =
    some ⟨4, "leading EXTENDED_ARG must be nonzero"⟩ := by decide
example : failure 4 [69, 1, 69, 0, 69, 0, 69, 0, 82, 0] =
    some ⟨10, "more than three EXTENDED_ARG prefixes"⟩ := by decide

-- The maximum unsigned 32-bit operand and the first negative signed encoding
-- are outside the compiler profile; natural-number arithmetic cannot wrap.
example : failure 0 [69, 128, 69, 0, 69, 0, 82, 0] =
    some ⟨6, "operand exceeds signed 32-bit range"⟩ := by decide
example : failure 0 [69, 255, 69, 255, 69, 255, 82, 255] =
    some ⟨6, "operand exceeds signed 32-bit range"⟩ := by decide

-- Every consumed opcode and operand byte is checked, also inside a prefix chain.
example : failure 4 [256] = some ⟨4, "byte value exceeds 255"⟩ := by decide
example : failure 4 [256, 0] = some ⟨4, "byte value exceeds 255"⟩ := by decide
example : failure 4 [82, 256] = some ⟨5, "byte value exceeds 255"⟩ := by decide
example : failure 4 [69, 256, 82, 0] = some ⟨5, "byte value exceeds 255"⟩ := by decide
example : failure 4 [69, 1, 256, 0] = some ⟨6, "byte value exceeds 255"⟩ := by decide
example : failure 4 [69, 1, 82, 256] = some ⟨7, "byte value exceeds 255"⟩ := by decide

end VeriPyAsm.Tests.Wordcode
