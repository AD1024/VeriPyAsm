import VeriPyAsm.CPython.V314.DecodeError

/-!
Parsing of one CPython 3.14.4 wordcode instruction header.

An instruction header contains up to three `EXTENDED_ARG` code units followed by
the terminal opcode's code unit. Inline caches are deliberately left to the
opcode-specific decoder. The raw prefix bytes and terminal opcode offset remain
available so that grouping code units does not erase their physical layout.

The admitted compiler profile requires a nonzero first prefix and a nonnegative
signed 32-bit operand. Opcode-specific operand restrictions belong to `Decode`.
This grouping is a decoding operation, not a claim that CPython dispatches the
whole group in one interpreter step.
-/

namespace VeriPyAsm.CPython.V314.Wordcode

structure Header where
  start : Nat
  opcodeOffset : Nat
  opcode : Nat
  arg : Nat
  prefixes : List Nat
  deriving Repr, DecidableEq

private def fail {α : Type} (offset : Nat) (reason : String) : Except DecodeError α :=
  .error ⟨offset, reason⟩

/-- `remaining` bounds the number of prefixes still admitted, independently of
the input length. `acc` contains the prefix operand bytes in big-endian order. -/
private def readAux (start offset acc : Nat) (prefixes : List Nat)
    (remaining : Nat) (bytes : List Nat) : Except DecodeError (Header × List Nat) :=
  match bytes with
  | [] =>
      if prefixes.isEmpty then fail offset "missing instruction"
      else fail start "dangling EXTENDED_ARG"
  | [opcode] =>
      if opcode > 255 then fail offset "byte value exceeds 255"
      else fail offset "truncated code unit"
  | opcode :: byteArg :: rest => do
      if opcode > 255 then fail offset "byte value exceeds 255"
      else if byteArg > 255 then fail (offset + 1) "byte value exceeds 255"
      else if opcode = 69 then
        if prefixes.isEmpty && byteArg == 0 then
          fail offset "leading EXTENDED_ARG must be nonzero"
        else
          match remaining with
          | 0 => fail offset "more than three EXTENDED_ARG prefixes"
          | n + 1 =>
              readAux start (offset + 2) (acc * 256 + byteArg)
                (prefixes ++ [byteArg]) n rest
      else
        let arg := acc * 256 + byteArg
        if arg > 2147483647 then fail offset "operand exceeds signed 32-bit range"
        else .ok (⟨start, offset, opcode, arg, prefixes⟩, rest)

/-- Consume the prefix chain and terminal two-byte code unit, returning the
remaining bytes before any inline caches. Only consumed bytes are validated. -/
def read (start : Nat) (bytes : List Nat) : Except DecodeError (Header × List Nat) :=
  readAux start start 0 [] 3 bytes

end VeriPyAsm.CPython.V314.Wordcode
