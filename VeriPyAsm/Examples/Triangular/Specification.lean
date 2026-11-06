import VeriPyAsm.Examples.Triangular.Artifact
import VeriPyAsm.Verification.Block

/-! The contract and verification annotations, independent of either the
hand-written block proof or automatic VC generation. -/

namespace VeriPyAsm.Examples

open Semantics Verification

namespace Triangular

def frame (pc : Nat) (n sum : Int) (stack : List Value := []) : Frame :=
  { pc, locals := [some (.int n), some (.int sum)], stack }

def invariant (N : Int) (current : Frame) : Prop :=
  ∃ n sum : Int, current = frame 6 n sum ∧ 0 ≤ n ∧
    2 * sum + n * (n + 1) = N * (N + 1)

/-- Only invariant states use this rank. Their first local is a nonnegative int;
the default for other states carries no semantic claim. -/
def rank (current : Frame) : Nat :=
  match current.locals[(0 : Nat)]? with
  | some (some (.int n)) => n.toNat
  | _ => 0

def postcondition (N : Int) : Postcondition :=
  { returned := fun value final => ∃ result : Int,
      value = .int result ∧ 2 * result = N * (N + 1) ∧
      final.locals = [some (.int 0), some (.int result)] ∧ final.stack = [] }

end Triangular

/-- Nonnegative exact integers are accepted. The return equation avoids any
division convention, and the final locals record the exhausted counter and sum. -/
def triangularContract : Contract Int where
  pre N initial := 0 ≤ N ∧ initial = { locals := [some (.int N), none] }
  post N _ := (Triangular.postcondition N).returned
  raises _ _ _ _ := False

end VeriPyAsm.Examples
