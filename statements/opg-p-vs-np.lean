import Mathlib

/-!
# P vs. NP

Source: https://www.openproblemgarden.org/op/p_vs_np
Credit: @Ciphore

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

Since decision problems here are already bitstrings, the input encoding is the identity.  A binary
string is made self-delimiting by doubling each bit after `true` and terminating with `false`;
this standard encoding is used for the first component of a verifier input.
-/

namespace OMA.S_opg_p_vs_np

open Computability Turing

/-- Self-delimiting binary encoding of a bitstring. -/
def encodeBitsWithEnd : List Bool → List Bool
  | [] => [false]
  | b :: l => true :: b :: encodeBitsWithEnd l

/-- Encode a pair of bitstrings as one bitstring. -/
def encodeBitPair (x : List Bool × List Bool) : List Bool :=
  encodeBitsWithEnd x.1 ++ x.2

/-- A bitstring decision problem computable in polynomial time. -/
def IsPolyTimeDecision (L : List Bool → Bool) : Prop :=
  Nonempty (TM2ComputableInPolyTime id encodeBool L)

/-- A bitstring verifier relation computable in polynomial time. -/
def IsPolyTimeVerifier (R : List Bool × List Bool → Bool) : Prop :=
  Nonempty (TM2ComputableInPolyTime encodeBitPair encodeBool R)

/-- The deterministic polynomial-time decision class. -/
def PClass : Set (List Bool → Bool) := {L | IsPolyTimeDecision L}

/-- The nondeterministic polynomial-time decision class, using polynomially bounded witnesses. -/
def NPClass : Set (List Bool → Bool) :=
  {L | ∃ p : Polynomial ℕ, ∃ R : List Bool × List Bool → Bool,
    IsPolyTimeVerifier R ∧ ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ R (x, w)}

/-- The P versus NP problem. -/
theorem main : PClass ≠ NPClass := by
  sorry

end OMA.S_opg_p_vs_np
