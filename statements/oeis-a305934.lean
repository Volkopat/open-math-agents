import Mathlib

/-!
# A305934: Powers of 3 that have exactly one digit '0' in base 10.

Source: https://oeis.org/A305934
Credit: @EtienneLefranc

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a305934

/-- `n` is a term of A305934: a power of 3 that has exactly one digit '0' in base 10. -/
def IsTerm (n : ℕ) : Prop := (∃ k : ℕ, n = 3 ^ k) ∧ (Nat.digits 10 n).count 0 = 1

/-- Conjecture (OEIS comment): it appears that this sequence is finite. -/

theorem main : {n : ℕ | IsTerm n}.Finite := by
  sorry

end OMA.S_oeis_a305934

