import Mathlib

/-!
# A254130: factorials exclusionary in decimal digits

Source: https://oeis.org/A254130
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A254/A254130.seq
Credit: @Bondyboy2001

A nonnegative integer `n` is in the sequence when the decimal digits of `n` and of `n!` are
disjoint. The source sequence starts at `0`.
-/

namespace OMA.S_oeis_a254130

/-- `n` and `n!` have no decimal digit in common. -/
def ExclusionaryFactorial (n : ℕ) : Prop :=
  ∀ d : ℕ, d ∈ Nat.digits 10 n → d ∉ Nat.digits 10 n.factorial

/-- The conjecture that the sequence is finite and ends at `16`. -/
theorem main : IsGreatest {n : ℕ | ExclusionaryFactorial n} 16 := by
  sorry

end OMA.S_oeis_a254130
