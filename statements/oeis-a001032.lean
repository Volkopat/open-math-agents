import Mathlib

/-!
# A001032: Numbers k such that sum of squares of k consecutive integers >= 1 is a square.

Source: https://oeis.org/A001032
Credit: @tueksta

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a001032

/-- `k` is a term of A001032: there are `k` consecutive integers `m, m+1, ..., m+k-1`,
all at least `1`, whose squares sum to a perfect square. -/
def InA001032 (k : ℕ) : Prop :=
  0 < k ∧ ∃ m r : ℕ, 0 < m ∧ ∑ i ∈ Finset.range k, (m + i) ^ 2 = r ^ 2

/-- Ralf Stephan's observation, which Thomas Andrews's necessary conditions establish:
every term of A001032 is congruent to 0, 1, 2, 9, 11, 16 or 23 modulo 24. -/
theorem main : ∀ k : ℕ, InA001032 k →
    k % 24 ∈ ({0, 1, 2, 9, 11, 16, 23} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a001032
