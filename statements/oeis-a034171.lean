import Mathlib

/-!
# A034171: Related to triple factorial numbers A007559(n+1).

Source: https://oeis.org/A034171
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a034171

/-- The OEIS entry with its displayed offset: `3^n*(3*n+1)!!!/(n+1)!`. -/
def entry (n : ℕ) : ℕ :=
  (3 ^ n * ∏ k ∈ Finset.range (n + 1), (3 * k + 1)) / Nat.factorial (n + 1)

/-- The sequence reindexed with offset `1`, as specified by the conjecture. -/
def a (n : ℕ) : ℕ :=
  entry (n - 1)

/-- The exceptional indices in Peter Bala's conjecture. -/
def excluded (p n : ℕ) : Prop :=
  ∃ m k : ℕ, m ≤ (p - 1) / 3 ∧ 1 ≤ k ∧ k ≤ (p - 1) / 3 ∧ n = m * p + k

/-- Peter Bala's conjecture for the offset-`1` indexing of the sequence. -/
theorem main :
    ∀ p n : ℕ, p.Prime → p ≡ 1 [MOD 3] → 0 < n → ¬ excluded p n →
      a (p * n) ≡ a n [MOD p ^ 2] := by
  sorry

end OMA.S_oeis_a034171
