import Mathlib

/-!
# OEIS A182749 and multiples with prescribed divisor count

Source: https://oeis.org/A182749 (Jon E. Schoenfield, June 1, 2024).
Credit: @FransDevelopment

For positive n, A182749(n) is the least n-digit multiple of n having exactly n
positive divisors, or zero if none exists. Every candidate is positive by the
lower digit bound. Thus positivity of the sequence is equivalent to existence
of a candidate. The entry records A182749(4) = 0.
-/

namespace OMA.S_oeis_a182749

/-- The positive multiples counted by the defining minimum, in base ten. -/
def Candidate (n m : ℕ) : Prop :=
  n ∣ m ∧ 10 ^ (n - 1) ≤ m ∧ m < 10 ^ n ∧ m.divisors.card = n

/-- Among positive nonsquarefree indices, exactly 4 has no candidate. -/
theorem main : ∀ n : ℕ, 0 < n → ¬ Squarefree n →
    ((∃ m : ℕ, Candidate n m) ↔ n ≠ 4) := by
  sorry

end OMA.S_oeis_a182749
