import Mathlib

/-!
# A392672: Smallest number m such that m*(m+1)*(m+2) has exactly n distinct prime factors.

Source: https://oeis.org/A392672
Credit: @azmiozgen

Conjecture (from the entry): this is an increasing sequence.

Formalization notes:
* a(n), offset 2, is the least m ≥ 1 such that m(m+1)(m+2) has exactly n distinct prime factors.
* Increasing is stated as a(n) < a(n+1) for all n ≥ 2.
* Controls (computed): a(2..10) = 1, 3, 5, 13, 33, 153, 285, 713, 5795, as in the entry.
-/

namespace OMA.S_oeis_a392672

/-- A392672(n): the least `m ≥ 1` with `m(m+1)(m+2)` having exactly `n` distinct prime factors. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ (m * (m + 1) * (m + 2)).primeFactors.card = n}

/-- The sequence is increasing from its offset `n = 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → a n < a (n + 1) := by
  sorry

end OMA.S_oeis_a392672
