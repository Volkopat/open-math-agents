import Mathlib

/-!
# A401787: a(n) is the number of prime quadruplets (q, q+2, q+6, q+8) with q strictly between p+8 and 2*(p+8), where p = A007530(n).

Source: https://oeis.org/A401787
Credit: @gblacher2

Conjecture (OEIS A401787): a(n) >= 1 for all n >= 5.

OEIS indexes A007530 and A401787 from 1, so `A007530 n = Nat.nth IsPrimeQuadruplet (n - 1)`.
A finite list of quadruplets would not make the statement vacuous: its last member, with
index at least 5, would have `a n = 0`.
-/

namespace OMA.S_oeis_a401787

/-- `q` starts a prime quadruplet `(q, q + 2, q + 6, q + 8)` (the terms of A007530). -/
def IsPrimeQuadruplet (q : ℕ) : Prop :=
  q.Prime ∧ (q + 2).Prime ∧ (q + 6).Prime ∧ (q + 8).Prime

/-- A007530(n), the first member of the `n`-th prime quadruplet (1-indexed). -/
noncomputable def A007530 (n : ℕ) : ℕ :=
  Nat.nth IsPrimeQuadruplet (n - 1)

/-- A401787(n): the number of prime quadruplets `(q, q + 2, q + 6, q + 8)` with
`p + 8 < q < 2 * (p + 8)`, where `p = A007530 n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {q : ℕ | A007530 n + 8 < q ∧ q < 2 * (A007530 n + 8) ∧ IsPrimeQuadruplet q}.ncard

theorem main : ∀ n : ℕ, 5 ≤ n → 1 ≤ a n := by
  sorry

end OMA.S_oeis_a401787
