import Mathlib

/-!
# A358618: First differences of A258036

Source: https://oeis.org/A358618

Conjecture (OEIS A358618):
Let `A258036` be the set of positive integers `k` such that the `(k - 1)`-st forward
difference of the first `k` prime numbers is strictly negative:
`∑_{j=0}^{k-1} (-1)^(k - 1 - j) * C(k - 1, j) * prime(j + 1) < 0`.
Then every first difference of `A258036` belongs to `{1, 2, 3}` (equivalently, for
every `k ∈ A258036`, at least one of `k + 1`, `k + 2`, `k + 3` also belongs to `A258036`).

Conventions:
- First terms of A258036: `4, 6, 8, 10, 12, 14, 17, 19, 21, 23, 25, 28, ...`.
- First terms of A358618: `2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 3, ...`.
-/

namespace OMA.S_oeis_a358618

/-- The `(k - 1)`-st forward difference of the first `k` prime numbers (`k ≥ 1`). -/
noncomputable def primeForwardDiff (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range k,
    (-1 : ℤ) ^ (k - 1 - j) * (Nat.choose (k - 1) j : ℤ) * (Nat.nth Nat.Prime j : ℤ)

/-- Membership predicate for OEIS A258036. -/
def InA258036 (k : ℕ) : Prop :=
  1 ≤ k ∧ primeForwardDiff k < 0

/-- Conjecture: all first differences of A258036 lie in `{1, 2, 3}`. -/
theorem main :
    ∀ k : ℕ, InA258036 k →
      InA258036 (k + 1) ∨ InA258036 (k + 2) ∨ InA258036 (k + 3) := by
  sorry

end OMA.S_oeis_a358618
