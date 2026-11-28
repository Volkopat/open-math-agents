import Mathlib

/-!
# A188474: A generalized Deutsch triangle.

Source: https://oeis.org/A188474
Credit: @thtsben2

The generalized Deutsch triangle (`r = 2`, offset 0) is defined by
`T(n, k) = ∑_{j=0}^{n - k + 1} (j / (n + 2 - j)) * C(n + 2 - j, n - k + 1) * C(n + 2 - j, k + 1) * 2^(j - 1)`.
Conjecture (Paul Barry, OEIS): the row sums `∑_{k=0}^{n} T(n, k)` equal `A137398(n + 1)`
(using 0-based indexing `0, 1, 2, 7, 22, 74, ...`, i.e., `A137398(n + 2)` under OEIS offset 1
where `a(1) = 0, a(2) = 1, a(3) = 2, a(m) = 2*a(m-1) + 2*a(m-2) + ∑_{k=1}^{m-3} C_k * a(m-k-1)`).
-/

namespace OMA.S_oeis_a188474

/-- The `k`-th Catalan number `C(2k, k) / (k + 1)`. -/
def catalan (k : ℕ) : ℕ := Nat.choose (2 * k) k / (k + 1)

/-- `A137398` (OEIS offset 1: `a(1) = 0, a(2) = 1, a(3) = 2, ...`, with `a(0) = 0`). -/
def A137398 : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | n + 4 =>
      2 * A137398 (n + 3) + 2 * A137398 (n + 2) +
        ∑ k ∈ Finset.Icc 1 (n + 1), catalan k * A137398 (n + 3 - k)
decreasing_by all_goals omega

/-- Entry `T(n, k)` of the generalized Deutsch triangle A188474. -/
def T (n k : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 (n - k + 1),
    ((j : ℚ) / ((n + 2 - j : ℕ) : ℚ)) *
      ((Nat.choose (n + 2 - j) (n - k + 1) : ℕ) : ℚ) *
      ((Nat.choose (n + 2 - j) (k + 1) : ℕ) : ℚ) *
      (2 : ℚ) ^ (j - 1)

theorem main : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), T n k = (A137398 (n + 2) : ℚ) := by
  sorry

end OMA.S_oeis_a188474
