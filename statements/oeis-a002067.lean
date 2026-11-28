import Mathlib

/-!
# OEIS A002067: a hafnian formula

Source: https://oeis.org/A002067
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(0) = 1`, `a(n) = ∑_{k=0}^{n-1} C(2n, 2k) a(k) a(n-k-1)`: `1, 1, 7, 127, 4369, …`.
Conjecture (Callan, 2017): `a(n)` is the hafnian of the triangular array `u(i, j) = i`
(`1 ≤ i < j ≤ 2n`), i.e. the sum over all perfect matchings of `{1, …, 2n}` of the product,
over the pairs `{i < j}` of the matching, of `i`.

Conventions:
* A perfect matching of `Fin (2n)` is a fixed-point-free involution `σ`; each pair `{i, σ i}`
  contributes its smaller element, counted from `1`. Taking the product over all `i` with
  `i < σ i` counts each pair once.
-/

namespace OMA.S_oeis_a002067

/-- The sequence, via its defining recurrence. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), (2 * (n + 1)).choose (2 * k) * a k * a (n - k)
decreasing_by
  all_goals (have := k.isLt; omega)

/-- The hafnian of `u(i, j) = i` on `{1, …, 2n}`. -/
def haf (n : ℕ) : ℕ :=
  ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin (2 * n)))).filter
      (fun σ => ∀ i, σ i ≠ i ∧ σ (σ i) = i),
    ∏ i ∈ Finset.univ.filter (fun i => i < σ i), ((i : ℕ) + 1)

/-- `a(n)` is the hafnian of `u(i, j) = i`. -/
theorem main : ∀ n : ℕ, a n = haf n := by
  sorry

end OMA.S_oeis_a002067
