import Mathlib

/-!
# A001652 and first occurrences in A123737

Source: https://oeis.org/A001652
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Kotesovec, listed in A001652): for `n > 1`, `a(n)` is the index of the first
occurrence of `n` in the sequence A123737, where `a(n) = 6 a(n-1) - a(n-2) + 2`, `a(0) = 0`,
`a(1) = 3`.

Conventions:
* A123737 is the sequence of partial sums of `(-1)^⌊k √2⌋`: `b(m) = ∑_{k=1}^{m} (-1)^⌊k √2⌋`
  (offset 1, as in its OEIS entry).
* "Index of the first occurrence of `n`": the least `m ≥ 1` with `b(m) = n`; the statement
  includes that `n` occurs.
-/

namespace OMA.S_oeis_a001652

/-- A001652. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 3
  | n + 2 => 6 * a (n + 1) - a n + 2

/-- A123737: partial sums of `(-1)^⌊k √2⌋`. -/
noncomputable def b (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (⌊(k : ℝ) * Real.sqrt 2⌋.toNat)

theorem main :
    ∀ n : ℕ, 1 < n → 1 ≤ a n ∧ b (a n).toNat = n ∧
      ∀ m : ℕ, 1 ≤ m → m < (a n).toNat → b m ≠ n := by
  sorry

end OMA.S_oeis_a001652
