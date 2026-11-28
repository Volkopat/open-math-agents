import Mathlib

/-!
# OEIS A061262: smallest number with exactly n representations as a sum of 3 triangular numbers

Source: https://oeis.org/A061262
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest number representable as the sum of 3 triangular numbers in exactly `n`
ways (`0` counts as triangular; representations are unordered, i.e. multisets of indices
`i ≤ j ≤ k` with `T_i + T_j + T_k = m`, `T_i = i(i+1)/2`, as in the entry's example for 57).
Conjectures in the entry:
* (Cloitre) for `n` large enough, `1 < a(n)/n² < 2`;
* (Z.-W. Sun) no term `a(n)` with `n > 2` is `≡ 0` or `3 (mod 5)`.
-/

namespace OMA.S_oeis_a061262

/-- Number of unordered representations of `m` as a sum of three triangular numbers. -/
def ways (m : ℕ) : ℕ :=
  ((Finset.range (m + 1) ×ˢ Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter fun t =>
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
      t.1 * (t.1 + 1) / 2 + t.2.1 * (t.2.1 + 1) / 2 + t.2.2 * (t.2.2 + 1) / 2 = m).card

/-- `a(n)`: the least `m` with exactly `n` representations. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m | ways m = n}

/-- Cloitre's and Sun's conjectures. -/
theorem main :
    (∃ N : ℕ, ∀ n ≥ N, n ^ 2 < a n ∧ a n < 2 * n ^ 2) ∧
      ∀ n : ℕ, 2 < n → a n % 5 ≠ 0 ∧ a n % 5 ≠ 3 := by
  sorry

end OMA.S_oeis_a061262
