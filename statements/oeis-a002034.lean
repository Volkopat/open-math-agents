import Mathlib

/-!
# OEIS A002034 (Kempner numbers): a trigonometric formula

Source: https://oeis.org/A002034
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Mats Granvik, in the OEIS entry): for `n ≥ 1`,
`a(n) = 1 + n - ∑_{k=1}^{n} ∑_{m=1}^{n} cos(-2π k m! / n) / n`,
where `a(n)` is the smallest positive integer `m` such that `n` divides `m!`.
-/

namespace OMA.S_oeis_a002034

/-- Kempner function: least `m ≥ 1` with `n ∣ m!`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ n ∣ m.factorial}

/-- Granvik's formula. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = 1 + n - ∑ k ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 n,
        Real.cos (-2 * Real.pi * k / n * (m.factorial : ℝ)) / n := by
  sorry

end OMA.S_oeis_a002034
