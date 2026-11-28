import Mathlib

/-!
# A025163: Associated Legendre polynomial P_n^1(2^(-1/2)) * 2^(3n/2 - 1)

Source: https://oeis.org/A025163
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: Let `a(n) = 2^(3n/2 - 1) * P_n^1(2^(-1/2))`, where
`P_n^1(x) = -(1 - x^2)^(1/2) * P_n'(x)` is the associated Legendre polynomial of
degree `n` and order `1`. Then for all `n ≥ 2`,
`(-n + 1) * a(n) + 2 * (2n - 1) * a(n - 1) - 8 * n * a(n - 2) = 0`.
-/

namespace OMA.S_oeis_a025163

/-- The `n`-th Legendre polynomial `P_n(x)` over `ℝ`. -/
noncomputable def legendrePoly : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | n + 2 =>
    ((2 * (n : ℝ) + 3) / ((n : ℝ) + 2)) • (Polynomial.X * legendrePoly (n + 1)) -
      (((n : ℝ) + 1) / ((n : ℝ) + 2)) • legendrePoly n

/-- `a(n) = 2^(3n/2 - 1) * P_n^1(2^(-1/2))` (up to overall sign convention on `P_n^1`). -/
noncomputable def a (n : ℕ) : ℝ :=
  -(2 : ℝ) ^ ((3 * (n : ℝ)) / 2 - 1) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) *
    (Polynomial.derivative (legendrePoly n)).eval ((2 : ℝ) ^ (-(1 / 2 : ℝ)))

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (-(n : ℝ) + 1) * a n + 2 * (2 * (n : ℝ) - 1) * a (n - 1) - 8 * (n : ℝ) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a025163
