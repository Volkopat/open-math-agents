import Mathlib

/-!
# A014533: 4th column from the center of (1 + x + x^2)^n

Source: https://oeis.org/A014533
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
Let `a(n)` be the 4th column from the center in the expansion of `(1 + x + x^2)^(n + 3)`,
so `a(1) = 1, a(2) = 5, a(3) = 21, a(4) = 77, ...` (with `a(0) = 0`).
Then for all `n ≥ 2`:
  `-(n + 7) * (n - 1) * a(n) + (n + 3) * (2*n + 5) * a(n - 1) + 3 * (n + 3) * (n + 2) * a(n - 2) = 0`.

Conventions:
- In `(1 + X + X^2)^m`, the center coefficient is at degree `m`, so the 4th column from
  the center is the coefficient of `X^(m + 4)`. With `m = n + 3`, this is `coeff (n + 7)`.
-/

namespace OMA.S_oeis_a014533

noncomputable def aSeq (n : ℕ) : ℤ :=
  ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ) ^ (n + 3)).coeff (n + 7)

theorem main :
    ∀ n : ℕ, n ≥ 2 →
      -((n : ℤ) + 7) * ((n : ℤ) - 1) * aSeq n +
        ((n : ℤ) + 3) * (2 * (n : ℤ) + 5) * aSeq (n - 1) +
        3 * ((n : ℤ) + 3) * ((n : ℤ) + 2) * aSeq (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a014533
