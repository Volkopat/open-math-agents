import Mathlib

/-!
# Van Hoeij's congruence for A000159

Source: https://oeis.org/A000159
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = T(n, n-3)` for `n ≥ 3`, where `T` is the triangle A058087 of coefficients of the ménage
hit polynomials. Conjecture (Mark van Hoeij, 2019): `a(n) + 2 a(n+p) + a(n+2p)` is divisible by
`p` for every prime `p ≠ 3`. (Mathar's recurrence in the entry is not stated here.)

Conventions:
* Kaplansky–Riordan: `U_n(t) = Σ_{k=0..n} (2n/(2n-k)) binom(2n-k, k) (n-k)! (t-1)^k`, and row
  `n` of A058087 lists the coefficients of `U_n` by descending powers, so `T(n, k)` is the
  coefficient of `t^(n-k)` and `a(n)` is the coefficient of `t³` in `U_n`.
* `U_n` is computed in `ℚ[t]`; its coefficients are integers, and divisibility is stated as
  `a(n) + 2a(n+p) + a(n+2p) = p · m` for an integer `m`. The index range is `n ≥ 3`.
-/

namespace OMA.S_oeis_a000159

open Polynomial

/-- The ménage hit polynomial `U_n`. -/
noncomputable def U (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C ((2 * n : ℚ) / (2 * n - k) * (2 * n - k).choose k * (n - k).factorial) * (X - 1) ^ k

/-- `a(n) = A058087(n, n-3)`. -/
noncomputable def a (n : ℕ) : ℚ := (U n).coeff 3

theorem main :
    ∀ p : ℕ, p.Prime → p ≠ 3 → ∀ n : ℕ, 3 ≤ n →
      ∃ m : ℤ, a n + 2 * a (n + p) + a (n + 2 * p) = p * m := by
  sorry

end OMA.S_oeis_a000159
