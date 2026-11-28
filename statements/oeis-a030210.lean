import Mathlib

/-!
# A030210: Ramanujan-Petersson bound for (eta(q) * eta(q^5))^4

Source: https://oeis.org/A030210
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

## Problem Statement
Let `a(n)` be the coefficient of `q^n` in the expansion of
`(η(q) * η(q^5))^4 = q * ∏_{k ≥ 1} (1 - q^k)^4 * (1 - q^(5k))^4`.

Conjecture: For every prime `p`, `|a(p)| < 2 * p^(3/2)` (equivalently, `a(p)^2 < 4 * p^3`).
-/

namespace OMA.S_oeis_a030210

/-- The `n`-th coefficient `a(n)` of `q * ∏_{k ≥ 1} (1 - q^k)^4 * (1 - q^(5k))^4`. -/
noncomputable def etaCoeff (n : ℕ) : ℤ :=
  (Polynomial.X *
    ∏ k ∈ Finset.Icc 1 n, (1 - Polynomial.X ^ k) ^ 4 * (1 - Polynomial.X ^ (5 * k)) ^ 4).coeff n

theorem main :
    ∀ p : ℕ, Nat.Prime p → (etaCoeff p) ^ 2 < 4 * (p : ℤ) ^ 3 := by
  sorry

end OMA.S_oeis_a030210
