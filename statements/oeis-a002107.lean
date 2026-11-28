import Mathlib

/-!
# OEIS A002107: closed forms for two summatory constants of `∏ (1 - x^k)^2`

Source: https://oeis.org/A002107
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the coefficient of `xⁿ` in `∏_{k ≥ 1} (1 - x^k)^2`. The entry records
`∑_{k=1}^{n} |a(k)| ~ C n / √(log n)` and `∑_{k=1}^{n} a(k)² ~ D n`. Conjecture (Kotesovec, 2026):
`C = √(8 π log(2 + √3) / 3)` and `D = log(7 + 4 √3)`.

Conventions:
* The coefficient of `xⁿ` only involves the factors with `k ≤ n`, so `a n` is the coefficient
  of `xⁿ` in the finite product `∏_{k=1}^{n} (1 - x^k)^2`.
* `main` states both asymptotics with the conjectured constants (`~` is
  `Asymptotics.IsEquivalent` as `n → ∞`).
-/

namespace OMA.S_oeis_a002107

open Polynomial Filter Asymptotics

/-- Coefficient of `xⁿ` in `∏_{k ≥ 1} (1 - x^k)^2`. -/
noncomputable def a (n : ℕ) : ℤ :=
  (∏ k ∈ Finset.range n, (1 - X ^ (k + 1) : ℤ[X]) ^ 2).coeff n

/-- The two asymptotics with Kotesovec's closed-form constants. -/
theorem main :
    IsEquivalent atTop (fun n : ℕ => ((∑ k ∈ Finset.Icc 1 n, |a k| : ℤ) : ℝ))
      (fun n => Real.sqrt (8 * Real.pi * Real.log (2 + Real.sqrt 3) / 3) * n /
        Real.sqrt (Real.log n)) ∧
    IsEquivalent atTop (fun n : ℕ => ((∑ k ∈ Finset.Icc 1 n, a k ^ 2 : ℤ) : ℝ))
      (fun n => Real.log (7 + 4 * Real.sqrt 3) * n) := by
  sorry

end OMA.S_oeis_a002107
