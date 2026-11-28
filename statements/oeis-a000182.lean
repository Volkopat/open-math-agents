import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# OEIS A000182: Tangent numbers

Source: https://oeis.org/A000182
Conjectures: Peter Bala (December 24, 2021 and December 15, 2025)
Credit: @kylerrusin
-/

namespace OMA.S_oeis_a000182

/-- The derivative polynomials for tangent, from `tan' = 1 + tan²`. -/
noncomputable def tangentPolynomial : ℕ → Polynomial ℤ
  | 0 => Polynomial.X
  | m + 1 => (1 + Polynomial.X ^ 2) * (tangentPolynomial m).derivative

/-- The coefficient of `x^(2*n-1)/(2*n-1)!` in tangent, with OEIS offset 1. -/
noncomputable def tangentNumber (n : ℕ) : ℤ := (tangentPolynomial (2 * n - 1)).eval 0

/-- Moduli are positive, as in the usual domain of Euler's totient function.
A negative nonzero modulus gives the same condition with its absolute value. -/
def Periodicity : Prop :=
  ∀ q : ℕ, 0 < q → ∃ period : ℕ, 0 < period ∧ period ∣ q.totient ∧
    ∃ cutoff : ℕ, 0 < cutoff ∧ ∀ n ≥ cutoff,
      Int.ModEq (q : ℤ) (tangentNumber (n + period)) (tangentNumber n)

/-- The two listed exceptions are failures of the unshifted congruence. -/
def UnshiftedGauss : Prop :=
  ∀ p n k : ℕ, p.Prime → 0 < n → 0 < k →
    (Int.ModEq ((p : ℤ) ^ k) (tangentNumber (n * p ^ k))
      (tangentNumber (n * p ^ (k - 1))) ↔ ¬ (p = 2 ∧ n = 1 ∧ (k = 1 ∨ k = 2)))

def ShiftedGauss : Prop :=
  ∀ i p n k : ℕ, 0 < i → p.Prime → 0 < n → 0 < k →
    Int.ModEq ((p : ℤ) ^ k) (tangentNumber (n * p ^ k + i))
      (tangentNumber (n * p ^ (k - 1) + i))

noncomputable def shiftedExponential (i : ℕ) : PowerSeries ℚ :=
  (PowerSeries.exp ℚ).subst
    (PowerSeries.mk fun n : ℕ => (tangentNumber (n + i) : ℚ) / (n : ℚ))

/-- Finite tails of Bala's fraction. Starting at index zero, the denominators
alternate `1 + X` and `1`, and the numerator multipliers occur in pairs
`(2*j+3)^2`, `(2*j+3)^2-1` for `j = 0, 1, …`. -/
noncomputable def fractionTail : ℕ → ℕ → PowerSeries ℚ
  | 0, j => 1 + if Even j then PowerSeries.X else 0
  | depth + 1, j =>
      (1 + if Even j then PowerSeries.X else 0) -
        PowerSeries.C (((2 * (j / 2) + 3 : ℕ) : ℚ) ^ 2 - if Even j then 0 else 1) *
          PowerSeries.X * (fractionTail depth (j + 1))⁻¹

noncomputable def fractionApproximation (depth : ℕ) : PowerSeries ℚ :=
  PowerSeries.X * (1 + 2 * PowerSeries.X * (fractionTail depth 0)⁻¹)

/-- Equality with the infinite fraction means stabilization in each degree. -/
def ContinuedFraction : Prop :=
  ∀ n : ℕ, ∃ cutoff : ℕ, ∀ depth ≥ cutoff,
    PowerSeries.coeff n (fractionApproximation depth) = (tangentNumber n : ℚ)

theorem main :
    Periodicity ∧ UnshiftedGauss ∧ ShiftedGauss ∧
      (ShiftedGauss → ∀ i : ℕ, 0 < i → ∀ n : ℕ, ∃ z : ℤ,
        PowerSeries.coeff n (shiftedExponential i) = (z : ℚ)) ∧
      ContinuedFraction := by
  sorry

end OMA.S_oeis_a000182
