import Mathlib

/-!
# A027642: a continued fraction for the Bernoulli exponential generating function

Source: https://oeis.org/A027642
Credit: @Bondyboy2001

Sergei N. Gladkovskii conjectured
`x/(exp(x)-1) = T(0)/2 - x`, where
`T(k) = 8*k+2 + x/(1 - x/(8*k+6 + x/(1 - x/T(k+1))))` as a continued fraction.

The continued fraction is interpreted in formal power series. Its tails are the unique family
`Q` with the stated constant terms satisfying the denominator-cleared recurrence. Clearing the
denominators is reversible: their constant terms are nonzero. The left side is the exponential
generating series of the Bernoulli numbers, `∑ B_n x^n/n!`.
-/

namespace OMA.S_oeis_a027642

open PowerSeries

/-- The exponential generating series `x/(exp(x)-1) = ∑ B_n x^n/n!`. -/
noncomputable def bernoulliEgf : PowerSeries ℚ :=
  mk fun n => (bernoulli n : ℚ) / (n.factorial : ℚ)

/-- Denominator-cleared form of the two-level continued-fraction recurrence. -/
def TailFamily (Q : ℕ → ℚ⟦X⟧) : Prop :=
  ∀ k : ℕ,
    constantCoeff (Q k) = (8 * (k : ℚ) + 2) ∧
      let A : ℚ⟦X⟧ := C (8 * (k : ℚ) + 2)
      let B : ℚ⟦X⟧ := C (8 * (k : ℚ) + 6)
      (Q k - A) * (B * Q (k + 1) - B * X + X ^ 2) =
        X * (B * Q (k + 1) - B * X + X * Q (k + 1))

/-- Gladkovskii's continued-fraction conjecture. -/
theorem main :
    ∃ Q : ℕ → ℚ⟦X⟧, TailFamily Q ∧ (∀ R : ℕ → ℚ⟦X⟧, TailFamily R → R = Q) ∧
      bernoulliEgf = (1 / 2 : ℚ) • Q 0 - X := by
  sorry

end OMA.S_oeis_a027642
