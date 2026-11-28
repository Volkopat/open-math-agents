import Mathlib

/-!
# OEIS A389542

The generating function `A` starts with `X` and satisfies
`A(A(X)² − X²) = 4A(X)³`. The conjecture describes its coefficients
modulo `4` in degrees greater than one.

Source: https://oeis.org/A389542
Credit: @wtho704
-/

namespace OMA.S_oeis_a389542

open PowerSeries

/-- Indices that are one more than a power of two. -/
def specialIndex (n : ℕ) : Prop := ∃ k : ℕ, n = 2 ^ k + 1

theorem main : ∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 →
    A.subst (A ^ 2 - X ^ 2) = 4 * A ^ 3 → ∀ n : ℕ, 1 < n →
      ((coeff n A ≡ 2 [ZMOD 4]) ↔ specialIndex n) ∧
        (¬ specialIndex n → (4 : ℤ) ∣ coeff n A) := by
  sorry

end OMA.S_oeis_a389542
