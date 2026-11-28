import Mathlib

/-!
# OEIS A378259

The source uses `A(X) = ∑ n ≥ 1, a(n) X^n / 4^(n−1)`. Set
`B(X) = A(4X)/4`, whose coefficients are the integers `a(n)`.
The source's Möbius formula for `A(X²)/A(X)` gives `scaledRatio B`
after substituting `4X` and dividing by `4`. Multiplying by `B` gives
`A(16X²)/16`, encoded as `scaledSquareSubstitution B`.

Source: https://oeis.org/A378259
Credit: @wtho704
-/

namespace OMA.S_oeis_a378259

open PowerSeries

/-- The source's ratio `A(X²)/A(X)` evaluated at `4X` and divided by `4`. -/
noncomputable def scaledRatio (B : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ d ∈ n.divisors, (4 : ℤ) ^ (n - d) * ArithmeticFunction.moebius (n / d) * coeff d B

/-- The source series `A(16X²)/16`, with coefficient `4^(d−1) * a(d)` at `2d`. -/
noncomputable def scaledSquareSubstitution (B : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    if 0 < n ∧ 2 ∣ n then (4 : ℤ) ^ (n / 2 - 1) * coeff (n / 2) B else 0

/-- Indices that are one more than a power of two. -/
def specialIndex (n : ℕ) : Prop := ∃ k : ℕ, n = 2 ^ k + 1

theorem main : ∀ B : PowerSeries ℤ, constantCoeff B = 0 → coeff 1 B = 1 →
    B * scaledRatio B = scaledSquareSubstitution B → ∀ n : ℕ, 1 < n →
      ((coeff n B ≡ 2 [ZMOD 4]) ↔ specialIndex n) ∧
        (¬ specialIndex n → (4 : ℤ) ∣ coeff n B) := by
  sorry

end OMA.S_oeis_a378259
