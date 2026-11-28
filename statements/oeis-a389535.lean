import Mathlib

/-!
# A389535: G.f. A(x) satisfies A( x*A(x)^4 + x*A(x)^5 ) = A(x)^5.

Source: https://oeis.org/A389535

Conjecture (7) in the entry: `A(x)^5 ≡ A(x^5) (mod 5)`, i.e. coefficientwise
`[x^n] A(x)^5 ≡ [x^(n/5)] A(x)` when `5 ∣ n` and `[x^n] A(x)^5 ≡ 0` otherwise (mod 5).

Formalization: `A ∈ ℤ⟦x⟧` with `A(0) = 0`, `A'(0) = 1` and the functional equation, written with
`PowerSeries.subst` for composition (the inner series `x*A^4 + x*A^5` has zero constant term).
-/

namespace OMA.S_oeis_a389535

/-- The defining conditions of A389535. -/
def IsA389535 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
  PowerSeries.coeff 1 A = 1 ∧
  PowerSeries.subst (PowerSeries.X * A ^ 4 + PowerSeries.X * A ^ 5) A = A ^ 5

/-- Conjecture (7) of A389535: `A(x)^5 ≡ A(x^5) (mod 5)`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA389535 A →
      ∀ n : ℕ, PowerSeries.coeff n (A ^ 5) ≡
        (if 5 ∣ n then PowerSeries.coeff (n / 5) A else 0) [ZMOD 5] := by
  sorry

end OMA.S_oeis_a389535
