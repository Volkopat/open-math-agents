import Mathlib

/-!
# Parity of the coefficients of OEIS A389540

The ordinary generating function starts with `X` and satisfies
`A(2X - 2A(X)) = 2A(X)^2`. Paul D. Hanna's conjecture specifies
exactly which positive indices have odd coefficients.

Source: https://oeis.org/A389540 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a389540

open PowerSeries

theorem main :
    ∀ A : PowerSeries ℤ, A.constantCoeff = 0 → A.coeff 1 = 1 →
      PowerSeries.subst (2 * X - 2 * A) A = 2 * A ^ 2 →
      ∀ n : ℕ, 1 ≤ n → (Odd (A.coeff n) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a389540
