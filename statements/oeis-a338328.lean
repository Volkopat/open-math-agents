import Mathlib

/-!
# Residues of the coefficients of the generating function for A338328

Source: https://oeis.org/A338328
Credit: @yuka30240

The sequence starts at index 1, so its ordinary generating function has constant term zero.
-/

namespace OMA.S_oeis_a338328

open PowerSeries

/-- The two conjectures of A338328 on odd coefficients and coefficients congruent to 2 modulo 4. -/
theorem main :
    ∀ A : PowerSeries ℤ, coeff 0 A = 0 →
    (∀ m : ℕ, 0 < m →
      coeff m ((1 + (m : PowerSeries ℤ) * X - A) ^ (2 * m - 1)) = 0) →
    ∀ n : ℕ, 0 < n →
    (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k) ∧
    (coeff n A ≡ 2 [ZMOD 4] ↔ ∃ i j : ℕ, i < j ∧ n = 2 * (2 ^ i + 2 ^ j)) := by
  sorry

end OMA.S_oeis_a338328

