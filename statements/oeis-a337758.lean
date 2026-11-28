import Mathlib

/-!
# OEIS A337758: Parity and residue two modulo four

Paul D. Hanna defines an integer series with constant term zero by the
coefficient condition below. The two conjectures identify the indices of
odd coefficients and the indices of coefficients congruent to two modulo
four. The OEIS sequence starts at index one.

Source: https://oeis.org/A337758 (OEIS Foundation, CC BY-SA 4.0).
Credit: @RiverMint78
-/

namespace OMA.S_oeis_a337758

open PowerSeries

/-- The defining coefficient condition for the generating function of A337758. -/
def IsGeneratingSeries (A : PowerSeries ℤ) : Prop :=
  constantCoeff A = 0 ∧ ∀ n : ℕ, 0 < n →
    coeff n ((1 + (n : PowerSeries ℤ) * X + (n : PowerSeries ℤ) * X ^ 2 - A) ^
      (n + 1)) = 0

theorem main : ∀ A : PowerSeries ℤ, IsGeneratingSeries A → ∀ n : ℕ, 0 < n →
    (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k) ∧
    (coeff n A ≡ 2 [ZMOD 4] ↔
      ∃ i j : ℕ, i < j ∧ n = 2 * (2 ^ i + 2 ^ j)) := by
  sorry

end OMA.S_oeis_a337758
