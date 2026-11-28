import Mathlib

/-!
# Strict convexity of Bessel integrals

Source: https://mathoverflow.net/questions/162821
The integer-order series for the Bessel function of the first kind is
DLMF 10.2.2, https://dlmf.nist.gov/10.2.E2.
Credit: @wtho704
-/

open MeasureTheory

namespace OMA.S_mo_162821

/-- The Bessel function of the first kind of nonnegative integer order. -/
noncomputable def besselJ (n : ℕ) (r : ℝ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ k * (r / 2) ^ (n + 2 * k) /
    ((k.factorial : ℝ) * ((n + k).factorial : ℝ))

noncomputable def beta (n : ℕ) : ℝ :=
  ∫ r in Set.Ioi (0 : ℝ), besselJ n r ^ 2 * besselJ 0 r ^ 2

theorem main : ∀ n : ℕ, 1 ≤ n →
    beta n < (beta (n - 1) + beta (n + 1)) / 2 := by
  sorry

end OMA.S_mo_162821
