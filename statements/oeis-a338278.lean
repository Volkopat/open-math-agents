import Mathlib

/-!
# The coefficients of the generating function for OEIS A338278

Source: https://oeis.org/A338278
Credit: @yuka30240

Every coefficient of positive degree is congruent to 3 modulo 9.
-/

namespace OMA.S_oeis_a338278

/-- The numerator of the summand with denominator `3^(m+1)` in the generating function. -/
noncomputable def numerator (m : ℕ) : Polynomial ℕ :=
  ∏ k ∈ Finset.Icc 1 m, (1 + (1 + Polynomial.X) ^ k)

/-- Sum the degree-`n` coefficients of the summands to obtain the coefficient of the series. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ a : ℕ, HasSum (fun m : ℕ => ((numerator m).coeff n : ℝ) / 3 ^ (m + 1)) (a : ℝ) ∧
      a ≡ 3 [MOD 9] := by
  sorry

end OMA.S_oeis_a338278

