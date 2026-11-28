import Mathlib

/-!
# Asymptotic growth of the largest coefficient in OEIS A186860

The OEIS data start at `n = 1`. Both generating programs use `n` factors,
of degrees `0` through `n - 1`, producing the maxima `1, 2, 7, 49, 562`.
This fixes the index of the last factor in the displayed product.

Source: https://oeis.org/A186860
Credit: @gdyan2022
-/

namespace OMA.S_oeis_a186860

open Polynomial

/-- Row `n` is the product of the first `n` ascending-coefficient polynomials. -/
noncomputable def row (n : ℕ) : Polynomial ℕ :=
  ∏ j ∈ Finset.range n, ∑ k ∈ Finset.range (j + 1), C (k + 1) * X ^ k

/-- Largest coefficient, taken over the finite support. -/
noncomputable def largestCoeff (n : ℕ) : ℕ := (row n).support.sup (row n).coeff

/-- Vaclav Kotesovec's 2023 asymptotic conjecture. -/
theorem main : Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (largestCoeff n : ℝ))
    (fun n : ℕ => (3 : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt Real.pi *
      (n : ℝ) ^ (2 * (n : ℝ) + 1 / 2) / ((2 : ℝ) ^ (n - 1) * Real.exp (2 * n))) := by
  sorry

end OMA.S_oeis_a186860
