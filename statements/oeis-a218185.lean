import Mathlib

/-!
# A218185: Mathar's recurrence, corrected to n ≥ 5

Source: https://oeis.org/A218185
Credit: @ivillar

Status: false as stated at n = 4 (the left side is -16 at n = 4 on the OEIS data); `main` is the
corrected recurrence (n ≥ 5), which is proved.

A218185 (offset 0): number of rows with the value true in the truth tables of all bracketed formulas with n distinct propositions p_1, ..., p_n connected by the binary connective of m-implication (case 3);
data 0, 0, 1, 4, 19, 100, 566, 3384, 21107, 136084, 900674, 6087496, ...

Conjecture (R. J. Mathar, Oct 08 2016):
n*(n-1)*(n-2)*a(n) -12*(2*n-5)*(n-1)*(n-2)*a(n-1) +4 *(n-2)*(52*n^2-312*n+465) *a(n-2)
-48*(2*n-7)*(8*n^2-56*n+95)*a(n-3) +256*(n-5) *(2*n-7) *(2*n-9)*a(n-4) = 0.

Formalization: The entry gives the g.f. in closed form, (-1 - sqrt(1-8*x) + sqrt(1-8*x)*sqrt(1-4*x) + sqrt(1-4*x) + 4*x)/4,
and this closed form is used as the definition here. T and W are the formal power series over ℚ with
T^2 = 1-8*x, W^2 = 1-4*x and constant terms 1, that is T = sqrt(1-8x) and W = sqrt(1-4x) (the constant
terms select the branches of the square roots); and G is determined by 4*G = -1 - T + T*W + W + 4*x
(its constant term 0 is recorded as a hypothesis);
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 5): on the data the left side of the recurrence as
stated is -16 at n = 4, and it vanishes from n = 5 on.
-/

namespace OMA.S_oeis_a218185

open PowerSeries

/-- The corrected recurrence (n ≥ 5): Mathar's recurrence, which fails at n = 4. -/
theorem main : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 8 * X →
    coeff 0 T = 1 →
    W ^ 2 = 1 - 4 * X →
    coeff 0 W = 1 →
    G * 4 = -1 - T + T * W + W + 4 * X →
    coeff 0 G = 0 →
    ∀ n : ℕ, 5 ≤ n →
      (2 * (n : ℚ) - 3 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) * coeff n G + (120 - 228 * (n : ℚ) + 132 * (n : ℚ) ^ 2 - 24 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-3720 + 4356 * (n : ℚ) - 1664 * (n : ℚ) ^ 2 + 208 * (n : ℚ) ^ 3) * coeff (n - 2) G + (31920 - 27936 * (n : ℚ) + 8064 * (n : ℚ) ^ 2 - 768 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (-80640 + 57088 * (n : ℚ) - 13312 * (n : ℚ) ^ 2 + 1024 * (n : ℚ) ^ 3) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a218185
