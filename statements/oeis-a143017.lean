import Mathlib

/-!
# A143017: Mathar's recurrence

Source: https://oeis.org/A143017
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A143017 (offset 1): number of {2-1-3, 2'^e-31}-avoiding permutations of size n (see definition in the Elizalde paper);
data 1, 2, 4, 9, 22, 56, 147, 396, 1088, 3036, 8582, 24524, ...

Conjecture (R. J. Mathar, Mar 14 2014):
-8*n*(n+1)*a(n) + 4*n*(2*n+5)*a(n-1) + 4*n*(n+7)*a(n-2) + 2*(70*n^2-395*n+564)*a(n-3) +
2*(25*n^2-143*n+222)*a(n-4) + 4*(49*n-228)*(n-5)*a(n-5) - 45*(n-5)*(n-6)*a(n-6) = 0.

Formalization: G is the formal power series over ℚ with zero constant term (the sequence has offset 1) and
x*G^3 + (4x-2)*G^2 + (4x-1)*G + x = 0, the equation for the g.f. given in the entry (the constant term
selects the series among the solutions of the equation);
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (-336)*(56) + (408)*(22) + (312)*(9) + (1428)*(4) + (528)*(2) + (264)*(1) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a143017

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A143017, for n ≥ 6. -/
theorem main : ∀ G : ℚ⟦X⟧, coeff 0 G = 0 →
    X * G ^ 3 + (4 * X - 2) * G ^ 2 + (4 * X - 1) * G + X = 0 →
    ∀ n : ℕ, 6 ≤ n →
      (-8 * (n : ℚ) - 8 * (n : ℚ) ^ 2) * coeff n G + (20 * (n : ℚ) + 8 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (28 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff (n - 2) G + (1128 - 790 * (n : ℚ) + 140 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (444 - 286 * (n : ℚ) + 50 * (n : ℚ) ^ 2) * coeff (n - 4) G + (4560 - 1892 * (n : ℚ) + 196 * (n : ℚ) ^ 2) * coeff (n - 5) G +
        (-1350 + 495 * (n : ℚ) - 45 * (n : ℚ) ^ 2) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a143017
