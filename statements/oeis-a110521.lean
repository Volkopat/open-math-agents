import Mathlib

/-!
# A110521: Mathar's recurrence

Source: https://oeis.org/A110521
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A110521 (offset 0): expansion of 1/(1 - (x + x^2)c(3x)), c(x) the g.f. of A000108;
data 1, 1, 5, 30, 224, 1871, 16771, 157668, 1533970, 15314626, 156008660, 1615147014, ...

Conjecture (R. J. Mathar, Dec 10 2011):
2*n*a(n) + 2*(16-11n)*a(n-1) + 2*(42-11n)*a(n-2) + (32-21n)*a(n-3) + 5*(20-7n)*a(n-4) +
6*(7-2n)*a(n-5) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-12*x and constant term 1, that is S = sqrt(1-12x)
(the constant term selects the branch of the square root); c is the series c(3x), with c(x) the Catalan
g.f., determined by 6*x*c = 1 - S; and the g.f. G is determined by G*(1 - (x+x^2)*c) = 1;
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (10)*(1871) + (-78)*(224) + (-26)*(30) + (-73)*(5) + (-75)*(1) + (-18)*(1) = 0.
-/

namespace OMA.S_oeis_a110521

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A110521, for n ≥ 5. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 12 * X →
    coeff 0 S = 1 →
    6 * X * c = 1 - S →
    G * (1 - (X + X ^ 2) * c) = 1 →
    ∀ n : ℕ, 5 ≤ n →
      (2 * (n : ℚ)) * coeff n G + (32 - 22 * (n : ℚ)) * coeff (n - 1) G +
        (84 - 22 * (n : ℚ)) * coeff (n - 2) G + (32 - 21 * (n : ℚ)) * coeff (n - 3) G +
        (100 - 35 * (n : ℚ)) * coeff (n - 4) G + (42 - 12 * (n : ℚ)) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a110521
