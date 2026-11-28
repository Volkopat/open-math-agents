import Mathlib

/-!
# A243022: Mathar's recurrence

Source: https://oeis.org/A243022
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A243022 (offset 0): expansion of -(2*x)/(1-sqrt(1-(2*(1-sqrt(1-4*x^2)))/x));
data -1, 1, 2, 2, 7, 18, 61, 198, 694, 2446, 8873, 32556, ...

Conjecture (R. J. Mathar, Jul 15 2017): D-finite with recurrence
+2*n*(n-1)*(2*n-3)*(5*n-12)*a(n) -(n-1)*(85*n^3-459*n^2+776*n-400)*a(n-1)
+4*(-40*n^4+396*n^3-1455*n^2+2324*n-1360)*a(n-2) +4*(n-4)*(170*n^3-1258*n^2+3003*n-2185)*a(n-3)
+16*(n-4)*(n-5)*(20*n^2-118*n+143)*a(n-4) -272*(n-4)*(n-5)*(n-6)*(5*n-7)*a(n-5) = 0.

Formalization: T is the formal power series over ℚ with T^2 = 1-4*x^2 and constant term 1; U is the formal power
series with x*U^2 = x - 2*(1-T) and constant term 1, that is U = sqrt(1 - 2*(1 - sqrt(1-4x^2))/x) (the
constant terms select the branches of the square roots); and G is determined by G*(1 - U) = -2*x (its
constant term is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (3640)*(18) + (-10520)*(7) + (-6460)*(2) + (10520)*(2) + (0)*(1) + (0)*(-1) = 0.
-/

namespace OMA.S_oeis_a243022

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A243022, for n ≥ 5. -/
theorem main : ∀ T U G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X ^ 2 →
    coeff 0 T = 1 →
    X * U ^ 2 = X - 2 * (1 - T) →
    coeff 0 U = 1 →
    G * (1 - U) = -(2 * X) →
    coeff 0 G = -1 →
    ∀ n : ℕ, 5 ≤ n →
      (-72 * (n : ℚ) + 150 * (n : ℚ) ^ 2 - 98 * (n : ℚ) ^ 3 + 20 * (n : ℚ) ^ 4) * coeff n G + (-400 + 1176 * (n : ℚ) - 1235 * (n : ℚ) ^ 2 + 544 * (n : ℚ) ^ 3 - 85 * (n : ℚ) ^ 4) * coeff (n - 1) G +
        (-5440 + 9296 * (n : ℚ) - 5820 * (n : ℚ) ^ 2 + 1584 * (n : ℚ) ^ 3 - 160 * (n : ℚ) ^ 4) * coeff (n - 2) G + (34960 - 56788 * (n : ℚ) + 32140 * (n : ℚ) ^ 2 - 7752 * (n : ℚ) ^ 3 + 680 * (n : ℚ) ^ 4) * coeff (n - 3) G +
        (45760 - 58352 * (n : ℚ) + 25680 * (n : ℚ) ^ 2 - 4768 * (n : ℚ) ^ 3 + 320 * (n : ℚ) ^ 4) * coeff (n - 4) G + (-228480 + 304096 * (n : ℚ) - 129200 * (n : ℚ) ^ 2 + 22304 * (n : ℚ) ^ 3 - 1360 * (n : ℚ) ^ 4) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a243022
