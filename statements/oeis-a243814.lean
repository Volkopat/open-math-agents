import Mathlib

/-!
# A243814: Mathar's recurrence

Source: https://oeis.org/A243814
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A243814 (offset 0): expansion of -(x*(1-sqrt((2*(1-sqrt(4*x^2+1)))/x+1)))/(1-sqrt(4*x^2+1)) - 1;
data 0, 1, 2, 4, 10, 29, 86, 259, 806, 2573, 8332, 27301, ...

Conjecture (R. J. Mathar, Jan 25 2020): D-finite with recurrence
2*n*(n+1)*(2*n-1)*a(n) -n*(47*n^2-127*n+86)*a(n-1) +4*(38*n^3-186*n^2+291*n-145)*a(n-2)
+4*(-94*n^3+724*n^2-1887*n+1650)*a(n-3) +16*(n-4)*(64*n^2-382*n+595)*a(n-4)
-16*(n-5)*(47*n-174)*(n-4)*a(n-5) +1920*(n-5)*(n-6)*(n-4)*a(n-6) = 0.

Formalization: T is the formal power series over ℚ with T^2 = 1+4*x^2 and constant term 1; U is the formal power
series with x*U^2 = 2*(1-T) + x and constant term 1, that is U = sqrt(2*(1 - sqrt(4x^2+1))/x + 1) (the
constant terms select the branches of the square roots); and G is determined by
G*(1-T) = -x*(1-U) - (1-T), which is the stated expression multiplied by 1-T (its constant term is
recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (924)*(86) + (-6096)*(29) + (12452)*(10) + (-15648)*(4) + (19424)*(2) + (-3456)*(1) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a243814

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A243814, for n ≥ 6. -/
theorem main : ∀ T U G : ℚ⟦X⟧, T ^ 2 = 1 + 4 * X ^ 2 →
    coeff 0 T = 1 →
    X * U ^ 2 = 2 * (1 - T) + X →
    coeff 0 U = 1 →
    G * (1 - T) = -(X * (1 - U)) - (1 - T) →
    coeff 0 G = 0 →
    ∀ n : ℕ, 6 ≤ n →
      (-2 * (n : ℚ) + 2 * (n : ℚ) ^ 2 + 4 * (n : ℚ) ^ 3) * coeff n G + (-86 * (n : ℚ) + 127 * (n : ℚ) ^ 2 - 47 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-580 + 1164 * (n : ℚ) - 744 * (n : ℚ) ^ 2 + 152 * (n : ℚ) ^ 3) * coeff (n - 2) G + (6600 - 7548 * (n : ℚ) + 2896 * (n : ℚ) ^ 2 - 376 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (-38080 + 33968 * (n : ℚ) - 10208 * (n : ℚ) ^ 2 + 1024 * (n : ℚ) ^ 3) * coeff (n - 4) G + (55680 - 40096 * (n : ℚ) + 9552 * (n : ℚ) ^ 2 - 752 * (n : ℚ) ^ 3) * coeff (n - 5) G +
        (-230400 + 142080 * (n : ℚ) - 28800 * (n : ℚ) ^ 2 + 1920 * (n : ℚ) ^ 3) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a243814
