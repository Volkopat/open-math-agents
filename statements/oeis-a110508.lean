import Mathlib

/-!
# A110508: Mathar's recurrence

Source: https://oeis.org/A110508
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A110508 (offset 0): expansion of 1/(1-(x+x^2)c(2x)), c(x) the g.f. of A000108;
data 1, 1, 4, 17, 87, 490, 2945, 18517, 120340, 802005, 5451651, 37652546, ...

Conjecture (R. J. Mathar, Nov 15 2011):
n*(3*n-7)*a(n) -4*(3*n-4)*(2*n-5)*a(n-1) +2*n*(3*n-7) +(-45*n^2+177*n-160)*a(n-3)
-4*(3*n-4)*(2*n-5)*a(n-4) = 0
(as printed in the entry, the third term 2*n*(3*n-7) carries no a(n-2); it is read here as
2*n*(3*n-7)*a(n-2), and with this reading the recurrence holds on the data).

Formalization: S is the formal power series over ℚ with S^2 = 1-8*x and constant term 1, that is S = sqrt(1-8x)
(the constant term selects the branch of the square root); c is the series c(2x), with c(y) the Catalan
g.f., determined by 4*x*c = 1 - S; and the g.f. G = 1/(1-(x+x^2)*c(2x)) is determined by
G*(1 - (x+x^2)*c) = 1;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (20)*(87) + (-96)*(17) + (40)*(4) + (-172)*(1) + (-96)*(1) = 0.
-/

namespace OMA.S_oeis_a110508

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A110508, for n ≥ 4. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 8 * X →
    coeff 0 S = 1 →
    4 * X * c = 1 - S →
    G * (1 - (X + X ^ 2) * c) = 1 →
    ∀ n : ℕ, 4 ≤ n →
      (-7 * (n : ℚ) + 3 * (n : ℚ) ^ 2) * coeff n G + (-80 + 92 * (n : ℚ) - 24 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-14 * (n : ℚ) + 6 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-160 + 177 * (n : ℚ) - 45 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-80 + 92 * (n : ℚ) - 24 * (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a110508
