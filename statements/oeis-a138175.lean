import Mathlib

/-!
# A138175: Mathar's recurrence (false as stated)

Source: https://oeis.org/A138175
Credit: @ivillar

Status: false as stated (counterexample n = 3: on the OEIS data a(0..3) = 1, 2, 4, 10 the left side
is -711504). The recurrence as printed in the entry fails at every n from 3 to 12; `main` is the
recurrence exactly as stated and is kept as the target of a disproof. (The data do satisfy the
recurrence with the third coefficient 9*(-351*n^3+2196*n^2-4325*n+2680), so the entry probably has
two sign typos; that modified recurrence is not what is stated here.)

A138175 (offset 0): row sums of the Riordan array (1/(1+x),x(1+2x)/(1+x)^3)^(-1);
data 1, 2, 4, 10, 24, 62, 156, 408, 1048, 2758, 7164, 18922, ...

Conjecture (R. J. Mathar, Oct 25 2012):
12*n*(n-1)*(39*n-88)*a(n) -8*(n-1)*(156*n^2-352*n+27)*a(n-1)
+9*(-351*n^3-2196*n^2-4325*n+2680)*a(n-2) +24*(39*n-49)*(3*n-7)*(3*n-8)*a(n-3) = 0.

Formalization: the entry gives the g.f. as 1/(1-2v), where v is the series reversion of x*(1-x^2), and
this is used as the definition here: T (the v of the entry) is the formal power series over ℚ with
zero constant term and T - T^3 = x (the constant term selects the reversion among the three series
solutions), and G is determined by G*(1 - 2*T) = 1; a(n) = [x^n] G. The recurrence involves a(n-3), so
it is stated for n ≥ 3. At n = 3 the left side is
12*3*2*29*10 - 8*2*375*4 + 9*(-39536)*2 + 24*68*2*1*1 = 20880 - 24000 - 711648 + 3264 = -711504.
-/

namespace OMA.S_oeis_a138175

open PowerSeries

/-- Mathar's recurrence for the coefficients of the g.f. of A138175, as stated in the entry, for
n ≥ 3. It is false: it fails at n = 3. -/
theorem main : ∀ T G : ℚ⟦X⟧, T - T ^ 3 = X →
    coeff 0 T = 0 →
    G * (1 - 2 * T) = 1 →
    ∀ n : ℕ, 3 ≤ n →
      12 * (n : ℚ) * ((n : ℚ) - 1) * (39 * (n : ℚ) - 88) * coeff n G -
        8 * ((n : ℚ) - 1) * (156 * (n : ℚ) ^ 2 - 352 * (n : ℚ) + 27) * coeff (n - 1) G +
        9 * (-351 * (n : ℚ) ^ 3 - 2196 * (n : ℚ) ^ 2 - 4325 * (n : ℚ) + 2680) * coeff (n - 2) G +
        24 * (39 * (n : ℚ) - 49) * (3 * (n : ℚ) - 7) * (3 * (n : ℚ) - 8) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a138175
