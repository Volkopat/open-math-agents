import Mathlib

/-!
# A168506: Mathar's recurrence

Source: https://oeis.org/A168506
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Jul 24 2012); the entry records it as a conjecture and notes no proof or
verification of it.

A168506 (offset 2): number of rooted plane trees of total weight n whose nodes are themselves planted plane trees whose roots are distinguished as either red or blue, the weight of each such node being equal to the size of the corresponding planted tree;
data 2, 2, 8, 18, 64, 188, 656, 2154, 7584, 26276, 93904, 335156, ...

Conjecture (R. J. Mathar, Jul 24 2012):
n*(n-1)*(n-6)*a(n) -2*(6*n-35)*(n-1)*(n-2)*a(n-1) +4*(8*n^3-88*n^2+305*n-330)*a(n-2)
+8*(8*n^3-92*n^2+314*n-305)*a(n-3) -16*(n-5)*(4*n-19)*(4*n-17)*a(n-4) = 0.

Formalization: The entry gives the g.f. (1/2)*(1-sqrt(1-4*x+4*x*sqrt(1-4*x))), and this closed form is used as the
definition here. T is the formal power series over ℚ with T^2 = 1-4*x and constant term 1; W is the
formal power series with W^2 = 1 - 4*x + 4*x*T and constant term 1, that is
W = sqrt(1-4*x+4*x*sqrt(1-4*x)) (the constant terms select the branches of the square roots); and G is
determined by G*2 = 1 - W (its constant term 0 is recorded as a hypothesis);
a(n) = [x^n] G. The sequence has offset 2, and [x^k] G = 0 for k < 2. The recurrence involves a(n-4); with
a(k) read as [x^k] G (so a(k) = 0 below the offset) it holds for n ≥ 5, and `main` is stated
for this range, which contains every n ≥ 6 (where all indices are at least the offset).
It is checked by the data, for example at n = 6:
(0)*(64) + (-40)*(18) + (240)*(8) + (-40)*(2) + (-560)*(2) = 0.
-/

namespace OMA.S_oeis_a168506

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A168506, for n ≥ 5. -/
theorem main : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    W ^ 2 = 1 - 4 * X + 4 * X * T →
    coeff 0 W = 1 →
    G * 2 = 1 - W →
    coeff 0 G = 0 →
    ∀ n : ℕ, 5 ≤ n →
      (6 * (n : ℚ) - 7 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) * coeff n G + (140 - 234 * (n : ℚ) + 106 * (n : ℚ) ^ 2 - 12 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-1320 + 1220 * (n : ℚ) - 352 * (n : ℚ) ^ 2 + 32 * (n : ℚ) ^ 3) * coeff (n - 2) G + (-2440 + 2512 * (n : ℚ) - 736 * (n : ℚ) ^ 2 + 64 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (25840 - 16688 * (n : ℚ) + 3584 * (n : ℚ) ^ 2 - 256 * (n : ℚ) ^ 3) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a168506
