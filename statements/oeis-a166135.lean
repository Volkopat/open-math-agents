import Mathlib

/-!
# A166135: Mathar's recurrence

Source: https://oeis.org/A166135
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A166135 (offset 1): number of possible paths to each node that lies along the edge of a cut 4-nomial tree, that is rooted one unit from the cut;
data 1, 1, 3, 7, 22, 65, 213, 693, 2352, 8034, 28014, 98505, ...

Conjecture (R. J. Mathar, Oct 08 2016):
2*n*(2*n+1)*a(n) + (17*n^2-53*n+24)*a(n-1) + 6*(-13*n^2+43*n-36)*a(n-2) - 108*(2*n-5)*(n-3)*a(n-3)
= 0.

Formalization: The entry gives the g.f. (sqrt((2 - 2*sqrt(1-4*x) - 3*x)/x) - 1)/2 (Benedict W. J. Irwin, Sep 24 2016),
and this closed form is used as the definition here. T is the formal power series over ℚ with
T^2 = 1-4*x and constant term 1; U is the formal power series with x*U^2 = 2 - 2*T - 3*x and constant
term 1, that is U = sqrt((2 - 2*sqrt(1-4x) - 3x)/x) (the constant terms select the branches of the
square roots); and G is determined by G*2 = U - 1 (its constant term is recorded as a hypothesis);
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (42)*(3) + (18)*(1) + (-144)*(1) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a166135

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A166135, for n ≥ 3. -/
theorem main : ∀ T U G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    X * U ^ 2 = 2 - 2 * T - 3 * X →
    coeff 0 U = 1 →
    G * 2 = U - 1 →
    coeff 0 G = 0 →
    ∀ n : ℕ, 3 ≤ n →
      (2 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff n G + (24 - 53 * (n : ℚ) + 17 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-216 + 258 * (n : ℚ) - 78 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-1620 + 1188 * (n : ℚ) - 216 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a166135
