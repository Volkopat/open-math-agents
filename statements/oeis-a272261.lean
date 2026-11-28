import Mathlib

/-!
# A272261: Mathar's recurrence

Source: https://oeis.org/A272261
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A272261 (offset 0): number of one-to-one functions f from [n] to [2n] where f(x) may not be equal to x or to 2n+1-x;
data 1, 0, 4, 40, 576, 10528, 233920, 6124032, 184656640, 6302821888, 240245858304, 10115537336320, ...

Conjecture (R. J. Mathar, Jan 27 2020): D-finite with recurrence
a(n) + 2*(-2*n+1)*a(n-1) - 4*a(n-2) = 0.

Formalization: the entry gives the e.g.f. exp(-1+sqrt(1-4*x))/sqrt(1-4*x) (Benedict W. J. Irwin, Jul 14 2016), and this
is used as the definition here. S is the formal power series over ℚ with S^2 = 1-4*x and constant term
1, that is S = sqrt(1-4x) (the constant term selects the branch of the square root); S - 1 has zero
constant term, so the composition exp(S - 1) of the exponential series with S - 1 is defined
(`(PowerSeries.exp ℚ).subst (S - 1)`); and the e.g.f. G is determined by G*S = exp(S - 1);
a(n) = n! [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (1)*(4) + (-6)*(0) + (-4)*(1) = 0.
-/

namespace OMA.S_oeis_a272261

open PowerSeries

/-- The sequence with exponential generating function G: a(n) = n! [x^n] G. -/
noncomputable def a (G : ℚ⟦X⟧) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n G

/-- Mathar's conjectured recurrence for A272261 (a(n) = n! [x^n] G), for n ≥ 2. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    G * S = (PowerSeries.exp ℚ).subst (S - 1) →
    ∀ n : ℕ, 2 ≤ n →
      (1) * a G n + (2 - 4 * (n : ℚ)) * a G (n - 1) +
        (-4) * a G (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a272261
