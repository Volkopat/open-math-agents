import Mathlib

/-!
# A187252: Mathar's recurrence, corrected to n ≥ 5

Source: https://oeis.org/A187252
Credit: @ivillar

Status: false as stated at n = 4 (the left side is 2 at n = 4 on the OEIS data, since a(4) = 2 and
a(0) = a(1) = a(2) = a(3) = 0); `main` is the corrected recurrence (n ≥ 5), which is proved. The conjecture
is due to R. J. Mathar (Jul 22 2022); the entry records it as a conjecture and notes no proof or verification.

A187252 (offset 0): number of cycles with at least 3 alternating runs in all permutations of [n] (it is
assumed that the smallest element of a cycle is in the first position);
data 0, 0, 0, 0, 2, 26, 260, 2508, 25040, 265552, 3018144, 36827872, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
a(n) +(-2*n-3)*a(n-1) +(n+7)*(n-1)*a(n-2) +4*(-n^2+2*n+1)*a(n-3) +4*(n-3)^2*a(n-4) = 0.

Formalization: the entry gives the e.g.f. g(z) = -(1/4)*(2*z - 1 + exp(2*z) + 4*log(1-z)) / (1-z), and this
closed form is used as the definition here. exp(2*z) is the formal power series `rescale 2 (exp ℚ)` (with
coefficients 2^n/n!), and log(1-z) is the formal power series -Sum_{n>=1} z^n/n (`logOneSub` below). G is the
formal power series over ℚ determined by 4*(1-x)*G = -(2*x - 1 + exp(2*x) + 4*log(1-x)), the stated
expression multiplied by 4*(1-z), and a(n) = n! [x^n] G. `main` is the corrected recurrence (n ≥ 5): on the
data the left side of the recurrence as stated is 2 at n = 4, and it vanishes from n = 5 on, for example at
n = 5: (1)*(26) + (-13)*(2) + (48)*(0) + (-56)*(0) + (16)*(0) = 0, and at n = 6:
(1)*(260) + (-15)*(26) + (65)*(2) + (-92)*(0) + (36)*(0) = 0.
-/

namespace OMA.S_oeis_a187252

open PowerSeries

/-- The formal power series log(1 - x) = -Sum_{n>=1} x^n/n. -/
noncomputable def logOneSub : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then 0 else -(1 / (n : ℚ)))

/-- The sequence with exponential generating function G: a(n) = n! [x^n] G. -/
noncomputable def a (G : ℚ⟦X⟧) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n G

/-- The corrected recurrence (n ≥ 5): Mathar's recurrence, which fails at n = 4. -/
theorem main : ∀ G : ℚ⟦X⟧,
    (4 : ℚ) • (G * (1 - X)) = -((2 : ℚ) • X - 1 + rescale (2 : ℚ) (exp ℚ) + (4 : ℚ) • logOneSub) →
    ∀ n : ℕ, 5 ≤ n →
      a G n + (-2 * (n : ℚ) - 3) * a G (n - 1) + ((n : ℚ) + 7) * ((n : ℚ) - 1) * a G (n - 2) +
        4 * (-(n : ℚ) ^ 2 + 2 * (n : ℚ) + 1) * a G (n - 3) + 4 * ((n : ℚ) - 3) ^ 2 * a G (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a187252
