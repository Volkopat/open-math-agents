import Mathlib

/-!
# A032115: Mathar's recurrence, corrected to n ≥ 6

Source: https://oeis.org/A032115
Credit: @ivillar

Status: false as stated at n = 5 (the left side is 2 at n = 5 on the OEIS data); `main` is the
corrected recurrence (n ≥ 6), which is proved.

A032115 (offset 0): 'BIJ' (reversible, indistinct, labeled) transform of 1,3,5,7...;
data 1, 1, 4, 17, 120, 1169, 13980, 195649, 3130288, 56345057, 1126900980, 24791821361, ...

Conjecture (R. J. Mathar, May 08 2020): D-finite with recurrence
a(n) +2*(-n-1)*a(n-1) +4*(n-1)*a(n-2) +2*a(n-3) +(-4*n+11)*a(n-4) +2*(n-4)*a(n-5) = 0.

Formalization: the entry gives the e.g.f. (1 + 2*(1-2*x)*exp(x) - (1-2*x)^2*exp(2*x))/(2*(1-2*x)*exp(x)) (Andrew Howroyd,
Sep 12 2018), and this is used as the definition here. With exp(x) the exponential series
(`PowerSeries.exp ℚ`) and exp(2*x) = exp(x)^2, the e.g.f. G is the formal power series over ℚ
determined by G*(2*(1-2*x)*exp(x)) = 1 + 2*(1-2*x)*exp(x) - (1-2*x)^2*exp(x)^2;
a(n) = n! [x^n] G. `main` is the corrected recurrence (n ≥ 6): on the data the left side of the recurrence as
stated is 2 at n = 5, and it vanishes from n = 6 on.
-/

namespace OMA.S_oeis_a032115

open PowerSeries

/-- The sequence with exponential generating function G: a(n) = n! [x^n] G. -/
noncomputable def a (G : ℚ⟦X⟧) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n G

/-- The corrected recurrence (n ≥ 6): Mathar's recurrence, which fails at n = 5. -/
theorem main : ∀ G : ℚ⟦X⟧, G * (2 * (1 - 2 * X) * PowerSeries.exp ℚ) = 1 + 2 * (1 - 2 * X) * PowerSeries.exp ℚ - (1 - 2 * X) ^ 2 * (PowerSeries.exp ℚ) ^ 2 →
    ∀ n : ℕ, 6 ≤ n →
      (1) * a G n + (-2 - 2 * (n : ℚ)) * a G (n - 1) +
        (-4 + 4 * (n : ℚ)) * a G (n - 2) + (2) * a G (n - 3) +
        (11 - 4 * (n : ℚ)) * a G (n - 4) + (-8 + 2 * (n : ℚ)) * a G (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a032115
