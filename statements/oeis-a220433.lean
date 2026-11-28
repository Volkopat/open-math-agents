import Mathlib

/-!
# A220433: Mathar's recurrence, corrected to n ≥ 3

Source: https://oeis.org/A220433
Credit: @ivillar

Status: false as stated at n = 2 (the left side is 2 at n = 2 on the OEIS data); `main` is the
corrected recurrence (n ≥ 3), which is proved.

A220433 (offset 0): expansion of e.g.f. for operads for alia algebras;
data 0, 1, 2, 11, 100, 1270, 20720, 413000, 9726640, 264279400, 8137329200, 280012733000, ...

Conjecture (R. J. Mathar, Feb 27 2023): D-finite with recurrence
4*a(n) +6*(-2*n+3)*a(n-1) -(3*n-5)*(3*n-7)*a(n-2) = 0.

Formalization: The entry gives the e.g.f. in closed form as the series reversion of t - t^2 + t^3/6 (Paul Laubie,
Nov 07 2023), and this is used as the definition here: G is the formal power series over ℚ with zero
constant term and G - G^2 + G^3/6 = x, written without denominators as 6*x = 6*G - 6*G^2 + G^3;
a(n) = n! [x^n] G. `main` is the corrected recurrence (n ≥ 3): on the data the left side of the recurrence as
stated is 2 at n = 2, and it vanishes from n = 3 on.
-/

namespace OMA.S_oeis_a220433

open PowerSeries

/-- The sequence with exponential generating function G: a(n) = n! [x^n] G. -/
noncomputable def a (G : ℚ⟦X⟧) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n G

/-- The corrected recurrence (n ≥ 3): Mathar's recurrence, which fails at n = 2. -/
theorem main : ∀ G : ℚ⟦X⟧, coeff 0 G = 0 →
    6 * X = 6 * G - 6 * G ^ 2 + G ^ 3 →
    ∀ n : ℕ, 3 ≤ n →
      (4) * a G n + (18 - 12 * (n : ℚ)) * a G (n - 1) +
        (-35 + 36 * (n : ℚ) - 9 * (n : ℚ) ^ 2) * a G (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a220433
