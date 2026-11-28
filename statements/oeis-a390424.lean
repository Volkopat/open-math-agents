import Mathlib

/-!
# A390424: Mathar's recurrence, corrected to n ≥ 6

Source: https://oeis.org/A390424
Credit: @ivillar

Status: false as stated at n = 5 (the left side is -5952 at n = 5 on the OEIS data); `main` is the
corrected recurrence (n ≥ 6), which is proved.

A390424 (offset 0): expansion of 1/(2 - g^2)^2, where g = 1+x*g^3 is the g.f. of A001764;
data 1, 4, 26, 176, 1209, 8360, 57998, 403048, 2803322, 19505448, 135732626, 944461632, ...

Conjecture (R. J. Mathar, Jan 26 2026): D-finite with recurrence
10*n*(2*n-5)*a(n) +(-511*n^2+1968*n-1337)*a(n-1) +2*(2461*n^2-12759*n+14814)*a(n-2)
+4*(-5447*n^2+35358*n-55483)*a(n-3) +16*(2651*n^2-20323*n+38832)*a(n-4)
-2976*(3*n-11)*(3*n-13)*a(n-5) = 0.

Formalization: T is the g.f. of A001764, the formal power series over ℚ with T = 1 + x*T^3 (this equation determines
T, and its constant term is 1), and the g.f. G is determined by G*(2 - T^2)^2 = 1 (its constant term 1 follows and is
recorded as a hypothesis);
a(n) = [x^n] G. `main` is the corrected recurrence (n ≥ 6): on the data the left side of the recurrence as
stated is -5952 at n = 5, and it vanishes from n = 6 on.
-/

namespace OMA.S_oeis_a390424

open PowerSeries

/-- The corrected recurrence (n ≥ 6): Mathar's recurrence, which fails at n = 5. -/
theorem main : ∀ T G : ℚ⟦X⟧, T = 1 + X * T ^ 3 →
    G * (2 - T ^ 2) ^ 2 = 1 →
    coeff 0 G = 1 →
    ∀ n : ℕ, 6 ≤ n →
      (-50 * (n : ℚ) + 20 * (n : ℚ) ^ 2) * coeff n G + (-1337 + 1968 * (n : ℚ) - 511 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (29628 - 25518 * (n : ℚ) + 4922 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-221932 + 141432 * (n : ℚ) - 21788 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (621312 - 325168 * (n : ℚ) + 42416 * (n : ℚ) ^ 2) * coeff (n - 4) G + (-425568 + 214272 * (n : ℚ) - 26784 * (n : ℚ) ^ 2) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a390424
