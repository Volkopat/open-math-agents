import Mathlib

/-!
# A158826: Third iteration of x*C(x) where C(x) is the Catalan function (A000108).

Source: https://oeis.org/A158826
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A158826 (R. J. Mathar, Aug 30 2021):
Conjecture D-finite with recurrence 1053*n*(n-1)*(n-2)*(n-3)*a(n)
-36*(n-1)*(n-2)*(n-3)*(634*n-1367)*a(n-1) +24*(n-2)*(n-3)*(7966*n^2-43500*n+61181)*a(n-2)
-8*(n-3)*(96128*n^3-957424*n^2+3221878*n-3665189)*a(n-3)
+16*(91904*n^4-1446528*n^3+8575792*n^2-22703688*n+22652013)*a(n-4)
-256*(8*n-35)*(8*n-41)*(8*n-39)*(8*n-37)*a(n-5)=0.

Conventions:
* The sequence has offset 1 (data 1, 3, 12, 54, 260, 1310, 6824, ...).
* The Catalan function is C(x) = Sum_{n>=0} A000108(n)*x^n, the ordinary generating function of
  the Catalan numbers (`catalan` in Mathlib), taken as a formal power series over `ℤ`;
  `f` is the power series x*C(x).
* The third iteration is the threefold composition f(f(f(x))), written with the Mathlib
  substitution of power series: `PowerSeries.subst g f` is the series f(g(x)), so
  `PowerSeries.subst (PowerSeries.subst f f) f` is f(f(f(x))). The substitutions are legitimate
  because f has zero constant term.
* a(n) is the coefficient of x^n in f(f(f(x))) (so a(0) = 0, which is below the offset and is
  not used).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 6`, which is
  exactly the range in which all the indices n, n-1, ..., n-5 are at least the offset 1.
* The identity is stated in `ℤ`, with the natural number `n` cast to `ℤ`, so the subtractions
  and negative coefficients are exact.
-/

namespace OMA.S_oeis_a158826

/-- The power series x*C(x), where C(x) is the generating function of the Catalan numbers. -/
noncomputable def f : PowerSeries ℤ :=
  PowerSeries.X * PowerSeries.mk (fun n => (catalan n : ℤ))

/-- A158826 (offset 1): a(n) is the coefficient of x^n in the third iteration f(f(f(x))) of
f(x) = x*C(x). -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (PowerSeries.subst (PowerSeries.subst f f) f)

/-- For every `n ≥ 6`, 1053*n*(n-1)*(n-2)*(n-3)*a(n) - 36*(n-1)*(n-2)*(n-3)*(634*n-1367)*a(n-1)
+ 24*(n-2)*(n-3)*(7966*n^2-43500*n+61181)*a(n-2)
- 8*(n-3)*(96128*n^3-957424*n^2+3221878*n-3665189)*a(n-3)
+ 16*(91904*n^4-1446528*n^3+8575792*n^2-22703688*n+22652013)*a(n-4)
- 256*(8*n-35)*(8*n-41)*(8*n-39)*(8*n-37)*a(n-5) = 0. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    1053 * (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * a n
      - 36 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (634 * (n : ℤ) - 1367) * a (n - 1)
      + 24 * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (7966 * (n : ℤ) ^ 2 - 43500 * (n : ℤ) + 61181)
        * a (n - 2)
      - 8 * ((n : ℤ) - 3)
        * (96128 * (n : ℤ) ^ 3 - 957424 * (n : ℤ) ^ 2 + 3221878 * (n : ℤ) - 3665189) * a (n - 3)
      + 16 * (91904 * (n : ℤ) ^ 4 - 1446528 * (n : ℤ) ^ 3 + 8575792 * (n : ℤ) ^ 2
          - 22703688 * (n : ℤ) + 22652013) * a (n - 4)
      - 256 * (8 * (n : ℤ) - 35) * (8 * (n : ℤ) - 41) * (8 * (n : ℤ) - 39) * (8 * (n : ℤ) - 37)
        * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a158826
