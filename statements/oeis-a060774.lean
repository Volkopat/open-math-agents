import Mathlib

/-!
# A060774: Mathar's two recurrences

Source: https://oeis.org/A060774
Credit: @ivillar

Status: false as stated at n = 4 (first recurrence) and at n = 2 (second recurrence) with the present
data: each then involves the term a(0) = 1, and the left sides are -72 and 288 instead of 0. The
conjectures date from Oct 31 2015, when the data started at n = 1; a(0) = 1 was prepended on
Sep 09 2016. `main` is the corrected recurrences (n ≥ 5 and n ≥ 3), which avoid a(0). For these the
entry records the conjectures only; no proof or verification is noted there. They follow from the
closed form recorded in the entry, which is used as the definition here.

A060774 (offset 0): a(n) = number of lattice paths from (0,0,0) to (n,n,n) along the cracks on the
surface of a Rubik-ized n X n X n cube so that no step increases distance from goal;
data 1, 6, 54, 384, 2550, 16506, 105840, 677088, 4335606, 27829230, 179161554, ...

Conjecture (R. J. Mathar, Oct 31 2015): 2*n*(2*n-1)*(n-1)*a(n) + (n-1)*(13*n^2-209*n+258)*a(n-1)
+ 2*(-259*n^3+1785*n^2-3728*n+2460)*a(n-2) + 6*(295*n^3-2068*n^2+4833*n-3780)*a(n-3)
- 36*(3*n-10)*(2*n-7)*(3*n-11)*a(n-4) = 0.
Conjecture (R. J. Mathar, Oct 31 2015): 2*n*(n-1)*(2*n-1)*(11*n^2-33*n+24)*a(n)
- (n-1)*(473*n^4-1892*n^3+2561*n^2-1338*n+216)*a(n-1)
+ 6*(3*n-5)*(3*n-4)*(2*n-3)*(11*n^2-11*n+2)*a(n-2) = 0.

Formalization: the entry records a(n) = 6*binomial(3n, n) - 6*binomial(2n, n), valid for n > 0 (it
gives 0 at n = 0), together with a(0) = 1; this is the definition of a(n) used here. Counterexamples
with the data: at n = 2 the second recurrence reads 24*54 - 216*6 + 288*1 = 288, and at n = 4 the
first reads 168*2550 + 3*(-370)*384 + 2*(-468)*54 + 6*1344*6 - 72*1 = -72.
-/

namespace OMA.S_oeis_a060774

/-- a(0) = 1 and a(n) = 6 C(3n, n) - 6 C(2n, n) for n > 0, as recorded in the entry. -/
def a (n : ℕ) : ℤ :=
  if n = 0 then 1 else 6 * ((3 * n).choose n : ℤ) - 6 * ((2 * n).choose n : ℤ)

/-- Mathar's two conjectured recurrences for A060774, from the first index that avoids a(0). -/
theorem main :
    (∀ n : ℕ, 5 ≤ n →
      2 * (n : ℤ) * (2 * (n : ℤ) - 1) * ((n : ℤ) - 1) * a n
      + ((n : ℤ) - 1) * (13 * (n : ℤ) ^ 2 - 209 * (n : ℤ) + 258) * a (n - 1)
      + 2 * (-259 * (n : ℤ) ^ 3 + 1785 * (n : ℤ) ^ 2 - 3728 * (n : ℤ) + 2460) * a (n - 2)
      + 6 * (295 * (n : ℤ) ^ 3 - 2068 * (n : ℤ) ^ 2 + 4833 * (n : ℤ) - 3780) * a (n - 3)
      - 36 * (3 * (n : ℤ) - 10) * (2 * (n : ℤ) - 7) * (3 * (n : ℤ) - 11) * a (n - 4) = 0) ∧
    (∀ n : ℕ, 3 ≤ n →
      2 * (n : ℤ) * ((n : ℤ) - 1) * (2 * (n : ℤ) - 1) * (11 * (n : ℤ) ^ 2 - 33 * (n : ℤ) + 24) * a n
      - ((n : ℤ) - 1) * (473 * (n : ℤ) ^ 4 - 1892 * (n : ℤ) ^ 3 + 2561 * (n : ℤ) ^ 2 - 1338 * (n : ℤ) + 216) * a (n - 1)
      + 6 * (3 * (n : ℤ) - 5) * (3 * (n : ℤ) - 4) * (2 * (n : ℤ) - 3) * (11 * (n : ℤ) ^ 2 - 11 * (n : ℤ) + 2) * a (n - 2) = 0) := by
  sorry

end OMA.S_oeis_a060774
