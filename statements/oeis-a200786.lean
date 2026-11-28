import Mathlib

/-!
# A200786: Number of 0..n arrays x(0..3) of 4 elements without any two consecutive increases.

Source: https://oeis.org/A200786
Credit: @Salofe

Conjectures from Colin Barker, Oct 15 2017, quoted verbatim from the entry (by R. H. Hardin,
Nov 22 2011):
"Conjectures from Colin Barker, Oct 15 2017: (Start)
G.f.: x*(16 - 5*x + 10*x^2 - 5*x^3 + x^4) / (1 - x)^5.
a(n) = (24 + 106*n + 151*n^2 + 86*n^3 + 17*n^4) / 24.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.
(End)"

Formalization notes:
* Offset 1, as in the entry (data: 16, 75, 225, 530, 1071, 1946, ...).
* A 0..n array x(0..3) of 4 elements is an ordered 4-tuple `(x0, x1, x2, x3) : ℕ × ℕ × ℕ × ℕ`
  with every entry in `0..n`, i.e. in `Finset.range (n + 1)`. Arrays are labelled tuples: they
  are not identified up to symmetry.
* "Two consecutive increases" means two increases in a row, x(i) < x(i+1) < x(i+2); in an array
  of 4 elements this can only happen at i = 0 or i = 1. So `a n` counts the 4-tuples with
  neither `x0 < x1 < x2` nor `x1 < x2 < x3`. This reading reproduces the data: a brute-force
  evaluation of this definition gives a(1..3) = 16, 75, 225 and agrees with all 34 terms of the
  entry's data (n = 1..34).
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℚ` in the form N * D⁻¹ with N = x(16 - 5x + 10x^2 - 5x^3 + x^4) and
  D = (1 - x)^5 (D has constant coefficient 1, so it is invertible). The definition also makes
  sense for n = 0, outside the range of the entry, where it gives a(0) = 1 (the array 0, 0, 0, 0);
  so the coefficient of x^0 of the series is set to 0, matching the g.f. sum over n >= 1.
* The closed form is stated in `ℚ` (so `/ 24` is exact division) for every n >= 1, the range of
  the entry. (The entry's empirical formula of R. H. Hardin, a(n) = (17/24)*n^4 + (43/12)*n^3 +
  (151/24)*n^2 + (53/12)*n + 1, is the same polynomial.)
* The recurrence is stated in `ℤ` for every n > 5, as in the entry (all indices are then >= 1).
-/

namespace OMA.S_oeis_a200786

/-- A200786(n): the number of arrays `(x0, x1, x2, x3)` with every entry in `0..n` and without
two consecutive increases, i.e. with neither `x0 < x1 < x2` nor `x1 < x2 < x3`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1)).filter
    (fun ⟨x0, x1, x2, x3⟩ => ¬ (x0 < x1 ∧ x1 < x2) ∧ ¬ (x1 < x2 ∧ x2 < x3))).card

open PowerSeries in
/-- Barker's conjectures: the generating function `x(16 - 5x + 10x^2 - 5x^3 + x^4)/(1 - x)^5`,
the closed form `a(n) = (24 + 106n + 151n^2 + 86n^3 + 17n^4)/24` for `n ≥ 1`, and the recurrence
`a(n) = 5a(n-1) - 10a(n-2) + 10a(n-3) - 5a(n-4) + a(n-5)` for `n > 5`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
        (X * (16 - 5 * X + 10 * X ^ 2 - 5 * X ^ 3 + X ^ 4)) * ((1 - X) ^ 5)⁻¹ ∧
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (24 + 106 * n + 151 * n ^ 2 + 86 * n ^ 3 + 17 * n ^ 4) / 24) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a200786
