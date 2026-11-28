import Mathlib

/-!
# A200887: Number of 0..n arrays x(0..3) of 4 elements without any interior element greater than both neighbors.

Source: https://oeis.org/A200887
Credit: @Salofe

Conjectures from Colin Barker, Oct 16 2017, quoted verbatim from the entry (by R. H. Hardin,
Nov 23 2011):
"Conjectures from Colin Barker, Oct 16 2017: (Start)
G.f.: x*(12 - 9*x + 9*x^2 - 5*x^3 + x^4) / (1 - x)^5.
a(n) = (1+n)^2 * (3+5*n+n^2) / 3.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.
(End)"

Formalization notes:
* Offset 1, as in the entry (data: 12, 51, 144, 325, 636, 1127, ...).
* A 0..n array x(0..3) of 4 elements is a map `x : Fin 4 → Fin (n + 1)`: an entry `x i` in
  `0..n` at each position `i ∈ {0, 1, 2, 3}`, the positions of x(0..3). Arrays are labelled:
  they are not identified up to symmetry.
* The interior elements are x(1) and x(2). The neighbors of x(1) are x(0) and x(2), those of
  x(2) are x(1) and x(3). "Greater than both neighbors" is strict: x(1) is such an element iff
  `x 0 < x 1` and `x 2 < x 1`, and x(2) is one iff `x 1 < x 2` and `x 3 < x 2`. An element equal
  to a neighbor is not greater than it. So `a n` counts the arrays satisfying neither condition.
* This reading reproduces the data: a brute-force evaluation of this definition gives
  12, 51, 144, 325, 636 for n = 1, ..., 5 and agrees with all 36 terms of the entry's data
  (n = 1..36), and the 16 solutions shown in the entry for n = 3 satisfy it.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℚ` with the denominator `(1 - x)^5` cleared (it has constant coefficient 1, so it
  is invertible). The definition also makes sense for n = 0, outside the range of the entry; the
  coefficient of x^0 of the series is set to 0, matching the g.f. sum over n >= 1.
* The closed form is stated in `ℚ` (so `/ 3` is exact division) for every n >= 1, the range of
  the entry. (The entry's empirical formula of R. H. Hardin, a(n) = (1/3)*n^4 + (7/3)*n^3 +
  (14/3)*n^2 + (11/3)*n + 1, is the same polynomial.)
* The recurrence is stated in `ℤ` for every n > 5, as in the entry (all indices are then >= 1).
-/

namespace OMA.S_oeis_a200887

/-- The array `x` (positions 0..3, entries in 0..n) has no interior element greater than both
of its neighbors: neither `x 1` is greater than `x 0` and `x 2`, nor `x 2` is greater than
`x 1` and `x 3`. -/
def NoPeak {n : ℕ} (x : Fin 4 → Fin (n + 1)) : Prop :=
  ¬ (x 0 < x 1 ∧ x 2 < x 1) ∧ ¬ (x 1 < x 2 ∧ x 3 < x 2)

instance (n : ℕ) : DecidablePred (@NoPeak n) := fun x =>
  inferInstanceAs (Decidable (¬ (x 0 < x 1 ∧ x 2 < x 1) ∧ ¬ (x 1 < x 2 ∧ x 3 < x 2)))

/-- A200887(n): the number of arrays x(0..3) of 4 elements in 0..n without any interior element
greater than both neighbors. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 4 → Fin (n + 1) => NoPeak x)).card

open PowerSeries in
/-- Barker's conjectures: the generating function `x(12 - 9x + 9x^2 - 5x^3 + x^4)/(1 - x)^5`,
the closed form `a(n) = (1 + n)^2 (3 + 5n + n^2)/3` for `n ≥ 1`, and the recurrence
`a(n) = 5a(n-1) - 10a(n-2) + 10a(n-3) - 5a(n-4) + a(n-5)` for `n > 5`. -/
theorem main :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 : PowerSeries ℚ) =
        X * (12 - 9 * X + 9 * X ^ 2 - 5 * X ^ 3 + X ^ 4)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (1 + n) ^ 2 * (3 + 5 * n + n ^ 2) / 3) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a200887
