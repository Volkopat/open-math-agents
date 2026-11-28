import Mathlib

/-!
# A200888: Number of 0..n arrays x(0..4) of 5 elements without any interior element greater than both neighbors.

Source: https://oeis.org/A200888
Credit: @Salofe

Conjectures from Colin Barker, Oct 16 2017, quoted verbatim from the entry (sequence by
R. H. Hardin, Nov 23 2011):
"Conjectures from Colin Barker, Oct 16 2017: (Start)
G.f.: x*(21 - 5*x + 11*x^2 - 16*x^3 + 6*x^4 - x^5) / (1 - x)^6.
a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6. (End)"

The entry also lists "Empirical: a(n) = (2/15)*n^5 + (11/6)*n^4 + (35/6)*n^3 + (23/3)*n^2 +
(68/15)*n + 1."; that closed form is not part of this statement, which states Barker's two
conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 21, 121, 422, 1121, 2507, 4977, ...). The definition also
  makes sense for n = 0 (it gives a(0) = 1, the single array of zeros), but that value is outside
  the entry and is not used: the g.f. below has constant coefficient 0.
* A 0..n array x(0..4) of 5 elements is a map `x : Fin 5 → Fin (n + 1)`: an entry `x i` in 0..n
  at each position `i ∈ {0, 1, 2, 3, 4}`, the positions of x(0..4). Arrays are labelled: they are
  not identified up to symmetry.
* The interior elements are x(1), x(2) and x(3); the neighbors of x(i) are x(i-1) and x(i+1).
  "Greater than both neighbors" is strict: x(i) is such an element iff `x i > x (i-1)` and
  `x i > x (i+1)`. An element equal to a neighbor is not greater than it. So `a n` counts the
  arrays in which none of x(1), x(2), x(3) is greater than both of its neighbors.
* This reading reproduces the data: a brute-force evaluation of this definition gives
  21, 121, 422, 1121, 2507, 4977, ... for n = 1, ..., 12, as in the entry, the 16 solutions shown
  in the entry for n = 3 satisfy it, and a single-sum evaluation of the same count agrees with
  all 210 terms of the b-file. (The non-strict reading would give a(1) = 0.)
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℚ` with the denominator `(1 - x)^6` cleared (it has constant coefficient 1, so it
  is invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 6, as in the entry (all indices are then >= 1).
-/

namespace OMA.S_oeis_a200888

/-- The array `x` (positions 0..4, entries in 0..n) has no interior element greater than both of
its neighbors: none of `x 1`, `x 2`, `x 3` is greater than both the entry before it and the entry
after it. -/
def NoPeak {n : ℕ} (x : Fin 5 → Fin (n + 1)) : Prop :=
  ¬ (x 1 > x 0 ∧ x 1 > x 2) ∧ ¬ (x 2 > x 1 ∧ x 2 > x 3) ∧ ¬ (x 3 > x 2 ∧ x 3 > x 4)

instance (n : ℕ) : DecidablePred (@NoPeak n) := fun x =>
  inferInstanceAs
    (Decidable (¬ (x 1 > x 0 ∧ x 1 > x 2) ∧ ¬ (x 2 > x 1 ∧ x 2 > x 3) ∧ ¬ (x 3 > x 2 ∧ x 3 > x 4)))

/-- A200888(n): the number of arrays x(0..4) of 5 elements in 0..n without any interior element
greater than both neighbors. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 5 → Fin (n + 1) => NoPeak x)).card

open PowerSeries in
/-- Barker's conjectures: the generating function
`x(21 - 5x + 11x^2 - 16x^3 + 6x^4 - x^5)/(1 - x)^6`, and the recurrence
`a(n) = 6a(n-1) - 15a(n-2) + 20a(n-3) - 15a(n-4) + 6a(n-5) - a(n-6)` for `n > 6`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
        X * (21 - 5 * X + 11 * X ^ 2 - 16 * X ^ 3 + 6 * X ^ 4 - X ^ 5) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a200888
