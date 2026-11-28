import Mathlib

/-!
# A200839: Number of 0..n arrays x(0..3) of 4 elements without any two consecutive increases or two consecutive decreases.

Source: https://oeis.org/A200839
Credit: @Salofe

Conjectures from Colin Barker, Oct 14 2017, quoted verbatim from the entry:
* "G.f.: x*(16 - 11*x + 9*x^2 - 5*x^3 + x^4) / (1 - x)^5."
* "a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5."

Formalization notes:
* Offset 1, as in the entry (data: 16, 69, 194, 435, 846, 1491, ...). The value `a 0`
  (entries in 0..0) is never used.
* An array is a map `x : Fin 4 → Fin (n + 1)`: an entry `x i` in 0..n at each position
  `i ∈ {0, 1, 2, 3}`, the positions of x(0..3). Arrays are labelled: they are not identified
  up to symmetry.
* "Two consecutive increases" means three consecutive positions `i`, `j = i + 1`, `k = j + 1`
  with `x i < x j < x k`; "two consecutive decreases" means `x i > x j > x k`. Equal
  neighbours are neither an increase nor a decrease, so they are allowed.
* This reading reproduces the data: exhaustive enumeration gives 16, 69, 194, 435, 846, 1491,
  2444 for n = 1, ..., 7 (a(1) = 2^4, as no array with entries in 0..1 has two consecutive
  strict increases or decreases), it agrees with the b-file for n = 1, ..., 20, and the 16
  solutions shown in the entry for n = 3 satisfy it.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - x)^5` cleared (it has constant coefficient 1, so it is
  invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 5, as in the entry.
-/

namespace OMA.S_oeis_a200839

/-- The array `x` (positions 0..3, entries in 0..n) has no two consecutive increases and no two
consecutive decreases: for any three consecutive positions `i`, `j = i + 1`, `k = j + 1`, it is
neither the case that `x i < x j < x k` nor that `x i > x j > x k`. -/
def Good {n : ℕ} (x : Fin 4 → Fin (n + 1)) : Prop :=
  ∀ i j k : Fin 4, j.val = i.val + 1 → k.val = j.val + 1 →
    ¬ (x i < x j ∧ x j < x k) ∧ ¬ (x i > x j ∧ x j > x k)

/-- A200839(n): the number of arrays x(0..3) of 4 elements in 0..n without any two consecutive
increases or two consecutive decreases. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {x : Fin 4 → Fin (n + 1) // Good x}

open PowerSeries in
/-- Barker's conjectures: the generating function
`x(16 - 11x + 9x^2 - 5x^3 + x^4)/(1 - x)^5`, and the recurrence
`a(n) = 5a(n-1) - 10a(n-2) + 10a(n-3) - 5a(n-4) + a(n-5)` for `n > 5`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
        X * (16 - 11 * X + 9 * X ^ 2 - 5 * X ^ 3 + X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a200839
