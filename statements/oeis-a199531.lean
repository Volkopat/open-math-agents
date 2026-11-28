import Mathlib

/-!
# A199531: Number of -n..n arrays x(0..3) of 4 elements with zero sum and no two consecutive zero elements.

Source: https://oeis.org/A199531
Credit: @Salofe

Conjectures from Colin Barker, May 15 2018, quoted verbatim from the entry:
* "G.f.: 4*x*(3 + 6*x - x^2) / (1 - x)^4."
* "a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4."

The entry also lists "Empirical: a(n) = (16/3)*n^3 + 8*n^2 - (4/3)*n." (row 4 of A199530);
that closed form is not part of this statement, which states Barker's two conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 12, 72, 212, 464, 860, 1432, ...). The value `a 0` (entries
  in 0..0) is never used.
* An array `x(0..3)` of 4 elements is a map `x : Fin 4 → ℤ`, `x i` being its element in position
  `i`. It is a "-n..n array" when every element lies in the integer interval `[-n, n]`, so these
  arrays are the elements of `Fintype.piFinset fun _ => Finset.Icc (-n) n`. Arrays are ordered
  tuples: they are not identified up to any symmetry.
* "Zero sum": `x 0 + x 1 + x 2 + x 3 = 0`.
* "No two consecutive zero elements": there is no position `i ∈ {0, 1, 2}` with
  `x i = x (i + 1) = 0`. Consecutive means positions `i` and `i + 1` of the array, read linearly
  (positions 3 and 0 are not consecutive).
* This reading reproduces the data: exhaustive enumeration gives 12, 72, 212, 464, 860, 1432,
  2212, 3232 for n = 1, ..., 8, and the 16 solutions shown in the entry for n = 5 satisfy it.
  Reading the array cyclically (also forbidding `x 3 = x 0 = 0`) would give 10, 68, 206 for
  n = 1, 2, 3 instead of 12, 72, 212.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℚ` with the denominator `(1 - x)^4` cleared (it has constant coefficient 1, so it
  is invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 4, as in the entry.
-/

namespace OMA.S_oeis_a199531

/-- The array `x(0..3)` has zero sum and no two consecutive zero elements (positions `i` and
`i + 1`, for `i = 0, 1, 2`). -/
def Good (x : Fin 4 → ℤ) : Prop :=
  ∑ i, x i = 0 ∧ ∀ i : Fin 3, ¬ (x i.castSucc = 0 ∧ x i.succ = 0)

/-- A199531(n): the number of arrays `x(0..3)` of 4 elements of `-n..n` with zero sum and no two
consecutive zero elements. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) n).filter Good).card

open PowerSeries in
/-- Barker's conjectures: the generating function `4x(3 + 6x - x^2)/(1 - x)^4`, and the
recurrence `a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4)` for `n > 4`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
        4 * X * (3 + 6 * X - X ^ 2) ∧
    ∀ n : ℕ, 4 < n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a199531
