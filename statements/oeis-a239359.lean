import Mathlib

/-!
# A239359: Number of n X 6 0..2 arrays with no element equal to one plus the sum of elements to its left or one plus the sum of elements above it or one plus the sum of the elements diagonally to its northwest, modulo 3.

Source: https://oeis.org/A239359
Credit: @Salofe

The sequence is due to R. H. Hardin (Mar 17 2014); it is column 6 of A239361.

Conjectures from Colin Barker, Oct 26 2018, quoted verbatim from the entry:
* "G.f.: x*(7 - 9*x + 5*x^2 + 7*x^3 + 13*x^4 - 33*x^5 + 12*x^6 + 12*x^7 + 2*x^8 + 7*x^9 -
  4*x^10 + 10*x^11 - 10*x^12 - 10*x^13 + 9*x^14 - 3*x^15 + x^16) / (1 - x)^4."
* "a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>17."

The entry also lists Hardin's "Empirical: a(n) = (8/3)*n^3 - (45/2)*n^2 + (257/6)*n + 330 for
n>13."; that closed form is not part of this statement, which states Barker's two conjectures
only.

Formalization notes:
* Offset 1, as in the entry (data: 7, 19, 39, 77, 156, 266, 409, 599, ...). The value `a 0` is
  never used: the g.f. has coefficient 0 at x^0, and the recurrence (n > 17) only involves
  a(n-4), ..., a(n) with n - 4 ≥ 14. (With the definitions below `a 0 = 1`, counting the empty
  array.)
* An n X 6 0..2 array is a function `A : Fin n → Fin 6 → Fin 3`; `A i j` is the entry in row `i`
  (rows numbered from top to bottom) and column `j` (columns numbered from left to right), and
  its value is `(A i j).val ∈ {0, 1, 2}`. Arrays are labelled: they are not identified up to
  symmetry.
* For the entry at `(i, j)`: the elements to its left are the `A i k` with `k < j`; the elements
  above it are the `A k j` with `k < i`; the elements diagonally to its northwest are the
  `A (i - k) (j - k)` with `k ≥ 1`, as far as the array goes, i.e. the `A p.1 p.2` with
  `p.1 < i`, `p.2 < j` and `i - p.1 = j - p.2` (written `p.1 + j = p.2 + i`). An empty sum is 0.
* "No element equal to one plus the sum ..., modulo 3": for every entry `x` and each of its three
  sums `S`, `x ≠ (1 + S) mod 3` (`Valid`). Since `x ∈ {0, 1, 2}`, this says that `x` is not
  congruent to `1 + S` modulo 3. `a n` is the number of valid n X 6 arrays.
* This reading reproduces the data: a direct search computing exactly the definition below gives
  7, 19, 39, 77, 156, 266, 409, 599, 852, 1191, 1635, 2213, 2944, 3837 for n = 1, ..., 14; the
  four 5 X 6 example arrays in the entry are valid; and a row-by-row automaton count of the same
  definition gives all 210 terms of the b-file (n = 1..210). Summing over the whole northwest
  quadrant instead of the diagonal, or using only the nearest diagonal neighbour, does not
  reproduce the data.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - x)^4` cleared (it has constant coefficient 1, so it is
  invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 17, as in the entry.
-/

namespace OMA.S_oeis_a239359

/-- No element of the n X 6 array `A` (`A i j` is the entry in row `i` and column `j`) is equal,
modulo 3, to one plus the sum of the elements to its left, to one plus the sum of the elements
above it, or to one plus the sum of the elements diagonally to its northwest. -/
def Valid {n : ℕ} (A : Fin n → Fin 6 → Fin 3) : Prop :=
  ∀ (i : Fin n) (j : Fin 6),
    (A i j).val ≠ (1 + ∑ k ∈ Finset.univ.filter (fun k : Fin 6 => k < j), (A i k).val) % 3 ∧
    (A i j).val ≠ (1 + ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < i), (A k j).val) % 3 ∧
    (A i j).val ≠ (1 + ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin 6 =>
      p.1 < i ∧ p.2 < j ∧ p.1.val + j.val = p.2.val + i.val), (A p.1 p.2).val) % 3

/-- A239359(n): the number of valid n X 6 0..2 arrays. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun A : Fin n → Fin 6 → Fin 3 => Valid A)).card

open PowerSeries in
/-- Barker's conjectures: the generating function
`x(7 - 9x + 5x^2 + 7x^3 + 13x^4 - 33x^5 + 12x^6 + 12x^7 + 2x^8 + 7x^9 - 4x^10 + 10x^11 - 10x^12 -
10x^13 + 9x^14 - 3x^15 + x^16)/(1 - x)^4`, and the recurrence
`a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4)` for `n > 17`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
        X * (7 - 9 * X + 5 * X ^ 2 + 7 * X ^ 3 + 13 * X ^ 4 - 33 * X ^ 5 + 12 * X ^ 6 +
          12 * X ^ 7 + 2 * X ^ 8 + 7 * X ^ 9 - 4 * X ^ 10 + 10 * X ^ 11 - 10 * X ^ 12 -
          10 * X ^ 13 + 9 * X ^ 14 - 3 * X ^ 15 + X ^ 16) ∧
    (∀ n : ℕ, 17 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) := by
  sorry

end OMA.S_oeis_a239359
