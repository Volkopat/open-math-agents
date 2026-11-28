import Mathlib

/-!
# A202785: Number of 3 X 3 0..n arrays with row and column sums equal.

Source: https://oeis.org/A202785
Credit: @Salofe

Conjectures from Colin Barker, Jun 01 2018, quoted verbatim from the entry (sequence by
R. H. Hardin, Dec 24 2011):
"Conjectures from Colin Barker, Jun 01 2018: (Start)
G.f.: x*(7 - 2*x + x^2)*(2 + x + 4*x^2 - x^3) / (1 - x)^6.
a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6. (End)"

The entry also lists "Empirical: a(n) = (3/10)*n^5 + (3/2)*n^4 + (7/2)*n^3 + (9/2)*n^2 +
(16/5)*n + 1." (with "Empirical formula verified (see link): Robert Israel, May 02 2019"); that
closed form is not part of this statement, which states Barker's two conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 14, 87, 340, 1001, 2442, 5215, ...).
* A 3 X 3 0..n array is a map `A : Fin 3 → Fin 3 → Fin (n + 1)`: `A i j` is the entry in row `i`
  and column `j` (`i, j ∈ {0, 1, 2}`), an integer in 0..n. Arrays are labelled: they are not
  identified up to symmetry.
* "Row and column sums equal" means that the three row sums and the three column sums are all
  equal to one common value `s` (`Good` below). Asking only that the three row sums agree and
  that the three column sums agree is the same condition, since both common values are a third
  of the sum of all nine entries. This reading reproduces the data: a brute-force evaluation of
  this definition gives 14, 87, 340, 1001, 2442, 5215 for n = 1, ..., 6, as in the entry, the 7
  solutions shown in the entry for n = 7 satisfy it, and a row-by-row count of the same
  definition agrees with the b-file for n = 1, ..., 40. (The reading "row i sum = column i sum
  for each i" would give a(1) = 80.)
* The definition also makes sense for n = 0 (it gives a(0) = 1, the zero array), but that value
  is outside the entry and is not used: the g.f. below has constant coefficient 0, that is, the
  series is Sum_{n>=1} a(n) x^n.
* The g.f. is the ordinary one, stated as an identity of formal power series over `ℤ` with the
  denominator `(1 - x)^6` cleared (it has constant coefficient 1, so it is invertible).
* The recurrence is stated in `ℤ` for every n > 6, as in the entry (all indices are then >= 1).
-/

namespace OMA.S_oeis_a202785

/-- The 3 X 3 array `A` (entries in 0..n) has all three row sums and all three column sums equal
to one common value `s`. -/
def Good {n : ℕ} (A : Fin 3 → Fin 3 → Fin (n + 1)) : Prop :=
  ∃ s : ℕ, (∀ i, ∑ j, (A i j : ℕ) = s) ∧ (∀ j, ∑ i, (A i j : ℕ) = s)

/-- A202785(n): the number of 3 X 3 arrays with entries in 0..n whose row sums and column sums
are all equal. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin 3 → Fin 3 → Fin (n + 1) // Good A}

/-- Barker's conjectures: the generating function
`x(7 - 2x + x^2)(2 + x + 4x^2 - x^3)/(1 - x)^6`, and the recurrence
`a(n) = 6a(n-1) - 15a(n-2) + 20a(n-3) - 15a(n-4) + 6a(n-5) - a(n-6)` for `n > 6`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - PowerSeries.X) ^ 6 =
        PowerSeries.X *
          (PowerSeries.C 7 - PowerSeries.C 2 * PowerSeries.X + PowerSeries.X ^ 2) *
          (PowerSeries.C 2 + PowerSeries.X + PowerSeries.C 4 * PowerSeries.X ^ 2 -
            PowerSeries.X ^ 3) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a202785
