import Mathlib

/-!
# A222993: Number of n X 2 0..2 arrays with successive rows and columns fitting to straight lines with nondecreasing slope, with a single point array taken as having zero slope.

Source: https://oeis.org/A222993
Credit: @Salofe

Conjectures from Colin Barker, Feb 19 2018 (quoted verbatim from the entry):
  "G.f.: x*(9 - 31*x + 51*x^2 - 40*x^3 + 12*x^4) / ((1 - x)^2*(1 - 2*x)^2*(1 - 3*x))."
  "a(n) = (-13 - 2^(6+n) + 3^(4+n) - 2*(1+2^(4+n))*n) / 4."

Formalization notes:
* An n X k array with entries 0..2 is `M : Fin n → Fin k → Fin 3`; `M i j` is the entry in row `i`
  (rows numbered 0, ..., n-1 from top to bottom) and column `j` (columns numbered 0, ..., k-1 from
  left to right), read as a natural number.
* The straight line fitted to a row or a column is its least-squares line through the points
  (position, entry): for row `i` the points are `(j, M i j)`, for column `j` the points are
  `(i, M i j)`. Its slope is `Σ (x - x̄)(y - ȳ) / Σ (x - x̄)^2` with `x̄, ȳ` the means (`slope`).
  A single point (and, vacuously, an empty row or column) has slope 0, as in the name.
* Nondecreasing slope for successive rows: slope(row i) ≤ slope(row i+1) for every pair of
  consecutive rows; the same for consecutive columns (`Good`).
* `T n k` is the whole table A222996 (number of good n X k arrays) and `a n = T n 2`; A222993 is
  column 2 of A222996. These definitions reproduce the OEIS data: a brute force over all arrays
  gives a(1), ..., a(6) = 9, 50, 222, 867, 3123, 10660, and T(3,3) = 3510,
  T(4,3) = T(3,4) = 35845 as in A222996.
* Offset 1. The g.f. is the series Σ_{n ≥ 1} a(n) x^n, so the coefficient of x^0 is 0 (the value
  `a 0 = T 0 2 = 1`, which counts the empty array, is not a term of the sequence). It is stated with
  the denominator cleared, as an identity in ℚ[[x]]; the denominator has constant term 1, so this is
  equivalent to the quotient form.
* The closed form is stated in ℚ for every n ≥ 1.
-/

namespace OMA.S_oeis_a222993

/-- Slope of the least-squares straight line through the points `(i, v i)`, `i = 0, ..., m - 1`;
a single point (or no point) is taken as having zero slope. -/
def slope {m : ℕ} (v : Fin m → ℕ) : ℚ :=
  if m ≤ 1 then 0 else
    let xbar : ℚ := (∑ i : Fin m, ((i : ℕ) : ℚ)) / m
    let ybar : ℚ := (∑ i : Fin m, (v i : ℚ)) / m
    (∑ i : Fin m, (((i : ℕ) : ℚ) - xbar) * ((v i : ℚ) - ybar)) /
      ∑ i : Fin m, (((i : ℕ) : ℚ) - xbar) ^ 2

/-- Successive rows (top to bottom) and successive columns (left to right) have nondecreasing
least-squares slopes. -/
def Good {n k : ℕ} (M : Fin n → Fin k → Fin 3) : Prop :=
  (∀ i i' : Fin n, i.val + 1 = i'.val →
      slope (fun j => (M i j : ℕ)) ≤ slope (fun j => (M i' j : ℕ))) ∧
  (∀ j j' : Fin k, j.val + 1 = j'.val →
      slope (fun i => (M i j : ℕ)) ≤ slope (fun i => (M i j' : ℕ)))

/-- The table A222996: the number of good n X k arrays with entries 0..2. -/
noncomputable def T (n k : ℕ) : ℕ := by
  classical
  exact Fintype.card {M : Fin n → Fin k → Fin 3 // Good M}

/-- A222993: column 2 of A222996. -/
noncomputable def a (n : ℕ) : ℕ := T n 2

open PowerSeries in
/-- Barker's two conjectures: the generating function and the closed form. -/
theorem main :
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))) *
        ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X)) =
      X * (9 - 31 * X + 51 * X ^ 2 - 40 * X ^ 3 + 12 * X ^ 4) ∧
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (-13 - 2 ^ (6 + n) + 3 ^ (4 + n) - 2 * (1 + 2 ^ (4 + n)) * n) / 4) := by
  sorry

end OMA.S_oeis_a222993
