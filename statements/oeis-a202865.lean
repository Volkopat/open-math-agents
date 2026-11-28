import Mathlib

/-!
# A202865: Number of 3 X 3 0..n arrays with row and column sums one greater than the previous row and column.

Source: https://oeis.org/A202865 (OEIS Foundation, CC BY-SA 4.0).
Credit: @mt211211 (AI-assisted: Claude Code, model claude-opus-5-5).

Entry (R. H. Hardin, Dec 25 2011), offset 1: a(n) is the number of 3 X 3 arrays with entries in
0..n whose second row sum is one greater than the first, whose third row sum is one greater than
the second, and likewise for the column sums. Terms: 2, 42, 228, 776, 2046, 4578, 9128, ...
The formula section reads:

  Empirical: a(n) = (3/10)*n^5 + (3/2)*n^4 + (3/2)*n^3 - (1/2)*n^2 - (4/5)*n.
  Conjectures from Colin Barker, Jun 02 2018: (Start)
  G.f.: 2*x*(1 + 15*x + 3*x^2 - x^3) / (1 - x)^6.
  a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.
  (End)

The empirical closed form is in R. H. Hardin's entry; the generating function and the recurrence
are Colin Barker's. All three are stated here, as a conjunction.

Formalization notes:
* An array is a function `Fin 3 → Fin 3 → Fin (n + 1)` (row, column ↦ entry in 0..n).
* "Row and column sums one greater than the previous row and column" is read, as in the entry's
  data, as: row sum 2 = row sum 1 + 1, row sum 3 = row sum 2 + 1, and the same for the three
  column sums. Nothing is assumed about the first row or column sum. (A brute-force count with
  this reading reproduces the listed terms 2, 42, 228.)
* `a n` is the number of such arrays, in ℤ. For `n = 0` the only array is zero, whose row sums
  are equal, so `a 0 = 0`: this is the constant coefficient of the generating function, which
  has no constant term since the entry has offset 1.
* The closed form is stated for every n ≥ 1 (the entry's range), over ℚ. The recurrence
  mentions a(n-6), so it is stated for n > 6, as in the entry, where all terms belong to the
  sequence. The generating function is stated with its denominator cleared, in ℚ⟦X⟧.
-/

namespace OMA.S_oeis_a202865

/-- A 3 X 3 array with entries in 0..n: `x i j` is the entry in row `i`, column `j`. -/
abbrev Arr (n : ℕ) := Fin 3 → Fin 3 → Fin (n + 1)

/-- The sum of row `i`. -/
def rowSum {n : ℕ} (x : Arr n) (i : Fin 3) : ℕ := ∑ j, (x i j : ℕ)

/-- The sum of column `j`. -/
def colSum {n : ℕ} (x : Arr n) (j : Fin 3) : ℕ := ∑ i, (x i j : ℕ)

/-- Each row sum is one greater than the previous row sum, and each column sum is one greater
than the previous column sum. -/
def IsValid {n : ℕ} (x : Arr n) : Prop :=
  rowSum x 1 = rowSum x 0 + 1 ∧ rowSum x 2 = rowSum x 1 + 1 ∧
    colSum x 1 = colSum x 0 + 1 ∧ colSum x 2 = colSum x 1 + 1

instance {n : ℕ} : DecidablePred (@IsValid n) := fun x => by
  unfold IsValid
  infer_instance

/-- A202865(n): the number of 3 X 3 arrays with entries in 0..n whose row sums and column sums
each exceed the previous one by one. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ.filter (fun x : Arr n => IsValid x)).card : ℤ)

open PowerSeries

/-- Hardin's empirical closed form (n ≥ 1), Barker's recurrence (n > 6) and Barker's generating
function with its denominator cleared. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
      3 / 10 * (n : ℚ) ^ 5 + 3 / 2 * (n : ℚ) ^ 4 + 3 / 2 * (n : ℚ) ^ 3 - 1 / 2 * (n : ℚ) ^ 2 -
        4 / 5 * (n : ℚ)) ∧
    (∀ n : ℕ, 6 < n → a n = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X) ^ 6 =
      2 * X * (1 + 15 * X + 3 * X ^ 2 - X ^ 3)) := by
  sorry

end OMA.S_oeis_a202865
