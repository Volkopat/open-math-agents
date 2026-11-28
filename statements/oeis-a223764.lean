import Mathlib

/-!
# OEIS A223764: Barker's generating function and recurrence

Source: https://oeis.org/A223764 (OEIS Foundation, CC BY-SA 4.0).
Credit: @EmadY
Formalization: AI-generated with Claude Code (model claude-opus-5-5).

Entry (R. H. Hardin), offset 1: Number of n X 2 0..1 arrays with rows, columns and antidiagonals
unimodal and diagonals nondecreasing. Data: 4, 12, 28, 56, 101, 169, 267, 403, 586, 826, 1134, ...
Formula section: Conjectures from Colin Barker, Feb 21 2018:
G.f.: x*(2 - 2*x + x^2)^2 / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.

Formalization notes:
* An n X 2 array is `A : Fin n → Fin 2 → Fin 2`; `A i j` is the entry in row `i` (counted from
  the top) and column `j` (counted from the left).
* A list is unimodal when it is nondecreasing up to some point and nonincreasing from there on:
  it splits as `l₁ ++ l₂` with `l₁` nondecreasing and `l₂` nonincreasing (either part may be
  empty). A list is nondecreasing when `List.Pairwise (· ≤ ·)` holds, nonincreasing when
  `List.Pairwise (· ≥ ·)` holds.
* A row is the list `[A i 0, A i 1]`, a column is the list of the `A i j` read from the top.
* Diagonals run down and to the right, antidiagonals down and to the left, both read from the
  top. In an n X 2 array each of them is either a single corner cell or a pair of cells in
  consecutive rows: the diagonal pair `A i 0, A (i+1) 1` and the antidiagonal pair
  `A i 1, A (i+1) 0`. A single cell is unimodal and nondecreasing, so the conditions are stated
  for the pairs.
* The g.f. is the formal power series `Sum_{n >= 1} a(n) x^n` over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The recurrence is stated in the integers for n > 5.
* `main` is the conjunction of Barker's two conjectures.
* Control: a brute-force enumeration of this reading gives 4, 12, 28, 56, 101, 169, 267, 403, 586
  for n = 1..9, the entry's data.
-/

namespace OMA.S_oeis_a223764

open PowerSeries

/-- A list is unimodal: nondecreasing up to some point, nonincreasing from there on. -/
def Unimodal (l : List (Fin 2)) : Prop :=
  ∃ l₁ l₂ : List (Fin 2), l = l₁ ++ l₂ ∧ l₁.Pairwise (· ≤ ·) ∧ l₂.Pairwise (· ≥ ·)

/-- An n X 2 array with entries 0..1 whose rows, columns and antidiagonals are unimodal and whose
diagonals are nondecreasing. -/
def Valid {n : ℕ} (A : Fin n → Fin 2 → Fin 2) : Prop :=
  (∀ i, Unimodal (List.ofFn (A i))) ∧
  (∀ j, Unimodal (List.ofFn fun i => A i j)) ∧
  (∀ i i' : Fin n, i'.val = i.val + 1 → Unimodal [A i 1, A i' 0]) ∧
  (∀ i i' : Fin n, i'.val = i.val + 1 → A i 0 ≤ A i' 1)

/-- A223764(n): the number of such n X 2 arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {A : Fin n → Fin 2 → Fin 2 // Valid A}

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the recurrence for n > 5. -/
theorem main :
    gf = X * (2 - 2 * X + X ^ 2) ^ 2 * ((1 - X) ^ 5)⁻¹ ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) =
      5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a223764
