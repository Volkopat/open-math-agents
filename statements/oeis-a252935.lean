import Mathlib

/-!
# OEIS A252935: Barker's generating function and recurrence

Source: https://oeis.org/A252935 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 24 2014), offset 1: Number of n X 5 nonnegative integer arrays with upper
left 0 and every value within 3 of its king move distance from the upper left and every value
increasing by 0 or 1 with every step right, diagonally se or down. Data: 15, 83, 494, 3067, 17962,
86488, ... The formula section states: Empirical: a(n) = (133120/3)*n^3 - 760496*n^2 +
(13526246/3)*n - 9199709 for n>8. Conjectures from Colin Barker, Dec 07 2018: (Start) G.f.: x*(15 +
23*x + 252*x^2 + 1529*x^3 + 8341*x^4 + 31149*x^5 + 70316*x^6 + 86878*x^7 + 49399*x^8 + 15733*x^9 +
2477*x^10 + 128*x^11) / (1 - x)^4. a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>12. (End)

Formalization notes:
* An n X 5 array is a function `Fin n → Fin 5 → ℕ`, x i j being the value in row i and column j,
  counted from 0, so the king-move distance of (i, j) from the upper left is max i j. Within 3 means
  that the value differs from max i j by at most 3, stated as max i j ≤ x i j + 3 ∧
  x i j ≤ max i j + 3. The steps right, diagonally se and down go from (i, j) to (i, j + 1),
  (i + 1, j + 1) and (i + 1, j), and along each the value increases by 0 or 1 (`step01`).
* `a n` is `Set.ncard` of the set of these arrays. The set is finite: the proof identifies it with a
  finite set of arrays of deficits max i j - x i j in 0..3.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^4 =
  x*(15 + 23*x + 252*x^2 + 1529*x^3 + 8341*x^4 + 31149*x^5 + 70316*x^6 + 86878*x^7 + 49399*x^8 + 15733*x^9 + 2477*x^10 + 128*x^11)
  in Z[[x]], which is equivalent because (1 - x)^4 has constant term 1.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..25), all the entry's listed terms.
-/

namespace OMA.S_oeis_a252935

open PowerSeries

/-- From the value u to the value v the value increases by 0 or 1. -/
def step01 (u v : ℕ) : Prop := v = u ∨ v = u + 1

/-- The conditions of the entry on an n X 5 array x of natural numbers (x i j in row i and
column j): the upper left value is 0, every value is within 3 of its king-move distance max i j
from the upper left, and every value increases by 0 or 1 with every step right, diagonally
down-right (se) or down. -/
def good (n : ℕ) (x : Fin n → Fin 5 → ℕ) : Prop :=
  (∀ i j, i.val = 0 → j.val = 0 → x i j = 0) ∧
  (∀ i j, max i.val j.val ≤ x i j + 3 ∧ x i j ≤ max i.val j.val + 3) ∧
  (∀ i (j j' : Fin 5), j'.val = j.val + 1 → step01 (x i j) (x i j')) ∧
  (∀ (i i' : Fin n) j, i'.val = i.val + 1 → step01 (x i j) (x i' j)) ∧
  (∀ (i i' : Fin n) (j j' : Fin 5), i'.val = i.val + 1 → j'.val = j.val + 1 →
    step01 (x i j) (x i' j'))

/-- A252935(n): the number of n X 5 arrays of natural numbers with these conditions. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin n → Fin 5 → ℕ | good n x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
      X * (15 + 23 * X + 252 * X ^ 2 + 1529 * X ^ 3 + 8341 * X ^ 4 + 31149 * X ^ 5 +
        70316 * X ^ 6 + 86878 * X ^ 7 + 49399 * X ^ 8 + 15733 * X ^ 9 + 2477 * X ^ 10 +
        128 * X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a252935
