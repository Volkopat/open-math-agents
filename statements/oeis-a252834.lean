import Mathlib

/-!
# OEIS A252834: Barker's generating function and recurrence

Source: https://oeis.org/A252834 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 22 2014), offset 1: Number of n X 6 nonnegative integer arrays with upper
left 0 and every value within 2 of its king move distance from the upper left and every value
increasing by 0 or 1 with every step right, diagonally se or down. Data: 16, 85, 529, 3365, 18528,
78674, ... The formula section states: Empirical: a(n) = 90112*n^2 - 1032064*n + 3059590 for n>9.
Conjectures from Colin Barker, Dec 07 2018: (Start) G.f.: x*(16 + 37*x + 322*x^2 + 2017*x^3 +
9935*x^4 + 32656*x^5 + 60328*x^6 + 54521*x^7 + 15495*x^8 + 4171*x^9 + 676*x^10 + 50*x^11) / (1 -
x)^3. a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>12. (End)

Formalization notes:
* An n X 6 array is a function `Fin n → Fin 6 → ℕ`, x i j being the value in row i and column j,
  counted from 0, so the king-move distance of (i, j) from the upper left is max i j. Within 2 means
  that the value differs from max i j by at most 2, stated as max i j ≤ x i j + 2 ∧
  x i j ≤ max i j + 2. The steps right, diagonally se and down go from (i, j) to (i, j + 1),
  (i + 1, j + 1) and (i + 1, j), and along each the value increases by 0 or 1 (`step01`).
* `a n` is `Set.ncard` of the set of these arrays. The set is finite: the proof identifies it with a
  finite set of arrays of deficits max i j - x i j in 0..2.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^3 =
  x*(16 + 37*x + 322*x^2 + 2017*x^3 + 9935*x^4 + 32656*x^5 + 60328*x^6 + 54521*x^7 + 15495*x^8 + 4171*x^9 + 676*x^10 + 50*x^11)
  in Z[[x]], which is equivalent because (1 - x)^3 has constant term 1.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..27), all the entry's listed terms.
-/

namespace OMA.S_oeis_a252834

open PowerSeries

/-- From the value u to the value v the value increases by 0 or 1. -/
def step01 (u v : ℕ) : Prop := v = u ∨ v = u + 1

/-- The conditions of the entry on an n X 6 array x of natural numbers (x i j in row i and
column j): the upper left value is 0, every value is within 2 of its king-move distance max i j
from the upper left, and every value increases by 0 or 1 with every step right, diagonally
down-right (se) or down. -/
def good (n : ℕ) (x : Fin n → Fin 6 → ℕ) : Prop :=
  (∀ i j, i.val = 0 → j.val = 0 → x i j = 0) ∧
  (∀ i j, max i.val j.val ≤ x i j + 2 ∧ x i j ≤ max i.val j.val + 2) ∧
  (∀ i (j j' : Fin 6), j'.val = j.val + 1 → step01 (x i j) (x i j')) ∧
  (∀ (i i' : Fin n) j, i'.val = i.val + 1 → step01 (x i j) (x i' j)) ∧
  (∀ (i i' : Fin n) (j j' : Fin 6), i'.val = i.val + 1 → j'.val = j.val + 1 →
    step01 (x i j) (x i' j'))

/-- A252834(n): the number of n X 6 arrays of natural numbers with these conditions. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin n → Fin 6 → ℕ | good n x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
      X * (16 + 37 * X + 322 * X ^ 2 + 2017 * X ^ 3 + 9935 * X ^ 4 + 32656 * X ^ 5 +
        60328 * X ^ 6 + 54521 * X ^ 7 + 15495 * X ^ 8 + 4171 * X ^ 9 + 676 * X ^ 10 +
        50 * X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a252834
