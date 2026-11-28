import Mathlib

/-!
# OEIS A252934: Barker's generating function and recurrence

Source: https://oeis.org/A252934 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 24 2014), offset 1: Number of n X 4 nonnegative integer arrays with upper
left 0 and every value within 3 of its king move distance from the upper left and every value
increasing by 0 or 1 with every step right, diagonally se or down. Data: 8, 34, 153, 711, 3067,
10920, ... The formula section states: Empirical: a(n) = (4096/3)*n^3 - 18720*n^2 + (269642/3)*n -
149376 for n>6. Conjectures from Colin Barker, Dec 07 2018: (Start) G.f.: x*(8 + 2*x + 65*x^2 +
271*x^3 + 1013*x^4 + 2340*x^5 + 2849*x^6 + 1331*x^7 + 293*x^8 + 20*x^9) / (1 - x)^4. a(n) = 4*a(n-1)
- 6*a(n-2) + 4*a(n-3) - a(n-4) for n>10. (End)

Formalization notes:
* An n X 4 array is a function `Fin n → Fin 4 → ℕ`, x i j being the value in row i and column j,
  counted from 0, so the king-move distance of (i, j) from the upper left is max i j. Within 3 means
  that the value differs from max i j by at most 3, stated as max i j ≤ x i j + 3 ∧
  x i j ≤ max i j + 3. The steps right, diagonally se and down go from (i, j) to (i, j + 1),
  (i + 1, j + 1) and (i + 1, j), and along each the value increases by 0 or 1 (`step01`).
* `a n` is `Set.ncard` of the set of these arrays. The set is finite: the proof identifies it with a
  finite set of arrays of deficits max i j - x i j in 0..3.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^4 =
  x*(8 + 2*x + 65*x^2 + 271*x^3 + 1013*x^4 + 2340*x^5 + 2849*x^6 + 1331*x^7 + 293*x^8 + 20*x^9) in
  Z[[x]], which is equivalent because (1 - x)^4 has constant term 1.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..30), all the entry's listed terms.
-/

namespace OMA.S_oeis_a252934

open PowerSeries

/-- From the value u to the value v the value increases by 0 or 1. -/
def step01 (u v : ℕ) : Prop := v = u ∨ v = u + 1

/-- The conditions of the entry on an n X 4 array x of natural numbers (x i j in row i and
column j): the upper left value is 0, every value is within 3 of its king-move distance max i j
from the upper left, and every value increases by 0 or 1 with every step right, diagonally
down-right (se) or down. -/
def good (n : ℕ) (x : Fin n → Fin 4 → ℕ) : Prop :=
  (∀ i j, i.val = 0 → j.val = 0 → x i j = 0) ∧
  (∀ i j, max i.val j.val ≤ x i j + 3 ∧ x i j ≤ max i.val j.val + 3) ∧
  (∀ i (j j' : Fin 4), j'.val = j.val + 1 → step01 (x i j) (x i j')) ∧
  (∀ (i i' : Fin n) j, i'.val = i.val + 1 → step01 (x i j) (x i' j)) ∧
  (∀ (i i' : Fin n) (j j' : Fin 4), i'.val = i.val + 1 → j'.val = j.val + 1 →
    step01 (x i j) (x i' j'))

/-- A252934(n): the number of n X 4 arrays of natural numbers with these conditions. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin n → Fin 4 → ℕ | good n x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
      X * (8 + 2 * X + 65 * X ^ 2 + 271 * X ^ 3 + 1013 * X ^ 4 + 2340 * X ^ 5 + 2849 * X ^ 6 +
        1331 * X ^ 7 + 293 * X ^ 8 + 20 * X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a252934
