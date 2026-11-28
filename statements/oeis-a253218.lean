import Mathlib

/-!
# OEIS A253218: Barker's generating function and recurrence

Source: https://oeis.org/A253218 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 29 2014), offset 1: Number of n X 3 nonnegative integer arrays with upper
left 0 and lower right its king-move distance away minus 2 and every value within 2 of its king move
distance from the upper left and every value increasing by 0 or 1 with every step right, diagonally
se or down. Data: 1, 1, 1, 19, 102, 263, ... The formula section states: Empirical: a(n) = 40*n^2 -
279*n + 497 for n>4. Conjectures from Colin Barker, Dec 09 2018: (Start) G.f.: x*(1 - 2*x + x^2 +
18*x^3 + 47*x^4 + 13*x^5 + 2*x^6) / (1 - x)^3. a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>7. (End)

Formalization notes:
* An n X 3 array is a function `Fin n → Fin 3 → ℕ`, x i j being the value in row i and column j,
  counted from 0, so the king-move distance of (i, j) from the upper left is max i j. Within 2 means
  that the value differs from max i j by at most 2, stated as max i j ≤ x i j + 2 ∧
  x i j ≤ max i j + 2. The steps right, diagonally se and down go from (i, j) to (i, j + 1),
  (i + 1, j + 1) and (i + 1, j), and along each the value increases by 0 or 1 (`step01`). The lower
  right value, at (n - 1, 2), is its king-move distance minus 2, stated as x i j + 2 = max i j for
  i = n - 1 and j = 2 in the natural numbers.
* `a n` is `Set.ncard` of the set of these arrays. The set is finite: the proof identifies it with a
  finite set of arrays of deficits max i j - x i j in 0..2.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^3 =
  x*(1 - 2*x + x^2 + 18*x^3 + 47*x^4 + 13*x^5 + 2*x^6) in Z[[x]], which is equivalent because
  (1 - x)^3 has constant term 1.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..41), all the entry's listed terms.
-/

namespace OMA.S_oeis_a253218

open PowerSeries

/-- From the value u to the value v the value increases by 0 or 1. -/
def step01 (u v : ℕ) : Prop := v = u ∨ v = u + 1

/-- The conditions of the entry on an n X 3 array x of natural numbers (x i j in row i and
column j): the upper left value is 0, the lower right value is its king-move distance from the
upper left minus 2, every value is within 2 of its king-move distance max i j from the upper
left, and every value increases by 0 or 1 with every step right, diagonally down-right (se) or
down. -/
def good (n : ℕ) (x : Fin n → Fin 3 → ℕ) : Prop :=
  (∀ i j, i.val = 0 → j.val = 0 → x i j = 0) ∧
  (∀ i j, i.val + 1 = n → j.val + 1 = 3 → x i j + 2 = max i.val j.val) ∧
  (∀ i j, max i.val j.val ≤ x i j + 2 ∧ x i j ≤ max i.val j.val + 2) ∧
  (∀ i (j j' : Fin 3), j'.val = j.val + 1 → step01 (x i j) (x i j')) ∧
  (∀ (i i' : Fin n) j, i'.val = i.val + 1 → step01 (x i j) (x i' j)) ∧
  (∀ (i i' : Fin n) (j j' : Fin 3), i'.val = i.val + 1 → j'.val = j.val + 1 →
    step01 (x i j) (x i' j'))

/-- A253218(n): the number of n X 3 arrays of natural numbers with these conditions. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin n → Fin 3 → ℕ | good n x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
      X * (1 - 2 * X + X ^ 2 + 18 * X ^ 3 + 47 * X ^ 4 + 13 * X ^ 5 + 2 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a253218
