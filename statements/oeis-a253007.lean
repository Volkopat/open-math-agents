import Mathlib

/-!
# OEIS A253007: Barker's generating function and recurrence

Source: https://oeis.org/A253007 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 25 2014), offset 1: Number of n X 4 nonnegative integer arrays with upper
left 0 and lower right its king-move distance away minus 3 and every value increasing by 0 or 1 with
every step right, diagonally se or down. Data: 1, 1, 1, 1, 124, 3423, ... The formula section
states: Empirical: a(n) = (65536/3)*n^3 - 422912*n^2 + (8343128/3)*n - 6208382 for n>9. Conjectures
from Colin Barker, Dec 08 2018: (Start) G.f.: x*(1 - 3*x + 3*x^2 - x^3 + 123*x^4 + 2930*x^5 +
20582*x^6 + 44788*x^7 + 42525*x^8 + 17119*x^9 + 2605*x^10 + 375*x^11 + 25*x^12) / (1 - x)^4. a(n) =
4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>13. (End)

Formalization notes:
* An n X 4 array is a function `Fin n → Fin 4 → ℕ`, x i j being the value in row i and column j,
  counted from 0, so the king-move distance of (i, j) from the upper left is max i j. The steps
  right, diagonally se and down go from (i, j) to (i, j + 1), (i + 1, j + 1) and (i + 1, j), and
  along each the value increases by 0 or 1 (`step01`). The lower right value, at (n - 1, 3), is its
  king-move distance minus 3, stated as x i j + 3 = max i j for i = n - 1 and j = 3 in the natural
  numbers.
* `a n` is `Set.ncard` of the set of these arrays. The set is finite: the proof identifies it with a
  finite set of arrays of deficits max i j - x i j in 0..6.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^4 =
  x*(1 - 3*x + 3*x^2 - x^3 + 123*x^4 + 2930*x^5 + 20582*x^6 + 44788*x^7 + 42525*x^8 + 17119*x^9 + 2605*x^10 + 375*x^11 + 25*x^12)
  in Z[[x]], which is equivalent because (1 - x)^4 has constant term 1.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..28), all the entry's listed terms.
-/

namespace OMA.S_oeis_a253007

open PowerSeries

/-- From the value u to the value v the value increases by 0 or 1. -/
def step01 (u v : ℕ) : Prop := v = u ∨ v = u + 1

/-- The conditions of the entry on an n X 4 array x of natural numbers (x i j in row i and
column j): the upper left value is 0, the lower right value is its king-move distance from the
upper left minus 3, and every value increases by 0 or 1 with every step right, diagonally down-right (se) or
down. -/
def good (n : ℕ) (x : Fin n → Fin 4 → ℕ) : Prop :=
  (∀ i j, i.val = 0 → j.val = 0 → x i j = 0) ∧
  (∀ i j, i.val + 1 = n → j.val + 1 = 4 → x i j + 3 = max i.val j.val) ∧
  (∀ i (j j' : Fin 4), j'.val = j.val + 1 → step01 (x i j) (x i j')) ∧
  (∀ (i i' : Fin n) j, i'.val = i.val + 1 → step01 (x i j) (x i' j)) ∧
  (∀ (i i' : Fin n) (j j' : Fin 4), i'.val = i.val + 1 → j'.val = j.val + 1 →
    step01 (x i j) (x i' j'))

/-- A253007(n): the number of n X 4 arrays of natural numbers with these conditions. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin n → Fin 4 → ℕ | good n x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
      X * (1 - 3 * X + 3 * X ^ 2 - X ^ 3 + 123 * X ^ 4 + 2930 * X ^ 5 + 20582 * X ^ 6 +
        44788 * X ^ 7 + 42525 * X ^ 8 + 17119 * X ^ 9 + 2605 * X ^ 10 + 375 * X ^ 11 +
        25 * X ^ 12) ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a253007
