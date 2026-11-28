import Mathlib

/-!
# OEIS A252979: Barker's generating function and recurrence

Source: https://oeis.org/A252979 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 25 2014), offset 1: Number of n X 4 nonnegative integer arrays with upper
left 0 and lower right its king-move distance away minus 2 and every value increasing by 0 or 1 with
every step right, diagonally se or down. Data: 3, 13, 33, 68, 1247, 8487, ... The formula section
states: Empirical: a(n) = 8192*n^2 - 87808*n + 241153 for n>6. Conjectures from Colin Barker, Dec 08
2018: (Start) G.f.: x*(3 + 4*x + 3*x^2 + 5*x^3 + 1129*x^4 + 4917*x^5 + 6117*x^6 + 3476*x^7 +
730*x^8) / (1 - x)^3. a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>9. (End)

Formalization notes:
* An n X 4 array is a function `Fin n → Fin 4 → ℕ`, x i j being the value in row i and column j,
  counted from 0, so the king-move distance of (i, j) from the upper left is max i j. The steps
  right, diagonally se and down go from (i, j) to (i, j + 1), (i + 1, j + 1) and (i + 1, j), and
  along each the value increases by 0 or 1 (`step01`). The lower right value, at (n - 1, 3), is its
  king-move distance minus 2, stated as x i j + 2 = max i j for i = n - 1 and j = 3 in the natural
  numbers.
* `a n` is `Set.ncard` of the set of these arrays. The set is finite: the proof identifies it with a
  finite set of arrays of deficits max i j - x i j in 0..5.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^3 =
  x*(3 + 4*x + 3*x^2 + 5*x^3 + 1129*x^4 + 4917*x^5 + 6117*x^6 + 3476*x^7 + 730*x^8) in Z[[x]], which
  is equivalent because (1 - x)^3 has constant term 1.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..31), all the entry's listed terms.
-/

namespace OMA.S_oeis_a252979

open PowerSeries

/-- From the value u to the value v the value increases by 0 or 1. -/
def step01 (u v : ℕ) : Prop := v = u ∨ v = u + 1

/-- The conditions of the entry on an n X 4 array x of natural numbers (x i j in row i and
column j): the upper left value is 0, the lower right value is its king-move distance from the
upper left minus 2, and every value increases by 0 or 1 with every step right, diagonally down-right (se) or
down. -/
def good (n : ℕ) (x : Fin n → Fin 4 → ℕ) : Prop :=
  (∀ i j, i.val = 0 → j.val = 0 → x i j = 0) ∧
  (∀ i j, i.val + 1 = n → j.val + 1 = 4 → x i j + 2 = max i.val j.val) ∧
  (∀ i (j j' : Fin 4), j'.val = j.val + 1 → step01 (x i j) (x i j')) ∧
  (∀ (i i' : Fin n) j, i'.val = i.val + 1 → step01 (x i j) (x i' j)) ∧
  (∀ (i i' : Fin n) (j j' : Fin 4), i'.val = i.val + 1 → j'.val = j.val + 1 →
    step01 (x i j) (x i' j'))

/-- A252979(n): the number of n X 4 arrays of natural numbers with these conditions. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin n → Fin 4 → ℕ | good n x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
      X * (3 + 4 * X + 3 * X ^ 2 + 5 * X ^ 3 + 1129 * X ^ 4 + 4917 * X ^ 5 + 6117 * X ^ 6 +
        3476 * X ^ 7 + 730 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a252979
