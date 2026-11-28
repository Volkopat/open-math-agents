import Mathlib

/-!
# OEIS A253001: Barker's generating function and recurrence

Source: https://oeis.org/A253001 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 25 2014), offset 1: Number of n X 5 nonnegative integer arrays with upper
left 0 and lower right its king-move distance away minus 3 and every value within 3 of its king move
distance from the upper left and every value increasing by 0 or 1 with every step right, diagonally
se or down. Data: 4, 14, 34, 69, 69, 3072, ... The formula section states: Empirical: a(n) =
(133120/3)*n^3 - 893616*n^2 + (18332582/3)*n - 14187577 for n>8. Conjectures from Colin Barker, Dec
08 2018: (Start) G.f.: x*(4 - 2*x + 2*x^2 + x^3 - 55*x^4 + 3088*x^5 + 27642*x^6 + 87677*x^7 +
87826*x^8 + 45975*x^9 + 12629*x^10 + 1453*x^11) / (1 - x)^4. a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) -
a(n-4) for n>12. (End)

Formalization notes:
* An n X 5 array is a function `Fin n → Fin 5 → ℕ`, x i j being the value in row i and column j,
  counted from 0, so the king-move distance of (i, j) from the upper left is max i j. Within 3 means
  that the value differs from max i j by at most 3, stated as max i j ≤ x i j + 3 ∧
  x i j ≤ max i j + 3. The steps right, diagonally se and down go from (i, j) to (i, j + 1),
  (i + 1, j + 1) and (i + 1, j), and along each the value increases by 0 or 1 (`step01`). The lower
  right value, at (n - 1, 4), is its king-move distance minus 3, stated as x i j + 3 = max i j for
  i = n - 1 and j = 4 in the natural numbers, so there is no such array when max (n - 1) 4 < 3.
* `a n` is `Set.ncard` of the set of these arrays. The set is finite: the proof identifies it with a
  finite set of arrays of deficits max i j - x i j in 0..3.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^4 =
  x*(4 - 2*x + 2*x^2 + x^3 - 55*x^4 + 3088*x^5 + 27642*x^6 + 87677*x^7 + 87826*x^8 + 45975*x^9 + 12629*x^10 + 1453*x^11)
  in Z[[x]], which is equivalent because (1 - x)^4 has constant term 1.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..27), all the entry's listed terms.
-/

namespace OMA.S_oeis_a253001

open PowerSeries

/-- From the value u to the value v the value increases by 0 or 1. -/
def step01 (u v : ℕ) : Prop := v = u ∨ v = u + 1

/-- The conditions of the entry on an n X 5 array x of natural numbers (x i j in row i and
column j): the upper left value is 0, the lower right value is its king-move distance from the
upper left minus 3, every value is within 3 of its king-move distance max i j from the upper
left, and every value increases by 0 or 1 with every step right, diagonally down-right (se) or
down. -/
def good (n : ℕ) (x : Fin n → Fin 5 → ℕ) : Prop :=
  (∀ i j, i.val = 0 → j.val = 0 → x i j = 0) ∧
  (∀ i j, i.val + 1 = n → j.val + 1 = 5 → x i j + 3 = max i.val j.val) ∧
  (∀ i j, max i.val j.val ≤ x i j + 3 ∧ x i j ≤ max i.val j.val + 3) ∧
  (∀ i (j j' : Fin 5), j'.val = j.val + 1 → step01 (x i j) (x i j')) ∧
  (∀ (i i' : Fin n) j, i'.val = i.val + 1 → step01 (x i j) (x i' j)) ∧
  (∀ (i i' : Fin n) (j j' : Fin 5), i'.val = i.val + 1 → j'.val = j.val + 1 →
    step01 (x i j) (x i' j'))

/-- A253001(n): the number of n X 5 arrays of natural numbers with these conditions. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin n → Fin 5 → ℕ | good n x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
      X * (4 - 2 * X + 2 * X ^ 2 + X ^ 3 - 55 * X ^ 4 + 3088 * X ^ 5 + 27642 * X ^ 6 +
        87677 * X ^ 7 + 87826 * X ^ 8 + 45975 * X ^ 9 + 12629 * X ^ 10 + 1453 * X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a253001
