import Mathlib

/-!
# OEIS A252823: Barker's g.f. and recurrence for n X 3 nonnegative integer arrays with upper left 0, every value within 3 of its city block distance from the upper left and increasing by 0 or 1 with every step right or down

Source: https://oeis.org/A252823 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A252823 (R. H. Hardin, Dec 22 2014), offset 1: Number of n X 3 nonnegative integer arrays with
upper left 0 and every value within 3 of its city block distance from the upper left and every value
increasing by 0 or 1 with every step right or down. Column 3 of A252828.
Formula section:
Conjectures from Colin Barker, Dec 06 2018:
G.f.: x*(4 - 22*x + 81*x^2 - 140*x^3 + 163*x^4 - 137*x^5 + 75*x^6 - 23*x^7 + 3*x^8) / (1 - x)^10.
a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>10.

Formalization notes:
* An array is a function x : Fin n -> Fin 3 -> N, x i j being the entry in row i and column j
  (nonnegative integers, not bounded in advance).
* Upper left 0: x(0,0) = 0. The city block distance of (i, j) from the upper left is i + j; every
  value within 3 of it means i + j - 3 <= x(i,j) <= i + j + 3, written without subtraction.
* Every value increasing by 0 or 1 with every step right or down: x(i,j+1) - x(i,j) and x(i+1,j) -
  x(i,j) are 0 or 1.
* a(n) is the number of such arrays, `Set.ncard` of the set of functions (the set is finite since
  x(i,j) <= i + j).
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x) (1 -
  x)^10 = x*(4 - 22*x + 81*x^2 - 140*x^3 + 163*x^4 - 137*x^5 + 75*x^6 - 23*x^7 + 3*x^8) in the
  formal power series ring over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the
  constant term is 0), and the recurrence for every n > 10 in the integers.
* Controls proved in the proof file: the definition gives 4, 18, 81, 340, 1238, 3891, 10761,
  26764, 60988, 129236 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a252823

open PowerSeries Finset

/-- The upper left element is 0, every value is within 3 of its city block distance i + j from the
upper left, and every value increases by 0 or 1 with every step right or down. -/
def Cond {R C : ℕ} (x : Fin R → Fin C → ℕ) : Prop :=
  (∀ i j, i.val = 0 → j.val = 0 → x i j = 0) ∧
    (∀ i j, x i j ≤ i.val + j.val + 3 ∧ i.val + j.val ≤ x i j + 3) ∧
    (∀ i j j', j'.val = j.val + 1 → x i j' = x i j ∨ x i j' = x i j + 1) ∧
    (∀ i i' j, i'.val = i.val + 1 → x i' j = x i j ∨ x i' j = x i j + 1)

/-- A252823(n): the number of n X 3 arrays of nonnegative integers satisfying `Cond`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {x : Fin n → Fin 3 → ℕ | Cond x}.ncard

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (4 - 22 * X + 81 * X ^ 2 - 140 * X ^ 3 + 163 * X ^ 4 - 137 * X ^ 5 + 75 * X ^ 6 - 23 * X ^ 7 + 3 * X ^ 8) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) =
      10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a252823
