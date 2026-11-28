import Mathlib

/-!
# OEIS A252814: Barker's g.f. and recurrence for n X 2 nonnegative integer arrays with upper left 0, every value within 2 of its city block distance from the upper left and increasing by 0 or 1 with every step right or down

Source: https://oeis.org/A252814 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A252814 (R. H. Hardin, Dec 22 2014), offset 1: Number of n X 2 nonnegative integer arrays with
upper left 0 and every value within 2 of its city block distance from the upper left and every value
increasing by 0 or 1 with every step right or down. Column 2 of A252820.
Formula section:
Conjectures from Colin Barker, Dec 06 2018:
G.f.: x*(2 - 4*x + 7*x^2 - 5*x^3 + x^4) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.

Formalization notes:
* An array is a function x : Fin n -> Fin 2 -> N, x i j being the entry in row i and column j
  (nonnegative integers, not bounded in advance).
* Upper left 0: x(0,0) = 0. The city block distance of (i, j) from the upper left is i + j; every
  value within 2 of it means i + j - 2 <= x(i,j) <= i + j + 2, written without subtraction.
* Every value increasing by 0 or 1 with every step right or down: x(i,j+1) - x(i,j) and x(i+1,j) -
  x(i,j) are 0 or 1.
* a(n) is the number of such arrays, `Set.ncard` of the set of functions (the set is finite since
  x(i,j) <= i + j).
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x) (1 -
  x)^5 = x*(2 - 4*x + 7*x^2 - 5*x^3 + x^4) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the recurrence for every n
  > 5 in the integers.
* Controls proved in the proof file: the definition gives 2, 6, 17, 40, 81, 147, 246, 387, 580,
  836 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a252814

open PowerSeries Finset

/-- The upper left element is 0, every value is within 2 of its city block distance i + j from the
upper left, and every value increases by 0 or 1 with every step right or down. -/
def Cond {R C : ℕ} (x : Fin R → Fin C → ℕ) : Prop :=
  (∀ i j, i.val = 0 → j.val = 0 → x i j = 0) ∧
    (∀ i j, x i j ≤ i.val + j.val + 2 ∧ i.val + j.val ≤ x i j + 2) ∧
    (∀ i j j', j'.val = j.val + 1 → x i j' = x i j ∨ x i j' = x i j + 1) ∧
    (∀ i i' j, i'.val = i.val + 1 → x i' j = x i j ∨ x i' j = x i j + 1)

/-- A252814(n): the number of n X 2 arrays of nonnegative integers satisfying `Cond`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {x : Fin n → Fin 2 → ℕ | Cond x}.ncard

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (2 - 4 * X + 7 * X ^ 2 - 5 * X ^ 3 + X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) =
      5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a252814
