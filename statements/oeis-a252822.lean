import Mathlib

/-!
# OEIS A252822: Barker's g.f. and recurrence for n X 2 nonnegative integer arrays with upper left 0, every value within 3 of its city block distance from the upper left and increasing by 0 or 1 with every step right or down

Source: https://oeis.org/A252822 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A252822 (R. H. Hardin, Dec 22 2014), offset 1: Number of n X 2 nonnegative integer arrays with
upper left 0 and every value within 3 of its city block distance from the upper left and every value
increasing by 0 or 1 with every step right or down. Column 2 of A252828.
Formula section:
Conjectures from Colin Barker, Dec 06 2018:
G.f.: x*(2 - 8*x + 18*x^2 - 17*x^3 + 9*x^4 - 4*x^5 + x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Formalization notes:
* An array is a function x : Fin n -> Fin 2 -> N, x i j being the entry in row i and column j
  (nonnegative integers, not bounded in advance).
* Upper left 0: x(0,0) = 0. The city block distance of (i, j) from the upper left is i + j; every
  value within 3 of it means i + j - 3 <= x(i,j) <= i + j + 3, written without subtraction.
* Every value increasing by 0 or 1 with every step right or down: x(i,j+1) - x(i,j) and x(i+1,j) -
  x(i,j) are 0 or 1.
* a(n) is the number of such arrays, `Set.ncard` of the set of functions (the set is finite since
  x(i,j) <= i + j).
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x) (1 -
  x)^7 = x*(2 - 8*x + 18*x^2 - 17*x^3 + 9*x^4 - 4*x^5 + x^6) in the formal power series ring over
  the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the
  recurrence for every n > 7 in the integers.
* Controls proved in the proof file: the definition gives 2, 6, 18, 53, 142, 339, 729, 1437, 2638,
  4568 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a252822

open PowerSeries Finset

/-- The upper left element is 0, every value is within 3 of its city block distance i + j from the
upper left, and every value increases by 0 or 1 with every step right or down. -/
def Cond {R C : ℕ} (x : Fin R → Fin C → ℕ) : Prop :=
  (∀ i j, i.val = 0 → j.val = 0 → x i j = 0) ∧
    (∀ i j, x i j ≤ i.val + j.val + 3 ∧ i.val + j.val ≤ x i j + 3) ∧
    (∀ i j j', j'.val = j.val + 1 → x i j' = x i j ∨ x i j' = x i j + 1) ∧
    (∀ i i' j, i'.val = i.val + 1 → x i' j = x i j ∨ x i' j = x i j + 1)

/-- A252822(n): the number of n X 2 arrays of nonnegative integers satisfying `Cond`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {x : Fin n → Fin 2 → ℕ | Cond x}.ncard

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (2 - 8 * X + 18 * X ^ 2 - 17 * X ^ 3 + 9 * X ^ 4 - 4 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) =
      7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a252822
