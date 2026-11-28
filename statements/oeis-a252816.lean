import Mathlib

/-!
# OEIS A252816: Barker's g.f. and recurrence for n X 4 nonnegative integer arrays with upper left 0, every value within 2 of its city block distance from the upper left and increasing by 0 or 1 with every step right or down

Source: https://oeis.org/A252816 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A252816 (R. H. Hardin, Dec 22 2014), offset 1: Number of n X 4 nonnegative integer arrays with
upper left 0 and every value within 2 of its city block distance from the upper left and every value
increasing by 0 or 1 with every step right or down. Column 4 of A252820.
Formula section:
Conjectures from Colin Barker, Dec 06 2018:
G.f.: x*(7 - 23*x + 79*x^2 - 147*x^3 + 176*x^4 - 138*x^5 + 67*x^6 - 18*x^7 + 2*x^8) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>9.

Formalization notes:
* An array is a function x : Fin n -> Fin 4 -> N, x i j being the entry in row i and column j
  (nonnegative integers, not bounded in advance).
* Upper left 0: x(0,0) = 0. The city block distance of (i, j) from the upper left is i + j; every
  value within 2 of it means i + j - 2 <= x(i,j) <= i + j + 2, written without subtraction.
* Every value increasing by 0 or 1 with every step right or down: x(i,j+1) - x(i,j) and x(i+1,j) -
  x(i,j) are 0 or 1.
* a(n) is the number of such arrays, `Set.ncard` of the set of functions (the set is finite since
  x(i,j) <= i + j).
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x) (1 -
  x)^9 = x*(7 - 23*x + 79*x^2 - 147*x^3 + 176*x^4 - 138*x^5 + 67*x^6 - 18*x^7 + 2*x^8) in the formal
  power series ring over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant
  term is 0), and the recurrence for every n > 9 in the integers.
* Controls proved in the proof file: the definition gives 7, 40, 187, 684, 2078, 5490, 13015,
  28299, 57338, 109549 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a252816

open PowerSeries Finset

/-- The upper left element is 0, every value is within 2 of its city block distance i + j from the
upper left, and every value increases by 0 or 1 with every step right or down. -/
def Cond {R C : ℕ} (x : Fin R → Fin C → ℕ) : Prop :=
  (∀ i j, i.val = 0 → j.val = 0 → x i j = 0) ∧
    (∀ i j, x i j ≤ i.val + j.val + 2 ∧ i.val + j.val ≤ x i j + 2) ∧
    (∀ i j j', j'.val = j.val + 1 → x i j' = x i j ∨ x i j' = x i j + 1) ∧
    (∀ i i' j, i'.val = i.val + 1 → x i' j = x i j ∨ x i' j = x i j + 1)

/-- A252816(n): the number of n X 4 arrays of nonnegative integers satisfying `Cond`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {x : Fin n → Fin 4 → ℕ | Cond x}.ncard

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (7 - 23 * X + 79 * X ^ 2 - 147 * X ^ 3 + 176 * X ^ 4 - 138 * X ^ 5 + 67 * X ^ 6 - 18 * X ^ 7 + 2 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) =
      9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a252816
