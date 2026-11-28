import Mathlib

/-!
# OEIS A278664: Barker's conjectures for the x-axis, from the left edge to the origin of the 2D Rule 62

Source: https://oeis.org/A278664 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A278664 (Robert Price, Nov 25 2016), offset 0: Binary representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 62, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, Nov 26 2016: (Start)
a(n) = a(n-1) + 10000*a(n-4) - 10000*a(n-5) for n>7.
G.f.: (1 +10*x +99*x^2 +990*x^3 -100*x^4 -990*x^5 +100*x^6 -10*x^7 +10000*x^10) / ((1 -x)*(1 -10*x)*(1 +10*x)*(1 +100*x^2)).
(End)

Formalization notes:
* Rule numbering, as in the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}} and
  rule[[10 - #]] of IntegerDigits[code, 2, 10]): the new state of a cell is bit 2s + c of the rule
  number, where c is its old state and s is the number of ON cells among its four orthogonal
  neighbors.
* Initial condition: at stage 0 the cell (0, 0) is ON and every other cell of Z x Z is OFF; each
  stage applies the rule to every cell of Z x Z (the background follows the rule too; the entry's
  program runs on a cyclic grid large enough that the result is the same).
* a(n) writes the states of the cells (x, 0) of stage n, for x = -n, ..., 0 in this order, as a
  string of binary digits and reads that string in base 10 (FromDigits in the entry's program).
* The statement is the conjunction of Barker's recurrence and generating function. The recurrence
  is stated in the integers. Since the denominator of the generating function has constant term 1,
  the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N in the formal
  power series ring over the integers.
* Controls: the definition gives 1, 11, 110, 1100, 11000, 110010, 1100110, 11000100 for n = 0..7 (the entry's data, checked by direct
  simulation).
-/

namespace OMA.S_oeis_a278664

open PowerSeries

/-- The new state of a cell: bit 2s + c of the rule number. -/
def ca (rule : ℕ) (c : Bool) (s : ℕ) : Bool := Nat.testBit rule (2 * s + c.toNat)

/-- Stage t of Rule 62 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => ca 62 (state t x y)
      ((state t (x - 1) y).toNat + (state t (x + 1) y).toNat +
        (state t x (y - 1)).toNat + (state t x (y + 1)).toNat)

/-- A278664(n): the cells (x, 0) of stage n, x = -n, ..., 0, read as base-10 digits. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (if state n ((k : ℤ) - (n : ℤ)) 0 then 1 else 0) * 10 ^ (n - k)

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = a (n - 1) + 10000 * a (n - 4) - 10000 * a (n - 5)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2)) =
      (1 + 10 * X + 99 * X ^ 2 + 990 * X ^ 3 - 100 * X ^ 4 - 990 * X ^ 5 + 100 * X ^ 6 - 10 * X ^ 7 + 10000 * X ^ 10 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a278664
