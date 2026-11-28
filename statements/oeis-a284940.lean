import Mathlib

/-!
# OEIS A284940: Barker's conjectures for the diagonal from the corner to the origin of the 2D Rule 107

Source: https://oeis.org/A284940 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A284940 (Robert Price, Apr 27 2017), offset 0: Binary representation of the diagonal from the corner to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 107, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, Apr 28 2017: (Start)
G.f.: (1 + 11*x - 100*x^2 - 110*x^3 - x^4 + 100*x^6 + 110*x^8 - 11100*x^10 + 10000*x^12) / ((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)*(1 - 10*x^2)).
a(n) = 111*a(n-2) - 1110*a(n-4) + 1000*a(n-6) for n>6.
(End)

Formalization notes:
* Rule numbering, as in the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}} and
  rule[[10 - #]] of IntegerDigits[code, 2, 10]): the new state of a cell is bit 2s + c of the rule
  number, where c is its old state and s is the number of ON cells among its four orthogonal
  neighbors.
* Initial condition: at stage 0 the cell (0, 0) is ON and every other cell of Z x Z is OFF; each
  stage applies the rule to every cell of Z x Z (the background follows the rule too; by the symmetry of the rule and of the start every diagonal is the same; the entry's
  program runs on a cyclic grid large enough that the result is the same).
* a(n) writes the states of the cells (x, x) of stage n, for x = n, ..., 0, in this order, as a string of
  binary digits and reads that string in base 10 (FromDigits in the entry's program).
* The statement is the conjunction of Barker's recurrence and generating function. The recurrence
  is stated in the integers. Since the denominator of the generating function has constant term 1,
  the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N in the formal
  power series ring over the integers.
* Controls: the definition gives 1, 11, 11, 1111, 110, 111111, 1100, 11111111 for n = 0..7 (the entry's data, checked by direct
  simulation).
-/

namespace OMA.S_oeis_a284940

open PowerSeries

/-- The new state of a cell: bit 2s + c of the rule number. -/
def ca (rule : ℕ) (c : Bool) (s : ℕ) : Bool := Nat.testBit rule (2 * s + c.toNat)

/-- Stage t of Rule 107 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => ca 107 (state t x y)
      ((state t (x - 1) y).toNat + (state t (x + 1) y).toNat +
        (state t x (y - 1)).toNat + (state t x (y + 1)).toNat)

/-- A284940(n): the cells (x, x) of stage n, for x = n, ..., 0, read as base-10 digits. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (if state n ((n : ℤ) - (k : ℤ)) ((n : ℤ) - (k : ℤ)) then 1 else 0) * 10 ^ (n - k)

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 111 * a (n - 2) - 1110 * a (n - 4) + 1000 * a (n - 6)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) =
      (1 + 11 * X - 100 * X ^ 2 - 110 * X ^ 3 - X ^ 4 + 100 * X ^ 6 + 110 * X ^ 8 - 11100 * X ^ 10 + 10000 * X ^ 12 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a284940
