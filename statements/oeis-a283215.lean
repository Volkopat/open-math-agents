import Mathlib

/-!
# OEIS A283215: Barker's conjectures for the right x-axis of the two-dimensional Rule 597 in binary

Source: https://oeis.org/A283215 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A283215 (Robert Price, Mar 03 2017), offset 0: Binary representation of the x-axis, from the
origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 597, based on the 5-celled von Neumann neighborhood. Comment: Initialized with a
single black (ON) cell at stage zero.
Formula section:
Conjectures from Colin Barker, Mar 04 2017:
G.f.: (1 + x + 1100*x^3) / ((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)*(1 + 100*x^2)).
a(n) = a(n-2) + 10000*a(n-4) - 10000*a(n-6) for n>5.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule (Rule 597
  turns an OFF cell with no ON neighbor ON). The entry's program runs on a finite torus of side
  2*128+1, which agrees with the plane for the stages listed.
* Counting convention: as the name and the program say (FromDigits in base 10 of the middle row
  from the center to the right edge), a(n) writes the cells (0,0), ..., (n,0) of stage n as binary
  digits, the origin first, and reads them in base 10 (a leading 0 at the origin drops out).
* The statement is the conjunction of both conjectures. The generating function A(x) =
  Sum_{n >= 0} a(n) x^n = N/D is stated as A * D = N in the formal power series ring over the
  integers, which is equivalent because D has constant term 1; the recurrence is stated in the
  integers.
* Controls from the entry, proved in the proof file: a(0..10) = 1, 1, 1, 1101, 10001, 11101,
  10001, 11011101, 100010001, 111011101, 100010001.
-/

namespace OMA.S_oeis_a283215

open PowerSeries

/-- Stage t of the two-dimensional Rule 597 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 597 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- A283215(n): the cells (0,0), ..., (n,0) of stage n as decimal digits, origin first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n (k : ℤ) 0 then 10 ^ (n - k) else 0

/-- Barker's generating function and recurrence. -/
theorem main :
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) *
      (1 + 100 * X ^ 2)) = 1 + X + 1100 * X ^ 3 ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = a (n - 2) + 10000 * a (n - 4) - 10000 * a (n - 6)) := by
  sorry

end OMA.S_oeis_a283215
