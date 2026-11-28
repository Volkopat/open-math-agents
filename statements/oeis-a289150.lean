import Mathlib

/-!
# OEIS A289150: Barker's generating function for the diagonal of the 2D Rule 597 from the corner

Source: https://oeis.org/A289150 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A289150 (Robert Price, Jul 12 2017), offset 0: Binary representation of the diagonal from
the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 597, based on the 5-celled von Neumann neighborhood. Comment: Initialized with a
single black (ON) cell at stage zero.
Formula section:
G.f.: (1 - x + x^2 - 10*x^4) / ((1 - x)*(1 - 10*x)*(1 + x^2)*(1 - 10*x^2)) (conjectured).
- Colin Barker, Jul 14 2017

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule (Rule 597
  turns an OFF cell with no ON neighbor ON). The entry's program runs on a finite torus of side
  2*128+1, which agrees with the plane for the stages listed.
* Counting convention: as the name says, a(n) writes the diagonal cells (n,n), ..., (1,1), (0,0)
  of stage n as binary digits, the corner first, and reads them in base 10. The listed terms are
  those of the diagonal. The entry's program reads the middle row (Range[i, 2*i-1] of the x-axis)
  instead, which gives 1 rather than the listed 110 at n = 2; the definition follows the name
  and the data.
* Since the denominator of the generating function has constant term 1, the identity A(x) = N/D
  for A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N in the formal power series ring over
  the integers.
* Controls from the entry, proved in the proof file: a(0..9) = 1, 10, 110, 1101, 11101, 111010,
  1111010, 11110101, 111110101, 1111101010.
-/

namespace OMA.S_oeis_a289150

open PowerSeries

/-- Stage t of the two-dimensional Rule 597 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 597 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- A289150(n): the cells (n,n), ..., (0,0) of stage n as decimal digits, corner first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n (k : ℤ) (k : ℤ) then 10 ^ k else 0

/-- Barker's generating function. -/
theorem main :
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 10 * X) * (1 + X ^ 2) * (1 - 10 * X ^ 2)) =
      1 - X + X ^ 2 - 10 * X ^ 4 := by
  sorry

end OMA.S_oeis_a289150
