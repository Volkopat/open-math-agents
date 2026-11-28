import Mathlib

/-!
# OEIS A288138: Barker's generating function for the diagonal of the 2D Rule 427 from the origin

Source: https://oeis.org/A288138 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A288138 (Robert Price, Jun 05 2017), offset 0: Decimal representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 427, based on the 5-celled von Neumann neighborhood. Comment: Initialized with a
single black (ON) cell at stage zero.
Formula section:
G.f.: (1 + 3*x + 5*x^2 - 4*x^3 - 6*x^4 + 4*x^5 - 24*x^6) / ((1 - x)*(1 + x)*(1 - 2*x)*(1 - 2*x^2)*
(1 + 2*x^2)*(1 + 2*x + 4*x^2)) (conjectured). - Colin Barker, Jun 06 2017

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule (Rule 427
  turns an OFF cell with no ON neighbor ON). The entry's program runs on a finite torus of side
  2*128+1, which agrees with the plane for the stages listed.
* Counting convention: as the name says, a(n) writes the diagonal cells (0,0), (1,1), ..., (n,n)
  of stage n as binary digits, the origin first (most significant), and reads them in base 2.
  The listed terms are those of the diagonal. The entry's program reads the middle row
  (Range[i, 2*i-1] of the x-axis, in base 10) instead, which gives 10 rather than the listed 3 at
  n = 1; the definition follows the name and the data.
* Since the denominator of the generating function has constant term 1, the identity A(x) = N/D
  for A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N in the formal power series ring over
  the integers.
* Controls from the entry, proved in the proof file: a(0..16) = 1, 3, 6, 7, 28, 63, 56, 223, 496,
  511, 1760, 3967, 4032, 14335, 31616, 32255, 114432.
-/

namespace OMA.S_oeis_a288138

open PowerSeries

/-- Stage t of the two-dimensional Rule 427 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 427 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- A288138(n): the cells (0,0), ..., (n,n) of stage n as binary digits, origin first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n (k : ℤ) (k : ℤ) then 2 ^ (n - k) else 0

/-- Barker's generating function. -/
theorem main : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) *
    (1 - 2 * X ^ 2) * (1 + 2 * X ^ 2) * (1 + 2 * X + 4 * X ^ 2)) =
      1 + 3 * X + 5 * X ^ 2 - 4 * X ^ 3 - 6 * X ^ 4 + 4 * X ^ 5 - 24 * X ^ 6 := by
  sorry

end OMA.S_oeis_a288138
