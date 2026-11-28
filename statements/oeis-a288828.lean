import Mathlib

/-!
# OEIS A288828: Wu's conjectures for the diagonal of the 2D Rule 515 from the origin, base 2

Source: https://oeis.org/A288828 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A288828 (Robert Price, Jun 17 2017), offset 0: Decimal representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 515, based on the 5-celled von Neumann neighborhood. Comment: Initialized with a
single black (ON) cell at stage zero.
Formula section:
From Chai Wah Wu, Sep 06 2019:
a(n) = 3*a(n-1) - 6*a(n-3) + 4*a(n-4) for n > 5 (conjectured).
G.f.: (8*x^5 - 8*x^4 - 2*x^3 + 4*x^2 - 1)/((x - 1)*(2*x - 1)*(2*x^2 - 1)) (conjectured).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule (Rule 515
  turns an OFF cell with no ON neighbor ON). The entry's program runs on a finite torus of side
  2*128+1, which agrees with the plane for the stages listed.
* Counting convention: as the name says, a(n) writes the diagonal cells (0,0), (1,1), ..., (n,n)
  of stage n as binary digits, the origin first (most significant), and reads them in base 2.
  The listed terms are those of the diagonal. The entry's program reads the middle row
  (Range[i, 2*i-1] of the x-axis, in base 10) instead, which gives 10 rather than the listed 3 at
  n = 1; the definition follows the name and the data.
* The statement is the conjunction of both conjectures. The recurrence is stated in the
  integers. The generating function A(x) = Sum_{n >= 0} a(n) x^n = N/D is stated as A * D = N in
  the formal power series ring over the integers, which is equivalent because D has constant
  term -1, a unit.
* Controls from the entry, proved in the proof file: a(0..15) = 1, 3, 5, 11, 27, 55, 119, 239, 495,
  991, 2015, 4031, 8127, 16255, 32639, 65279.
-/

namespace OMA.S_oeis_a288828

open PowerSeries

/-- Stage t of the two-dimensional Rule 515 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 515 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- A288828(n): the cells (0,0), ..., (n,n) of stage n as binary digits, origin first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n (k : ℤ) (k : ℤ) then 2 ^ (n - k) else 0

/-- Wu's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 1) - 6 * a (n - 3) + 4 * a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((X - 1) * (2 * X - 1) * (2 * X ^ 2 - 1)) =
      8 * X ^ 5 - 8 * X ^ 4 - 2 * X ^ 3 + 4 * X ^ 2 - 1 := by
  sorry

end OMA.S_oeis_a288828
