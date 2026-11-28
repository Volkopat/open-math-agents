import Mathlib

/-!
# OEIS A284028: Mathar's conjecture that the x-axis of the two-dimensional Rule 790 is that of Rule 771

Source: https://oeis.org/A284028 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A284028 (Robert Price, Mar 18 2017), offset 0: Binary representation of the x-axis, from the
left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 790, based on the 5-celled von Neumann neighborhood. Comment: Initialized with a
single black (ON) cell at stage zero.
Formula section:
Conjecture: a(n) = A283906(n+1). - R. J. Mathar, Jun 21 2025
Entry A283906 (Robert Price, Mar 17 2017), offset 0: Binary representation of the x-axis, from the
left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 771, based on the 5-celled von Neumann neighborhood.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entries' programs (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule (it stays
  OFF for Rule 790; Rule 771 turns an OFF cell with no ON neighbor ON, so its background is ON from
  stage 1). The entries' programs run on a finite torus of side 2*128+1, which agrees with the
  plane for the stages listed.
* Counting convention: as the names and the programs say (FromDigits in base 10 of the middle row
  from the left edge to the center), a(n) writes the cells (-n,0), ..., (0,0) of stage n as binary
  digits, the left edge first, and reads them in base 10 (a leading zero at the left edge drops
  out); A283906 is defined the same way for Rule 771.
* Controls from the entries, proved in the proof file: a(0..9) = 1, 11, 101, 1111, 10111, 111011,
  1010101, 11111111, 101111111, 1110111111 and A283906(0..10) = 1, 1, 11, 101, 1111, 10111, 111011,
  1010101, 11111111, 101111111, 1110111111.
-/

namespace OMA.S_oeis_a284028

/-- Stage t of the two-dimensional outer totalistic automaton `rule` (Wolfram's code for the 5-cell
von Neumann neighborhood) from a single ON cell at the origin. -/
def state (rule : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit rule ((state rule t x y).toNat + 2 * ((state rule t (x - 1) y).toNat +
      (state rule t (x + 1) y).toNat + (state rule t x (y - 1)).toNat + (state rule t x (y + 1)).toNat))

/-- A284028(n): the cells (-n,0), ..., (0,0) of stage n of Rule 790 as decimal digits, left edge
first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state 790 n (-(k : ℤ)) 0 then 10 ^ k else 0

/-- A283906(n): the cells (-n,0), ..., (0,0) of stage n of Rule 771 as decimal digits, left edge
first. -/
def A283906 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state 771 n (-(k : ℤ)) 0 then 10 ^ k else 0

/-- Mathar's conjecture. -/
theorem main : ∀ n : ℕ, a n = A283906 (n + 1) := by
  sorry

end OMA.S_oeis_a284028
