import Mathlib

/-!
# OEIS A290197: Corneth's conjecture for the diagonal of the 2D Rule 721 from the origin

Source: https://oeis.org/A290197 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A290197 (Robert Price, Jul 23 2017), offset 0: Binary representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 721, based on the 5-celled von Neumann neighborhood. Comment: Initialized with a
single black (ON) cell at stage zero.
Formula section:
Conjecture: For n>=4, a(n) = (10^n-1) / 9 (in decimal). David A. Corneth, Jul 23 2017

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule (Rule 721
  turns an OFF cell with no ON neighbor ON). The entry's program runs on a finite torus of side
  2*128+1, which agrees with the plane for the stages listed.
* Counting convention: as the name says, a(n) writes the diagonal cells (0,0), (1,1), ..., (n,n)
  of stage n as binary digits, the origin first (most significant), and reads them in base 10,
  so a leading 0 at the origin vanishes. The listed terms are those of the diagonal. The entry's
  program reads the middle row (Range[i, 2*i-1] of the x-axis) instead, which gives 111 rather
  than the listed 101 at n = 2; the definition follows the name and the data.
* The conjecture is stated in the rationals, so the division is exact.
* Controls from the entry, proved in the proof file: a(0..10) = 1, 1, 101, 1011, 1111, 11111,
  111111, 1111111, 11111111, 111111111, 1111111111.
-/

namespace OMA.S_oeis_a290197

/-- Stage t of the two-dimensional Rule 721 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 721 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- A290197(n): the cells (0,0), ..., (n,n) of stage n as decimal digits, origin first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n (k : ℤ) (k : ℤ) then 10 ^ (n - k) else 0

/-- Corneth's conjecture. -/
theorem main : ∀ n : ℕ, 4 ≤ n → (a n : ℚ) = (10 ^ n - 1) / 9 := by
  sorry

end OMA.S_oeis_a290197
