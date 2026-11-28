import Mathlib

/-!
# OEIS A273684: Blomberg's conjecture for the two-dimensional Rule 841 at stages 2^n - 1

Source: https://oeis.org/A273684
Credit: @yooeonwoo

Entry A273684 (offset 0): Number of active (ON, black) cells at stage 2^n - 1 of the
two-dimensional cellular automaton defined by Rule 841, based on the 5-celled von Neumann
neighborhood, initialized with a single black (ON) cell at stage zero.
Conjecture (Lars Blomberg, Jul 23 2016): Rule 857 also generates this sequence.

Formalization notes:
* Rule numbering follows Wolfram's outer-totalistic code for the 5-cell von Neumann neighborhood,
  matching the entry's Mathematica program (CAStep with kernel {{0,2,0},{2,1,2},{0,2,0}}): the new
  state of a cell is bit c + 2*s of the rule number, where c is its own state (1 for ON) and s is
  the number of ON cells among its four orthogonal neighbors.
* At stage 0 the origin (0, 0) is ON and every other cell of Z^2 is OFF; each step updates every
  cell of Z^2 synchronously (the uniform background flips from OFF to ON at stage 1 and stays ON).
* Matching the entry's Mathematica program (which trims stage t to its central (2t+1) x (2t+1)
  square and counts ON cells there), count rule t is the number of ON cells of stage t in
  [-t, t]^2, and a(n) = count 841 (2^n - 1), giving 1, 4, 37, 177, 753, 3177, ...
* The conjecture states that count 857 (2^n - 1) = a n for every natural number n.
-/

namespace OMA.S_oeis_a273684

/-- Stage `t` of the two-dimensional outer-totalistic 5-cell von Neumann cellular automaton with
Wolfram code `rule`, initialized with a single ON cell at `(0, 0)`. -/
def state (rule : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y =>
    Nat.testBit rule
      ((state rule t x y).toNat +
        2 * ((state rule t (x - 1) y).toNat + (state rule t (x + 1) y).toNat +
             (state rule t x (y - 1)).toNat + (state rule t x (y + 1)).toNat))

/-- Number of ON cells at stage `t` of `rule` inside the trimmed square `[-t, t] x [-t, t]`. -/
noncomputable def count (rule t : ℕ) : ℕ :=
  ((Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t).filter
    (fun p => state rule t p.1 p.2 = true)).card

/-- A273684(n): active ON cells at stage `2^n - 1` of Rule 841. -/
noncomputable def a (n : ℕ) : ℕ := count 841 (2 ^ n - 1)

/-- Conjecture (Lars Blomberg, Jul 23 2016): Rule 857 generates the same sequence as Rule 841. -/
theorem main : ∀ n : ℕ, count 857 (2 ^ n - 1) = a n := by
  sorry

end OMA.S_oeis_a273684
