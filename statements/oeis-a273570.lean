import Mathlib

/-!
# OEIS A273570: Blomberg's and Barker's conjectures for the two-dimensional Rule 798 at stages 2^n - 1

Source: https://oeis.org/A273570 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A273570 (Robert Price, May 25 2016), offset 0: Number of active (ON, black) cells at stage
2^n-1 of the two-dimensional cellular automaton defined by Rule 798, based on the 5-celled von
Neumann neighborhood. Comments: Initialized with a single black (ON) cell at stage zero.
Conjecture: Rule 862 also generates this sequence. - Lars Blomberg, Jul 21 2016
Formula section:
Conjecture: a(n) = 2*4^n - 6*2^n + 13, n>1. - Lars Blomberg
Conjectures from Colin Barker, Dec 01 2016:
a(n) = 7*a(n-1) - 14*a(n-2) + 8*a(n-3) for n>4.
G.f.: (1 - 2*x + 8*x^3 + 32*x^4) / ((1 - x)*(1 - 2*x)*(1 - 4*x)).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule (it stays
  OFF for these rules). The entry's program runs on a finite torus of side 2*128+1, which agrees
  with the plane for the stages listed.
* Counting convention: as the program does (it trims stage t to its central (2t+1) X (2t+1)
  square and counts the ON cells there), count rule t is the number of ON cells of stage t in the
  square |x|, |y| <= t, and a(n) = count 798 (2^n - 1).
* "Rule 862 also generates this sequence" is stated as count 862 (2^n - 1) = a(n) for every n.
* The statement is the conjunction of the four conjectures. Since the denominator of the
  generating function has constant term 1, the identity A(x) = N/D for A(x) = Sum_{n >= 0} a(n)
  x^n is stated as A * D = N in the formal power series ring over the integers; the closed form
  and the recurrence are stated in the integers.
* Controls from the entry, proved in the proof file: a(0..11) = 1, 5, 21, 93, 429, 1869, 7821,
  32013, 129549, 521229, 2091021, 8376333.
-/

namespace OMA.S_oeis_a273570

open PowerSeries

/-- Stage t of the two-dimensional outer totalistic automaton `rule` (Wolfram's code for the 5-cell
von Neumann neighborhood) from a single ON cell at the origin. -/
def state (rule : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit rule ((state rule t x y).toNat + 2 * ((state rule t (x - 1) y).toNat +
      (state rule t (x + 1) y).toNat + (state rule t x (y - 1)).toNat + (state rule t x (y + 1)).toNat))

/-- The number of ON cells of stage t of the automaton `rule` in the square |x|, |y| <= t. -/
noncomputable def count (rule t : ℕ) : ℕ :=
  ((Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t).filter
    (fun p => state rule t p.1 p.2 = true)).card

/-- A273570(n): the number of ON cells of stage 2^n - 1 of Rule 798 in its square. -/
noncomputable def a (n : ℕ) : ℕ := count 798 (2 ^ n - 1)

/-- Blomberg's two conjectures and Barker's two. -/
theorem main :
    (∀ n : ℕ, count 862 (2 ^ n - 1) = a n) ∧
    (∀ n : ℕ, 1 < n → (a n : ℤ) = 2 * 4 ^ n - 6 * 2 ^ n + 13) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      1 - 2 * X + 8 * X ^ 3 + 32 * X ^ 4 := by
  sorry

end OMA.S_oeis_a273570
