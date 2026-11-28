import Mathlib

/-!
# OEIS A273145: the ON cells of the two-dimensional Rule 597 at stage 2^n - 1

Source: https://oeis.org/A273145 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A273145 (Robert Price, May 16 2016), offset 0: Number of active (ON, black) cells at stage
2^n-1 of the two-dimensional cellular automaton defined by Rule 597, based on the 5-celled von
Neumann neighborhood. Comment: Initialized with a single black (ON) cell at stage zero.
Formula section:
Conjecture: a(n) = 14*4^(n-1) - 4*2^n + 1, n>1. - Lars Blomberg, Jul 13 2016
Conjectures from Colin Barker, Jul 13 2016:
a(n) = 7*a(n-1)-14*a(n-2)+8*a(n-3) for n>4.
G.f.: (1+x-x^2+10*x^3-8*x^4) / ((1-x)*(1-2*x)*(1-4*x)).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule (Rule 597
  turns an OFF cell with no ON neighbor ON).
* Counting convention: stage t is counted in the square |x|, |y| <= t, as the program of the
  companion entry A273144 trims stage t to its central (2t+1) X (2t+1) square, and a(n) is the
  count at t = 2^n - 1; the listed terms are reproduced this way.
* The statement is the conjunction of the three conjectures: Blomberg's closed form for n > 1 and
  Barker's recurrence for n > 4, both in the integers, and the generating function A(x) =
  Sum_{n >= 0} a(n) x^n = N/D, stated as A * D = N in the formal power series ring over the
  integers (D has constant term 1).
* Controls from the entry, proved in the proof file: a(0..9) = 1, 8, 41, 193, 833, 3457, 14081,
  56833, 228353, 915457.
-/

namespace OMA.S_oeis_a273145

open PowerSeries

/-- Stage t of the two-dimensional Rule 597 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 597 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- The number of ON cells of stage t in the square |x|, |y| <= t. -/
noncomputable def count (t : ℕ) : ℕ :=
  ((Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t).filter
    (fun p => state t p.1 p.2 = true)).card

/-- A273145(n): the number of ON cells of stage 2^n - 1 in its square. -/
noncomputable def a (n : ℕ) : ℕ := count (2 ^ n - 1)

/-- Blomberg's closed form, Barker's recurrence and Barker's generating function. -/
theorem main :
    (∀ n : ℕ, 1 < n → (a n : ℤ) = 14 * 4 ^ (n - 1) - 4 * 2 ^ n + 1) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      1 + X - X ^ 2 + 10 * X ^ 3 - 8 * X ^ 4 := by
  sorry

end OMA.S_oeis_a273145
