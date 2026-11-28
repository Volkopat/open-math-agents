import Mathlib

/-!
# OEIS A270682: the ON cells of the 2D Rule 190 at stage 2^n - 1, Blomberg's and Barker's conjectures

Source: https://oeis.org/A270682 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A270682 (Robert Price, Mar 21 2016), offset 0: Number of active (ON, black) cells at stage
2^n-1 of the two-dimensional cellular automaton defined by Rule 190, based on the 5-celled von
Neumann neighborhood. Comments: Initialized with a single black (ON) cell at stage zero.
Conjecture: Rule 254 also generates this sequence. - Lars Blomberg, Jun 03 2016
Formula section:
Conjecture: a(n) = 4^n + 4*2^n - 8, n>1. - Lars Blomberg, Jun 03 2016
Conjectures from Colin Barker, Jun 08 2016:
a(n) = 7*a(n-1)-14*a(n-2)+8*a(n-3) for n>4.
G.f.: (1-2*x+3*x^2-18*x^3-8*x^4) / ((1-x)*(1-2*x)*(1-4*x)).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell (Rules 190 and 254 keep an OFF cell with no ON
  neighbor OFF, so the background stays OFF).
* Counting convention: stage t is counted in the square |x|, |y| <= t, which the entry's program
  keeps when it trims stage t to its central (2t+1) X (2t+1) square, and a(n) is the count at
  t = 2^n - 1; the listed terms are reproduced this way. Blomberg's first conjecture is read as
  the same count for Rule 254 equaling a(n) for every n.
* The statement is the conjunction of Blomberg's two conjectures and Barker's two: the closed
  form for n > 1 and the recurrence for n > 4 are stated in the integers, and the generating
  function A(x) = Sum_{n >= 0} a(n) x^n = N/D is stated as A * D = N in the formal power series
  ring over the integers (D has constant term 1).
* Controls from the entry, proved in the proof file: a(0..12) = 1, 5, 24, 88, 312, 1144, 4344,
  16888, 66552, 264184, 1052664, 4202488, 16793592.
-/

namespace OMA.S_oeis_a270682

open PowerSeries

/-- Stage t of the two-dimensional Rule 190 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 190 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- Stage t of the two-dimensional Rule 254 from a single ON cell at the origin. -/
def state254 : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 254 ((state254 t x y).toNat + 2 * ((state254 t (x - 1) y).toNat +
      (state254 t (x + 1) y).toNat + (state254 t x (y - 1)).toNat + (state254 t x (y + 1)).toNat))

/-- The number of ON cells of stage t of the automaton s in the square |x|, |y| <= t. -/
noncomputable def count (s : ℕ → ℤ → ℤ → Bool) (t : ℕ) : ℕ :=
  ((Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t).filter
    (fun p => s t p.1 p.2 = true)).card

/-- A270682(n): the number of ON cells of stage 2^n - 1 of Rule 190 in its square. -/
noncomputable def a (n : ℕ) : ℕ := count state (2 ^ n - 1)

/-- Blomberg's two conjectures and Barker's two. -/
theorem main :
    (∀ n : ℕ, count state254 (2 ^ n - 1) = a n) ∧
    (∀ n : ℕ, 1 < n → (a n : ℤ) = 4 ^ n + 4 * 2 ^ n - 8) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      1 - 2 * X + 3 * X ^ 2 - 18 * X ^ 3 - 8 * X ^ 4 := by
  sorry

end OMA.S_oeis_a270682
