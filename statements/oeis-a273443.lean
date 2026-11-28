import Mathlib

/-!
# OEIS A273443: Barker's conjectures for the two-dimensional Rule 721

Source: https://oeis.org/A273443 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A273443 (Robert Price, May 22 2016), offset 0: Number of active (ON, black) cells in n-th
stage of growth of two-dimensional cellular automaton defined by Rule 721, based on the 5-celled
von Neumann neighborhood. Comment: Initialized with a single black (ON) cell at stage zero.
Formula section:
Conjectures from Colin Barker, May 23 2016:
a(n) = 4*n*(1+n) for n>3.
a(n) = 3*a(n-1)-3*a(n-2)+a(n-3) for n>6.
G.f.: (1+x+12*x^2-11*x^3+16*x^4-18*x^5+7*x^6) / (1-x)^3.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule. The entry's
  program runs on a finite torus of side 2*128+1, which agrees with the plane for the stages
  listed.
* Counting convention: a(n) is the number of ON cells of stage n in the square -n..n x -n..n, as
  the entry's program trims stage n to its central (2n+1) x (2n+1) square before counting.
* The statement is the conjunction of the three conjectures; the recurrence is stated in the
  integers. Since the denominator of the generating function has constant term 1, the identity
  A(x) = N/D for A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N in the formal power series
  ring over the integers.
* Controls from the entry: the definition gives 1, 4, 21, 41, 80, 120, 168, 224 for n = 0..7.
-/

namespace OMA.S_oeis_a273443

open PowerSeries

/-- Stage t of the two-dimensional Rule 721 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 721 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- A273443(t): the number of ON cells of stage t in the square -t..t x -t..t. -/
def on (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)).filter fun p : ℕ × ℕ =>
    state t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t)).card

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 3 < n → on n = 4 * n * (1 + n)) ∧
    (∀ n : ℕ, 6 < n → (on n : ℤ) = 3 * on (n - 1) - 3 * on (n - 2) + on (n - 3)) ∧
    mk (fun n => (on n : ℤ)) * (1 - X) ^ 3 =
      (1 + X + 12 * X ^ 2 - 11 * X ^ 3 + 16 * X ^ 4 - 18 * X ^ 5 + 7 * X ^ 6 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a273443
