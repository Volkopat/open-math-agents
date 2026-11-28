import Mathlib

/-!
# OEIS A273744: Barker's conjectures for the partial sums of the two-dimensional Rule 901

Source: https://oeis.org/A273744 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A273744 (Robert Price, May 28 2016), offset 0: Partial sums of the number of active (ON,
black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 901,
based on the 5-celled von Neumann neighborhood. Comment: Initialized with a single black (ON)
cell at stage zero.
Formula section:
Conjectures from Colin Barker, May 29 2016:
a(n) = n*(11+12*n+4*n^2)/3 for n>0.
a(n) = 4*a(n-1)-6*a(n-2)+4*a(n-3)-a(n-4) for n>4.
G.f.: (1+5*x+4*x^2-3*x^3+x^4) / (1-x)^4.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule. The entry's
  program runs on a finite torus of side 2*128+1, which agrees with the plane for the stages
  listed.
* Counting convention: stage t counts the ON cells in the square -t..t x -t..t, as the entry's
  program trims stage t to its central (2t+1) x (2t+1) square, and a(n) is the sum of these
  counts for t = 0..n.
* The statement is the conjunction of the three conjectures. The closed form is stated for n > 0
  as 3a(n) = n(11+12n+4n^2), and the recurrence in the integers. Since the denominator of the
  generating function has constant term 1, the identity A(x) = N/D for A(x) = Sum_{n >= 0} a(n)
  x^n is stated as A * D = N in the formal power series ring over the integers.
* Controls from the entry: the definition gives 1, 9, 34, 83, 164, 285, 454 for n = 0..6.
-/

namespace OMA.S_oeis_a273744

open PowerSeries

/-- Stage t of the two-dimensional Rule 901 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 901 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- The number of ON cells of stage t in the square -t..t x -t..t. -/
def on (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)).filter fun p : ℕ × ℕ =>
    state t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t)).card

/-- A273744(n): the sum of the stage counts for t = 0..n. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), on t

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 0 < n → 3 * a n = n * (11 + 12 * n + 4 * n ^ 2)) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * (1 - X) ^ 4 =
      (1 + 5 * X + 4 * X ^ 2 - 3 * X ^ 3 + X ^ 4 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a273744
