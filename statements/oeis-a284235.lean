import Mathlib

/-!
# OEIS A284235: Wu's recurrence and generating function for the x-axis of the 2D Rule 833

Source: https://oeis.org/A284235 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A284235 (Robert Price, Mar 23 2017), offset 0: Binary representation of the x-axis, from
the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 833, based on the 5-celled von Neumann neighborhood. Comment:
Initialized with a single black (ON) cell at stage zero.
Formula section:
Conjectures from Chai Wah Wu, May 04 2024:
a(n) = 10*a(n-1) + a(n-2) - 10*a(n-3) for n > 5.
G.f.: (10*x^5 - 11*x^4 + x^3 + 10*x^2 - 10*x + 1)/((x - 1)*(x + 1)*(10*x - 1)).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule (Rule 833
  turns an OFF cell with no ON neighbor ON). The entry's program runs on a finite torus of side
  2*128+1, which agrees with the plane for the stages listed.
* Reading convention: a(n) writes the cells (-n,0), (-n+1,0), ..., (0,0) of stage n as a string
  of binary digits, left edge first, and reads the string as a decimal number, as the entry's
  program does (FromDigits base 10 of the middle row from the left edge to the origin); the cell
  (-j,0) carries the weight 10^j, and leading OFF cells give leading zeros.
* The statement is the conjunction of the two conjectures; the recurrence is stated in the
  integers. The denominator (x-1)(x+1)(10x-1) of the generating function has constant term 1, a
  unit, so the identity A(x) = N/D for A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N in the
  formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 1, 0, 11, 101, 1010, 10101, 101010,
  1010101, 10101010, 101010101, 1010101010, 10101010101, 101010101010, 1010101010101,
  10101010101010 for n = 0..14, the entry's first terms.
-/

namespace OMA.S_oeis_a284235

open PowerSeries

/-- Stage t of the two-dimensional Rule 833 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 833 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- A284235(n): the cells (-n,0), ..., (0,0) of stage n written as binary digits, left edge
first, read in base 10; the cell (-j,0) carries the weight 10^j. -/
def a (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), if state n (-(j : ℤ)) 0 then 10 ^ j else 0

/-- Wu's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3)) ∧
    mk (fun n => (a n : ℤ)) * ((X - 1) * (X + 1) * (10 * X - 1)) =
      (10 * X ^ 5 - 11 * X ^ 4 + X ^ 3 + 10 * X ^ 2 - 10 * X + 1 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a284235
