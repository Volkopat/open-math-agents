import Mathlib

/-!
# OEIS A284354: Barker's conjectures for the x-axis of the two-dimensional Rule 899

Source: https://oeis.org/A284354 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A284354 (Robert Price, Mar 25 2017), offset 0: Decimal representation of the x-axis, from
the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 899, based on the 5-celled von Neumann neighborhood. Comment:
Initialized with a single black (ON) cell at stage zero.
Formula section:
Conjectures from Colin Barker, Mar 26 2017:
G.f.: (1 + x + x^2) / ((1 - x)*(1 - 2*x)*(1 + 2*x)).
a(n) = (2^(n+3) - 4)/4 for n even.
a(n) = (3*2^(n+1) - 4)/4 for n odd.
a(n) = a(n-1) + 4*a(n-2) - 4*a(n-3) for n>2.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule. The entry's
  program runs on a finite torus of side 2*128+1, which agrees with the plane for the stages
  listed.
* Counting convention: a(n) reads the cells (0,0), (1,0), ..., (n,0) of stage n as a binary
  number with the origin as the most significant digit, as the entry's program does (FromDigits
  base 2 from the origin to the right edge).
* The statement is the conjunction of the four conjectures. Since the denominator of the
  generating function has constant term 1, the identity A(x) = N/D for A(x) = Sum_{n >= 0} a(n)
  x^n is stated as A * D = N in the formal power series ring over the integers. The two closed
  forms are stated as 4a(n) = 2^(n+3) - 4 (n even) and 4a(n) = 3*2^(n+1) - 4 (n odd) in the
  integers, and the recurrence in the integers.
* Controls from the entry: the definition gives 1, 2, 7, 11, 31, 47, 127, 191 for n = 0..7.
-/

namespace OMA.S_oeis_a284354

open PowerSeries

/-- Stage t of the two-dimensional Rule 899 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 899 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- A284354(n): the cells (0,0), ..., (n,0) of stage n as a binary number, origin first. -/
def a (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), if state n (j : ℤ) 0 then 2 ^ (n - j) else 0

/-- Barker's generating function, closed forms and recurrence. -/
theorem main :
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 + 2 * X)) =
      (1 + X + X ^ 2 : PowerSeries ℤ) ∧
    (∀ n : ℕ, n % 2 = 0 → 4 * (a n : ℤ) = 2 ^ (n + 3) - 4) ∧
    (∀ n : ℕ, n % 2 = 1 → 4 * (a n : ℤ) = 3 * 2 ^ (n + 1) - 4) ∧
    (∀ n : ℕ, 2 < n → (a n : ℤ) = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a284354
