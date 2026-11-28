import Mathlib

/-!
# OEIS A287468: Barker's conjectures for the diagonal of the 2D Rule 276 read from the corner

Source: https://oeis.org/A287468 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A287468 (Robert Price, May 25 2017), offset 0: Binary representation of the diagonal from
the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 276, based on the 5-celled von Neumann neighborhood. Comment: Initialized with a
single black (ON) cell at stage zero.
Formula section:
From Colin Barker, May 29 2017:
Conjectures:
G.f.: 1 / ((1 - x)*(1 + x)*(1 - 10*x^2)).
a(n) = (10^(n/2+1) - 1) / 9 for n even.
a(n) = 0 for n odd.
a(n) = 11*a(n-2) - 10*a(n-4) for n>3.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell (Rule 276 maps an OFF cell with no ON neighbor to
  OFF).
* Counting convention: as the name says, a(n) writes the diagonal cells (n,n), ..., (1,1), (0,0)
  of stage n as binary digits, the corner first, and reads them in base 10. The listed terms are
  those of the diagonal. The entry's program reads the middle row (Range[i, 2*i-1] of the x-axis)
  instead, which gives 101 rather than the listed 11 at n = 2; the definition follows the name
  and the data.
* The statement is the conjunction of the four conjectures. Since the denominator of the
  generating function has constant term 1, the identity A(x) = 1/D for A(x) = Sum_{n >= 0} a(n)
  x^n is stated as A * D = 1 in the formal power series ring over the integers. The closed form
  for even n is stated as 9a(n) = 10^(n/2+1) - 1 in the integers, and the recurrence in the
  integers.
* Controls from the entry, proved in the proof file: a(0..11) = 1, 0, 11, 0, 111, 0, 1111, 0,
  11111, 0, 111111, 0.
-/

namespace OMA.S_oeis_a287468

open PowerSeries

/-- Stage t of the two-dimensional Rule 276 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 276 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- A287468(n): the cells (n,n), ..., (0,0) of stage n as decimal digits, corner first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n (k : ℤ) (k : ℤ) then 10 ^ k else 0

/-- Barker's generating function, closed forms and recurrence. -/
theorem main :
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X ^ 2)) = (1 : PowerSeries ℤ) ∧
    (∀ n : ℕ, n % 2 = 0 → 9 * (a n : ℤ) = 10 ^ (n / 2 + 1) - 1) ∧
    (∀ n : ℕ, n % 2 = 1 → a n = 0) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 11 * a (n - 2) - 10 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a287468
