import Mathlib

/-!
# OEIS A287470: Barker's conjectures for the diagonal of the 2D Rule 276

Source: https://oeis.org/A287470 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A287470 (Robert Price, May 25 2017), offset 0: Decimal representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 276, based on the 5-celled von Neumann neighborhood. Comment: Initialized with a
single black (ON) cell at stage zero.
Formula section:
From Colin Barker, May 29 2017: Conjectures:
G.f.: 1 / ((1 - 2*x)*(1 + 2*x)*(1 - 2*x^2)).
a(n) = 2^(n+1) - 2^(n/2) for n even.
a(n) = 0 for n odd.
a(n) = 6*a(n-2) - 8*a(n-4) for n>3.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell (Rule 276 keeps an OFF cell with no ON neighbor OFF,
  so the background stays OFF). The entry's program runs on a finite torus of side 2*128+1,
  which agrees with the plane for the stages listed.
* Reading convention: as the name and the data say, a(n) reads the diagonal cells (0,0), (1,1),
  ..., (n,n) of stage n as a binary number with the origin as the most significant digit, written
  in decimal; the cell (k,k) carries the weight 2^(n-k). The program printed in the entry reads
  the middle row in base 10 instead, which does not give the listed terms (for n = 2 it gives
  101, the data has 6 = 110 in base 2).
* The statement is the conjunction of the four conjectures; the closed forms and the recurrence
  are stated in the integers, with n/2 natural-number division (n even). The denominator of the
  generating function has constant term 1, a unit, so the identity A(x) = N/D for
  A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N in the formal power series ring over the
  integers.
* Controls proved in the proof file: the definition gives 1, 0, 6, 0, 28, 0, 120, 0, 496, 0, 2016,
  0, 8128, 0, 32640, 0, 130816, 0, 523776, 0 for n = 0..19, the entry's first terms.
-/

namespace OMA.S_oeis_a287470

open PowerSeries

/-- Stage t of the two-dimensional Rule 276 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 276 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- A287470(n): the cells (0,0), (1,1), ..., (n,n) of stage n as a binary number, origin first;
the cell (k,k) carries the weight 2^(n-k). -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n (k : ℤ) (k : ℤ) then 2 ^ (n - k) else 0

/-- Barker's generating function, closed forms and recurrence. -/
theorem main :
    mk (fun n => (a n : ℤ)) * ((1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2)) =
      (1 : PowerSeries ℤ) ∧
    (∀ n : ℕ, n % 2 = 0 → (a n : ℤ) = 2 ^ (n + 1) - 2 ^ (n / 2)) ∧
    (∀ n : ℕ, n % 2 = 1 → a n = 0) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 6 * a (n - 2) - 8 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a287470
