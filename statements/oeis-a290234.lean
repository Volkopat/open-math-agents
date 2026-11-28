import Mathlib

/-!
# OEIS A290234: Barker's conjectures for the diagonal of the 2D Rule 773 from the corner, in base 2

Source: https://oeis.org/A290234 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A290234 (Robert Price, Jul 24 2017), offset 0: Decimal representation of the diagonal from
the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 773, based on the 5-celled von Neumann neighborhood. Comment: Initialized with a
single black (ON) cell at stage zero.
Formula section:
Conjectures from Colin Barker, Jul 25 2017:
G.f.: (1-2*x^3) / ((1-x)*(1+x)*(1-2*x)*(1-2*x^2)).
a(n) = 2^(n+1) - 1 for n even.
a(n) = 2^(n+1) - 2^((n+1)/2) for n odd.
a(n) = 2*a(n-1) + 3*a(n-2) - 6*a(n-3) - 2*a(n-4) + 4*a(n-5) for n>4.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule (Rule 773
  turns an OFF cell with no ON neighbor ON). The entry's program runs on a finite torus of side
  2*128+1, which agrees with the plane for the stages listed.
* Counting convention: as the name says, a(n) reads the diagonal cells (n,n), ..., (1,1), (0,0)
  of stage n as binary digits, the corner most significant, and gives the value. The listed
  terms are those of the diagonal. The entry's program reads the middle row (Range[i, 2*i-1] of
  the x-axis) with FromDigits in base 10 instead; the definition follows the name and the data.
* The statement is the conjunction of the four conjectures. Since the denominator of the
  generating function has constant term 1, the identity A(x) = N/D for A(x) = Sum_{n >= 0} a(n)
  x^n is stated as A * D = N in the formal power series ring over the integers. The closed forms
  (for odd n, (n+1)/2 is an integer) and the recurrence are stated in the integers.
* Controls from the entry, proved in the proof file: a(0..11) = 1, 2, 7, 12, 31, 56, 127, 240,
  511, 992, 2047, 4032.
-/

namespace OMA.S_oeis_a290234

open PowerSeries

/-- Stage t of the two-dimensional Rule 773 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit 773 ((state t x y).toNat + 2 * ((state t (x - 1) y).toNat +
      (state t (x + 1) y).toNat + (state t x (y - 1)).toNat + (state t x (y + 1)).toNat))

/-- A290234(n): the cells (n,n), ..., (0,0) of stage n as binary digits, corner first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n (k : ℤ) (k : ℤ) then 2 ^ k else 0

/-- Barker's generating function, closed forms and recurrence. -/
theorem main :
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 - 2 * X ^ 2)) =
      1 - 2 * X ^ 3 ∧
    (∀ n : ℕ, n % 2 = 0 → (a n : ℤ) = 2 ^ (n + 1) - 1) ∧
    (∀ n : ℕ, n % 2 = 1 → (a n : ℤ) = 2 ^ (n + 1) - 2 ^ ((n + 1) / 2)) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * a (n - 1) + 3 * a (n - 2) - 6 * a (n - 3) -
      2 * a (n - 4) + 4 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a290234
