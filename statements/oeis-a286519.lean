import Mathlib

/-!
# OEIS A286519: Barker's closed form, recurrence and g.f. for the diagonal of the 2D Rule 659

Source: https://oeis.org/A286519 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A286519 (Robert Price, Jul 22 2017), offset 0: Binary representation of the diagonal from the
origin to the corner (or of the corner to the origin) of the n-th stage of growth of the
two-dimensional cellular automaton defined by Rule 659, based on the 5-celled von Neumann
neighborhood.
Formula section:
Conjectures from Colin Barker, Jul 22 2017:
G.f.: (1 - 10*x^2 + 110*x^3 - 100*x^4) / ((1 - x)*(1 - 10*x)).
a(n) = (10^(1+n) - 1) / 9 for n>2.
a(n) = 11*a(n-1) - 10*a(n-2) for n>4.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 659
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Reading convention: a(n) writes the diagonal cells (0, 0), ..., (n, n) of stage n (origin first)
  as binary digits and reads them as a decimal number, as the name says; the listed terms follow
  this reading (controls below), while the program printed in the entry takes the cells of the
  middle row instead.
* The name offers two readings (from the origin to the corner, or from the corner to the origin);
  the statement uses the first. The two give the same numbers wherever they were compared: the digit
  string of each stage is a palindrome for n <= 150 (simulation, not part of the proof).
* The statement is the conjunction of the 3 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed form is stated in the rationals, where every
  division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power
  series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero constant
  term.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..16 equal to
  the entry's first 17 terms, 1, 11, 101, 1111, 11111, 111111, 1111111, 11111111, 111111111,
  1111111111, 11111111111, 111111111111, ....
-/

namespace OMA.S_oeis_a286519

open PowerSeries

/-- Rule 659: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 659). -/
def rule (c : Bool) (k : ℕ) : Bool := (659 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A286519(n): the diagonal cells `(0,0), ..., (n,n)` of stage `n` (origin first) as binary digits read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ), (k : ℤ)) then 10 ^ (n - k) else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    A = (1 - 10 * X ^ 2 + 110 * X ^ 3 - 100 * X ^ 4) * ((1 - X) * (1 - 10 * X))⁻¹ ∧
    (∀ n : ℕ, 2 < n → (a n : ℚ) = (10 ^ (1 + n) - 1) / 9) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2)) := by
  sorry

end OMA.S_oeis_a286519
