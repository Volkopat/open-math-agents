import Mathlib

/-!
# OEIS A285474: Barker's closed form, recurrence and g.f. for the diagonal of the 2D Rule 3

Source: https://oeis.org/A285474 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A285474 (Robert Price, Apr 19 2017), offset 0: Binary representation of the diagonal from the
origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton defined
by Rule 3, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, Apr 19 2017:
G.f.: (1 + 11*x - x^2) / ((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)).
a(n) = (-1 - (-10)^n + (-1)^n + 19*10^n)/18.
a(n) = 101*a(n-2) - 100*a(n-4) for n>3.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 3 turns
  an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite grid.
* Reading convention: a(n) writes the diagonal cells (0, 0), ..., (n, n) of stage n (origin first)
  as binary digits and reads them as a decimal number, as the name says; the listed terms follow
  this reading (controls below), while the program printed in the entry takes the cells of the
  middle row instead.
* The statement is the conjunction of the 3 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed form is stated in the rationals, where every
  division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power
  series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero constant
  term.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..16 equal to
  the entry's first 17 terms, 1, 11, 100, 1111, 10000, 111111, 1000000, 11111111, 100000000,
  1111111111, 10000000000, 111111111111, ....
-/

namespace OMA.S_oeis_a285474

open PowerSeries

/-- Rule 3: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 3). -/
def rule (c : Bool) (k : ℕ) : Bool := (3 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A285474(n): the diagonal cells `(0,0), ..., (n,n)` of stage `n` (origin first) as binary digits read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ), (k : ℤ)) then 10 ^ (n - k) else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    A = (1 + 11 * X - X ^ 2) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X))⁻¹ ∧
    (∀ n : ℕ, (a n : ℚ) = (-1 - (-10) ^ n + (-1) ^ n + 19 * 10 ^ n) / 18) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 101 * a (n - 2) - 100 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a285474
