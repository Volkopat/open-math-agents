import Mathlib

/-!
# OEIS A290836: Barker's closed form, recurrence and g.f. for the diagonal of the 2D Rule 969

Source: https://oeis.org/A290836 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A290836 (Robert Price, Aug 11 2017), offset 0: Decimal representation of the diagonal from the
corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton defined
by Rule 969, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, Aug 12 2017:
G.f.: (1 - x + x^2 + 4*x^3 - 7*x^4 + 9*x^5 - 6*x^6) / ((1 - x)*(1 - 2*x)).
a(n) = 2^(1+n) - 1 for n>4.
a(n) = 3*a(n-1) - 2*a(n-2) for n>6.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 969
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Reading convention: a(n) reads the diagonal cells (n, n), ..., (0, 0) of stage n as a binary
  number, the corner most significant, as the name says; the listed terms follow this reading
  (controls below), while the program printed in the entry takes the cells of the middle row
  instead.
* The statement is the conjunction of the 3 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed form is stated in the rationals, where every
  division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power
  series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero constant
  term.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..20 equal to
  the entry's first 21 terms, 1, 2, 5, 15, 28, 63, 127, 255, 511, 1023, 2047, 4095, ....
-/

namespace OMA.S_oeis_a290836

open PowerSeries

/-- Rule 969: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 969). -/
def rule (c : Bool) (k : ℕ) : Bool := (969 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A290836(n): the diagonal cells `(n,n), ..., (0,0)` of stage `n` (corner first) read as a binary number. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ), (k : ℤ)) then 2 ^ k else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    A = (1 - X + X ^ 2 + 4 * X ^ 3 - 7 * X ^ 4 + 9 * X ^ 5 - 6 * X ^ 6) *
      ((1 - X) * (1 - 2 * X))⁻¹ ∧
    (∀ n : ℕ, 4 < n → (a n : ℚ) = 2 ^ (1 + n) - 1) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2)) := by
  sorry

end OMA.S_oeis_a290836
