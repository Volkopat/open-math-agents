import Mathlib

/-!
# OEIS A286773: Barker's closed forms, recurrence and g.f. for the diagonal of the 2D Rule 221

Source: https://oeis.org/A286773 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A286773 (Robert Price, May 14 2017), offset 0: Decimal representation of the diagonal from the
origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton defined
by Rule 221, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, May 15 2017:
G.f.: (1 - x - 3*x^2 + 8*x^3 + 4*x^4 - 8*x^5) / ((1 - x)*(1 + x)*(1 - 2*x)).
a(n) = 2^n for n>2 and even.
a(n) = 2^n - 1 for n>2 and odd.
a(n) = 2*a(n-1) + a(n-2) - 2*a(n-3) for n>5.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 221
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Reading convention: a(n) reads the diagonal cells (0, 0), ..., (n, n) of stage n as a binary
  number, the origin most significant, as the name says; the listed terms follow this reading
  (controls below), while the program printed in the entry takes the cells of the middle row
  instead.
* The statement is the conjunction of the 4 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed forms are stated in the rationals, where
  every division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal
  power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero
  constant term.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..19 equal to
  the entry's first 20 terms, 1, 1, 0, 7, 16, 31, 64, 127, 256, 511, 1024, 2047, ....
-/

namespace OMA.S_oeis_a286773

open PowerSeries

/-- Rule 221: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 221). -/
def rule (c : Bool) (k : ℕ) : Bool := (221 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A286773(n): the diagonal cells `(0,0), ..., (n,n)` of stage `n` (origin first) read as a binary number. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ), (k : ℤ)) then 2 ^ (n - k) else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed forms, recurrence and generating function. -/
theorem main :
    A = (1 - X - 3 * X ^ 2 + 8 * X ^ 3 + 4 * X ^ 4 - 8 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 2 * X))⁻¹ ∧
    (∀ n : ℕ, 2 < n → Even n → (a n : ℚ) = 2 ^ n) ∧
    (∀ n : ℕ, 2 < n → Odd n → (a n : ℚ) = 2 ^ n - 1) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a286773
