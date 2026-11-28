import Mathlib

/-!
# OEIS A290828: Barker's closed forms, recurrence and g.f. for the diagonal of the 2D Rule 961

Source: https://oeis.org/A290828 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A290828 (Robert Price, Aug 11 2017), offset 0: Decimal representation of the diagonal from the
corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton defined
by Rule 961, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, Aug 12 2017:
G.f.: (1 + 5*x^3 - 3*x^4 + 2*x^5) / ((1 - x)*(1 + x)*(1 - 2*x)).
a(n) = 2*(2^n - 2) for n>2 and even.
a(n) = 2^(n+1) - 1 for n>2 and odd.
a(n) = 2*a(n-1) + a(n-2) - 2*a(n-3) for n>5.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 961
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Reading convention: a(n) reads the diagonal cells (n, n), ..., (0, 0) of stage n as a binary
  number, the corner most significant, as the name says; the listed terms follow this reading
  (controls below), while the program printed in the entry takes the cells of the middle row
  instead.
* The statement is the conjunction of the 4 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed forms are stated in the rationals, where
  every division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal
  power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero
  constant term.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..19 equal to
  the entry's first 20 terms, 1, 2, 5, 15, 28, 63, 124, 255, 508, 1023, 2044, 4095, ....
-/

namespace OMA.S_oeis_a290828

open PowerSeries

/-- Rule 961: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 961). -/
def rule (c : Bool) (k : ℕ) : Bool := (961 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A290828(n): the diagonal cells `(n,n), ..., (0,0)` of stage `n` (corner first) read as a binary number. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ), (k : ℤ)) then 2 ^ k else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed forms, recurrence and generating function. -/
theorem main :
    A = (1 + 5 * X ^ 3 - 3 * X ^ 4 + 2 * X ^ 5) * ((1 - X) * (1 + X) * (1 - 2 * X))⁻¹ ∧
    (∀ n : ℕ, 2 < n → Even n → (a n : ℚ) = 2 * (2 ^ n - 2)) ∧
    (∀ n : ℕ, 2 < n → Odd n → (a n : ℚ) = 2 ^ (n + 1) - 1) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a290828
