import Mathlib

/-!
# OEIS A283506: Barker's closed forms, recurrence and g.f. for the x-axis of the 2D Rule 641

Source: https://oeis.org/A283506 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A283506 (Robert Price, Mar 09 2017), offset 0: Decimal representation of the x-axis, from the
left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 641, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, Mar 10 2017:
G.f.: (1 - 2*x + 4*x^2 + 4*x^3) / ((1 - x)*(1 + x)*(1 - 2*x)).
a(n) = 2^(n+1) - 3 for n>0 and even.
a(n) = 2^(n+1) - 4 for n odd.
a(n) = 2*a(n-1) + a(n-2) - 2*a(n-3) for n>3.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 641
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Reading convention: a(n) reads the cells (-n, 0), ..., (0, 0) of stage n as a binary number, the
  left edge most significant, as the entry's program does (the middle row of the trimmed stage, from
  the left edge to the center, FromDigits).
* The statement is the conjunction of the 4 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed forms are stated in the rationals, where
  every division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal
  power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero
  constant term.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..16 equal to
  the entry's first 17 terms, 1, 0, 5, 12, 29, 60, 125, 252, 509, 1020, 2045, 4092, ....
-/

namespace OMA.S_oeis_a283506

open PowerSeries

/-- Rule 641: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 641). -/
def rule (c : Bool) (k : ℕ) : Bool := (641 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A283506(n): the cells `(-n,0), ..., (0,0)` of stage `n` (left edge first) read as a binary number. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ) - n, 0) then 2 ^ (n - k) else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed forms, recurrence and generating function. -/
theorem main :
    A = (1 - 2 * X + 4 * X ^ 2 + 4 * X ^ 3) * ((1 - X) * (1 + X) * (1 - 2 * X))⁻¹ ∧
    (∀ n : ℕ, 0 < n → Even n → (a n : ℚ) = 2 ^ (n + 1) - 3) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = 2 ^ (n + 1) - 4) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a283506
