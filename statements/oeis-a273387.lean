import Mathlib

/-!
# OEIS A273387: Barker's closed form, recurrence and g.f. for Rule 659

Source: https://oeis.org/A273387 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A273387 (Robert Price, May 21 2016), offset 0: First differences of number of active (ON,
black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 659,
based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, May 21 2016:
a(n) = 8*(1+n) for n>2.
a(n) = 2*a(n-1)-a(n-2) for n>4.
G.f.: 4*(1+x+3*x^2-5*x^3+2*x^4) / (1-x)^2.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 659
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Counting convention: a(n) is the number of ON cells of stage n + 1 in [-(n+1), n+1]^2 minus the
  number of ON cells of stage n in [-n, n]^2, as an integer, the part of the grid the entry's
  program keeps (it trims each stage s to the square [-s, s]^2, Range[k+1-n, k-1+n]).
* The statement is the conjunction of the 3 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed form is stated in the rationals, where every
  division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power
  series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero constant
  term.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..16 equal to
  the entry's first 17 terms, 4, 12, 32, 32, 40, 48, 56, 64, 72, 80, 88, 96, ....
-/

namespace OMA.S_oeis_a273387

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

/-- A273387(n): the number of ON cells of stage `n + 1` in `[-(n+1), n+1]²` minus that of stage `n` in `[-n, n]²`. -/
def a (n : ℕ) : ℤ :=
  ((∑ x ∈ Finset.range (2 * (n + 1) + 1), ∑ y ∈ Finset.range (2 * (n + 1) + 1), if state (n + 1) ((x : ℤ) - (n + 1 : ℕ), (y : ℤ) - (n + 1 : ℕ)) then 1 else 0 : ℕ) : ℤ) - ((∑ x ∈ Finset.range (2 * n + 1), ∑ y ∈ Finset.range (2 * n + 1), if state n ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0 : ℕ) : ℤ)

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℚ) = 8 * (1 + n)) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) ∧
    A = (4 * (1 + X + 3 * X ^ 2 - 5 * X ^ 3 + 2 * X ^ 4)) * ((1 - X) ^ 2)⁻¹ := by
  sorry

end OMA.S_oeis_a273387
