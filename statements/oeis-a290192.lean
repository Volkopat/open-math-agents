import Mathlib

/-!
# OEIS A290192: Wu's recurrence and generating function for the diagonal of the 2D Rule 705

Source: https://oeis.org/A290192 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A290192 (Robert Price, Jul 23 2017), offset 0: Binary representation of the diagonal from the
corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton defined
by Rule 705, based on the 5-celled von Neumann neighborhood.
Formula section:
From Chai Wah Wu, Nov 01 2018:
a(n) = 10*a(n-1) + a(n-2) - 10*a(n-3) for n > 5 (conjectured).
G.f.: (10*x^5 + 89*x^4 + 91*x^3 + 1)/((x - 1)*(x + 1)*(10*x - 1)) (conjectured).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 705
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Reading convention: a(n) writes the diagonal cells (n, n), ..., (0, 0) of stage n (corner first)
  as binary digits and reads them as a decimal number, as the name says; the listed terms follow
  this reading (controls below), while the program printed in the entry takes the cells of the
  middle row instead.
* The statement is the conjunction of the 2 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n
  in the formal power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a
  nonzero constant term.
* Not part of the site's problem, so not stated here: the formula line G.f.: (10*x^5 + 89*x^4 +
  91*x^3 + 1)/((x - 1)*(x + 1)*(10*x .
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..17 equal to
  the entry's first 18 terms, 1, 10, 101, 1101, 11100, 111101, 1111100, 11111101, 111111100,
  1111111101, 11111111100, 111111111101, ....
-/

namespace OMA.S_oeis_a290192

open PowerSeries

/-- Rule 705: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 705). -/
def rule (c : Bool) (k : ℕ) : Bool := (705 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A290192(n): the diagonal cells `(n,n), ..., (0,0)` of stage `n` (corner first) as binary digits read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ), (k : ℤ)) then 10 ^ k else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Wu's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3)) ∧
    A = (10 * X ^ 5 + 89 * X ^ 4 + 91 * X ^ 3 + 1) * ((X - 1) * (X + 1) * (10 * X - 1))⁻¹ := by
  sorry

end OMA.S_oeis_a290192
