import Mathlib

/-!
# OEIS A283505: Barker's closed form, recurrence and g.f. for the x-axis of the 2D Rule 641

Source: https://oeis.org/A283505 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A283505 (Robert Price, Mar 09 2017), offset 0: Binary representation of the x-axis, from the
origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 641, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, Mar 10 2017:
G.f.: (1 - x + x^2 + 10*x^3) / ((1 - x)*(1 - 10*x)*(1 + 10*x)).
a(n) = -1/9 + (-5)^n*2^(n-1) + 23*2^n*5^(n-1)/9 for n>1.
a(n) = a(n-1) + 100*a(n-2) - 100*a(n-3) for n>3.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 641
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Reading convention: a(n) writes the cells (0, 0), ..., (n, 0) of stage n (origin first) as binary
  digits and reads them as a decimal number, as the entry's program does (the middle row of the
  trimmed stage, from the center to the right edge, FromDigits).
* The statement is the conjunction of the 3 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed form is stated in the rationals, where every
  division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power
  series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero constant
  term.
* In exponents, n - k is natural-number subtraction; it is exact in the stated range.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..16 equal to
  the entry's first 17 terms, 1, 0, 101, 11, 10111, 1111, 1011111, 111111, 101111111, 11111111,
  10111111111, 1111111111, ....
-/

namespace OMA.S_oeis_a283505

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

/-- A283505(n): the cells `(0,0), ..., (n,0)` of stage `n` (origin first) as binary digits read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ), 0) then 10 ^ (n - k) else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    A = (1 - X + X ^ 2 + 10 * X ^ 3) * ((1 - X) * (1 - 10 * X) * (1 + 10 * X))⁻¹ ∧
    (∀ n : ℕ, 1 < n → (a n : ℚ) = -1 / 9 + (-5) ^ n * 2 ^ (n - 1) + 23 * 2 ^ n * 5 ^ (n - 1) / 9) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a283505
