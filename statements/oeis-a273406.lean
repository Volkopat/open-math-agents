import Mathlib

/-!
# OEIS A273406: Barker's closed forms, recurrence and g.f. for the partial sums of the 2D Rule 673

Source: https://oeis.org/A273406 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A273406 (Robert Price, May 21 2016), offset 0: Partial sums of the number of active (ON,
black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 673,
based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, May 22 2016:
a(n) = (9+3*(-1)^n-10*n+48*n^2+16*n^3)/12.
a(n) = (8*n^3+24*n^2-5*n+6)/6 for n even.
a(n) = (8*n^3+24*n^2-5*n+3)/6 for n odd.
a(n) = 3*a(n-1)-2*a(n-2)-2*a(n-3)+3*a(n-4)-a(n-5) for n>4.
G.f.: (1+2*x+13*x^2+4*x^3-4*x^4) / ((1-x)^4*(1+x)).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 673
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Counting convention: a(n) is the sum over the stages s = 0..n of the number of ON cells of stage s
  in the square [-s, s]^2, the part of the grid the entry's program keeps (it trims each stage s to
  the square [-s, s]^2, Range[k+1-n, k-1+n]).
* The statement is the conjunction of the 5 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed forms are stated in the rationals, where
  every division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal
  power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero
  constant term.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..19 equal to
  the entry's first 20 terms, 1, 5, 26, 70, 147, 263, 428, 648, 933, 1289, 1726, 2250, ....
-/

namespace OMA.S_oeis_a273406

open PowerSeries

/-- Rule 673: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 673). -/
def rule (c : Bool) (k : ℕ) : Bool := (673 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A273406(n): the sum over the stages `s = 0..n` of the number of ON cells of stage `s` in the square `[-s, s]²`. -/
def a (n : ℕ) : ℕ :=
  ∑ s ∈ Finset.range (n + 1), ∑ x ∈ Finset.range (2 * s + 1), ∑ y ∈ Finset.range (2 * s + 1), if state s ((x : ℤ) - s, (y : ℤ) - s) then 1 else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed forms, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, (a n : ℚ) = (9 + 3 * (-1) ^ n - 10 * n + 48 * n ^ 2 + 16 * n ^ 3) / 12) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = (8 * n ^ 3 + 24 * n ^ 2 - 5 * n + 6) / 6) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = (8 * n ^ 3 + 24 * n ^ 2 - 5 * n + 3) / 6) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2) - 2 * a (n - 3) + 3 * a (n - 4) - a (n - 5)) ∧
    A = (1 + 2 * X + 13 * X ^ 2 + 4 * X ^ 3 - 4 * X ^ 4) * ((1 - X) ^ 4 * (1 + X))⁻¹ := by
  sorry

end OMA.S_oeis_a273406
