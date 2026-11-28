import Mathlib

/-!
# OEIS A279872: Wu's recurrence and g.f. for the x-axis of the 2D Rule 209, in base 2

Source: https://oeis.org/A279872 (OEIS Foundation, CC BY-SA 4.0).

Entry A279872 (Robert Price, Dec 21 2016), offset 0: Decimal representation of the x-axis, from the
left edge to the origin, (and also from the origin to the right edge) of the n-th stage of growth
of the two-dimensional cellular automaton defined by Rule 209, based on the 5-celled von Neumann
neighborhood.
Formula section:
Conjectures from Chai Wah Wu, Aug 02 2021:
a(n) = 5*a(n-2) - 4*a(n-4) for n > 3.
G.f.: (2*x^2 + 1)/(4*x^4 - 5*x^2 + 1).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 209
  turns an OFF cell with no ON neighbor ON, and an ON cell with four ON neighbors OFF); the
  entry's program evolves the same rule on a finite grid that wraps around, which agrees with the
  plane at every stage it prints.
* Reading convention: a(n) is the number whose binary digits, from most to least significant, are
  the states (1 = ON, 0 = OFF) of the cells (-n, 0), ..., (0, 0) of stage n, the left edge first,
  as the entry's program does (the middle row of the trimmed stage, from the left edge to the
  center, FromDigits in base 2). The name says the reading from the origin to the right edge
  gives the same numbers; the statement uses the first reading.
* The statement is the conjunction of the 2 conjectures of the site's problem, in the entry's
  order. The recurrence is stated in the integers, for every n > 3. The generating function is
  A(x) = Sum_{n >= 0} a(n) x^n in the formal power series ring over the rationals, and the identity
  is A = N * D⁻¹, where D has a nonzero constant term.
* The definition reproduces the entry's data: a(n) for n = 0..41 agrees with the 42 listed terms
  1, 0, 7, 0, 31, 0, 127, ... (checked by simulating the automaton; not part of the
  statement).
* The entry's comment that the nonzero bisection appears to be A083420 (Tom Copeland) is not
  among the conjectures of the site's problem and is not stated.
-/

namespace OMA.S_oeis_a279872

open PowerSeries

/-- Rule 209: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 209). -/
def rule (c : Bool) (k : ℕ) : Bool := (209 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A279872(n): the cells `(-n,0), ..., (0,0)` of stage `n` (left edge first) read as the binary
digits of a number. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ) - n, 0) then 2 ^ (n - k) else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Wu's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) ∧
    A = (2 * X ^ 2 + 1) * (4 * X ^ 4 - 5 * X ^ 2 + 1)⁻¹ := by
  sorry

end OMA.S_oeis_a279872
