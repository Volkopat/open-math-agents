import Mathlib

/-!
# OEIS A277560: Barker's recurrence and g.f. for the x-axis of the 2D Rule 7, in base 10

Source: https://oeis.org/A277560 (OEIS Foundation, CC BY-SA 4.0).

Entry A277560 (Robert Price, Nov 05 2016), offset 0: Binary representation of the x-axis, from the
left edge to the origin, or from the origin to the right edge, of the n-th stage of growth of the
two-dimensional cellular automaton defined by Rule 7, based on the 5-celled von Neumann
neighborhood.
Formula section:
Conjectures from Colin Barker, Nov 06 2016:
G.f.: (1 + 11*x - 101*x^2 + 100*x^4)/((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)).
a(n) = 101*a(n-2) - 100*a(n-4) for n>4.
a(n) = (-1)*(-1 + (-1)^n)*(-1 - 10^n)/18 for n>0.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 7 turns
  an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite grid.
* Reading convention: a(n) is the number whose decimal digits, from most to least significant, are
  the states (1 = ON, 0 = OFF) of the cells (-n, 0), ..., (0, 0) of stage n, the left edge first,
  as the entry's program does (the middle row of the trimmed stage, from the left edge to the
  center, FromDigits in base 10). The name offers two readings (from the left edge to the origin,
  or from the origin to the right edge); the statement uses the first.
* The statement is the conjunction of the g.f. and the recurrence, in the entry's order. The
  recurrence is stated in the integers, for every n > 4. The generating function is
  A(x) = Sum_{n >= 0} a(n) x^n in the formal power series ring over the rationals, and the identity
  is A = N * D⁻¹, where D has a nonzero constant term.
* The third conjecture, the closed form a(n) = (-1)*(-1 + (-1)^n)*(-1 - 10^n)/18 for n > 0, is not
  stated: as printed it is false. At n = 1 it gives (-1)(-2)(-11)/18 = -11/9, while a(1) = 11 is
  the entry's second term; at every odd n it is negative, and the data are not. (The evidently
  intended form, with -1 + 10^(n+1) in place of -1 - 10^n, follows from the g.f.) Stating the
  printed form would make the whole conjunction false for a typographical reason.
* The definition reproduces the entry's data: a(n) for n = 0..26 agrees with the 27 listed terms
  1, 11, 0, 1111, 0, 111111, ... (checked by simulating the automaton; not part of the statement).
-/

namespace OMA.S_oeis_a277560

open PowerSeries

/-- Rule 7: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 7). -/
def rule (c : Bool) (k : ℕ) : Bool := (7 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A277560(n): the cells `(-n,0), ..., (0,0)` of stage `n` (left edge first) read as the decimal
digits of a number. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ) - n, 0) then 10 ^ (n - k) else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's generating function and recurrence. -/
theorem main :
    A = (1 + 11 * X - 101 * X ^ 2 + 100 * X ^ 4) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X))⁻¹ ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 101 * a (n - 2) - 100 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a277560
