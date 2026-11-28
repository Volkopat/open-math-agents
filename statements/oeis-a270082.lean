import Mathlib

/-!
# OEIS A270082: Barker's conjectures for the first differences of the ON cells of the 2D Rule 62

Source: https://oeis.org/A270082 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A270082 (Robert Price, Mar 10 2016), offset 0: First differences of number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 62, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, Mar 10 2016: (Start)
a(n) = a(n-2)+a(n-4)-a(n-6) for n>9.
G.f.: (4+7*x+4*x^2+5*x^3+5*x^5-12*x^6-x^7+4*x^8+4*x^9-4*x^11) / ((1-x)^2*(1+x)^2*(1+x^2)).
(End)

Formalization notes:
* Rule numbering, as in the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}} and
  rule[[10 - #]] of IntegerDigits[code, 2, 10]): the new state of a cell is bit 2s + c of the rule
  number, where c is its old state and s is the number of ON cells among its four orthogonal
  neighbors.
* Initial condition: at stage 0 the cell (0, 0) is ON and every other cell of Z x Z is OFF; each
  stage applies the rule to every cell of Z x Z (Rule 62 keeps the background OFF).
* As in the entry's program, stage t counts the ON cells (x, y) with -t <= x, y <= t, and
  a(n) = on(n + 1) - on(n), an integer.
* The statement is the conjunction of Barker's recurrence and generating function, in the
  integers; the identity A(x) = N/D is stated as A * D = N in the formal power series ring over
  the integers (D has constant term 1).
* Controls: the definition gives 4, 7, 8, 12, 12, 24, 4, 28 for n = 0..7 (the entry's data,
  checked by direct simulation).
-/

namespace OMA.S_oeis_a270082

open PowerSeries

/-- The new state of a cell: bit 2s + c of the rule number. -/
def ca (rule : ℕ) (c : Bool) (s : ℕ) : Bool := Nat.testBit rule (2 * s + c.toNat)

/-- Stage t of Rule 62 from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => ca 62 (state t x y)
      ((state t (x - 1) y).toNat + (state t (x + 1) y).toNat +
        (state t x (y - 1)).toNat + (state t x (y + 1)).toNat)

/-- The number of ON cells of stage t with -t <= x, y <= t (x = i - t, y = j - t, i, j <= 2t). -/
def on (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)).filter fun p : ℕ × ℕ =>
    state t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t)).card

/-- A270082(n): the first differences of the ON-cell counts. -/
def a (n : ℕ) : ℤ := (on (n + 1) : ℤ) - on n

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 9 < n → (a n : ℤ) = a (n - 2) + a (n - 4) - a (n - 6)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2)) =
      (4 + 7 * X + 4 * X ^ 2 + 5 * X ^ 3 + 5 * X ^ 5 - 12 * X ^ 6 - X ^ 7 + 4 * X ^ 8 + 4 * X ^ 9 - 4 * X ^ 11 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a270082
