import Mathlib

/-!
# OEIS A283648: Barker's g.f., closed forms and recurrence for the x-axis of Rule 705

Source: https://oeis.org/A283648 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Mar 12 2017), offset 0: Binary representation of the x-axis, from the left
edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined
by 'Rule 705', based on the 5-celled von Neumann neighborhood. Comment: Initialized with a single
black (ON) cell at stage zero. The formula section states: Conjectures from Colin Barker, Mar 14
2017: (Start) G.f.: (1 - 10*x + 110*x^2 + x^3 - 21*x^4 + 110*x^5) / ((1 - x)*(1 + x)*(1 - 10*x)).
a(n) = 10*(10^n - 10)/9 for n>2 and even. a(n) = (10^(n+1) - 91)/9 for n>2 and odd. a(n) =
10*a(n-1) + a(n-2) - 10*a(n-3) for n>5. (End)

Formalization notes:
* Conventions (Wolfram's outer totalistic numbering, as in the entry's Mathematica program, whose
  step reads bit 2k + c of the code): a cell in state c with k ON von Neumann neighbors becomes
  bit 2k + c of 705. The automaton runs on Z x Z from one ON cell at the origin on an all-OFF
  background, and the rule is applied to every cell, including the background. (The program
  evolves a finite grid with wrap-around; the definition below is the automaton on the plane.)
* a(n) is the cells (-n, 0), ..., (0, 0) after n steps, read as the digits of a number in base 10,
  the left edge most significant.
* `main` is the conjunction of the four conjectures. The closed forms are stated in Q, the
  recurrence in the integers, and the g.f. as A(x) = N(x) * D(x)^(-1) in Q[[x]] (D has constant
  term 1).
* Controls: the definitions give a(0..5) = 1, 0, 111, 1101, 11100, 111101, as in the entry.
-/

namespace OMA.S_oeis_a283648

/-- Rule 705: new state from the cell's state and its number of ON neighbors. -/
def rule (c : Bool) (k : ℕ) : Bool := (705 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A283648(n): cells `(-n,0), ..., (0,0)` as binary digits in base 10, left edge first. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ) - n, 0) then 10 ^ (n - k) else 0

open PowerSeries in
/-- Barker's conjectures: the g.f., the two closed forms for n > 2, and the recurrence for n > 5. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 - 10 * X + 110 * X ^ 2 + X ^ 3 - 21 * X ^ 4 + 110 * X ^ 5) *
        ((1 - X) * (1 + X) * (1 - 10 * X))⁻¹ ∧
    (∀ n : ℕ, 2 < n → n % 2 = 0 → (a n : ℚ) = 10 * (10 ^ n - 10) / 9) ∧
    (∀ n : ℕ, 2 < n → n % 2 = 1 → (a n : ℚ) = (10 ^ (n + 1) - 91) / 9) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a283648
