import Mathlib

/-!
# OEIS A273446: Blomberg's conjectures for Rule 721 at the stages 2^n - 1

Source: https://oeis.org/A273446 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, May 22 2016), offset 0: Number of active (ON, black) cells at stage 2^n-1 of
the two-dimensional cellular automaton defined by 'Rule 721', based on the 5-celled von Neumann
neighborhood. Comments: Initialized with a single black (ON) cell at stage zero. Conjecture: Rule
729 also generates this sequence. - Lars Blomberg, Jul 19 2016. The formula section states:
Conjecture: a(n) = 4*4^n - 4*2^n, n>2. - Lars Blomberg, Jul 19 2016

Formalization notes:
* Conventions (Wolfram's outer totalistic numbering, as in the entry's Mathematica program, whose
  step reads bit 2k + c of the code): under Rule N a cell in state c with k ON von Neumann
  neighbors becomes bit 2k + c of N. The automaton runs on Z x Z from one ON cell at the origin on
  an all-OFF background, and the rule is applied to every cell, including the background. (The
  program evolves a finite grid with wrap-around; the definition below is the automaton on the
  plane.)
* As in the program, stage s is counted in the central (2s+1) x (2s+1) square: `count N s` is the
  number of ON cells there after s steps of Rule N, and a(n) = count 721 (2^n - 1).
* Rule 729 generates this sequence means that the same count for Rule 729 at the stages 2^n - 1
  equals a(n) for every n.
* `main` is the conjunction of both conjectures.
* Controls: the definitions give a(0..2) = 1, 4, 41, as in the entry.
-/

namespace OMA.S_oeis_a273446

/-- Outer totalistic rule `N`: new state from the cell's state and its number of ON neighbors. -/
def rule (N : ℕ) (c : Bool) (k : ℕ) : Bool := N.testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- Rule `N` on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state (N : ℕ) : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule N (state N t p) ((nbrs p).countP (fun q => state N t q))

/-- ON cells of stage `s` in the central `(2s+1) x (2s+1)` square. -/
noncomputable def count (N s : ℕ) : ℕ :=
  ((Finset.Icc (-(s : ℤ)) s ×ˢ Finset.Icc (-(s : ℤ)) s).filter (fun p => state N s p)).card

/-- A273446(n): ON cells of Rule 721 at stage `2^n - 1`. -/
noncomputable def a (n : ℕ) : ℕ := count 721 (2 ^ n - 1)

/-- Blomberg's conjectures: Rule 729 gives the same sequence, and a(n) = 4*4^n - 4*2^n for n > 2. -/
theorem main :
    (∀ n : ℕ, count 729 (2 ^ n - 1) = a n) ∧
    (∀ n : ℕ, 2 < n → a n = 4 * 4 ^ n - 4 * 2 ^ n) := by
  sorry

end OMA.S_oeis_a273446
