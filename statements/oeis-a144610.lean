import Mathlib

/-!
# OEIS A144610: the Sturmian word of slope e is the cutting sequence A085369 of 1/e

Source: https://oeis.org/A144610 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, Jan 13 2009), offset 0: Sturmian word of slope e.
Conjecture: a(n) = A085369(n). - R. J. Mathar, Jan 27 2026
Data: 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, ...
A144595 (N. J. A. Sloane), cited for the details: The Christoffel word (or path) of slope s is
defined as follows. Start at (0,0) in the 2-dimensional integer lattice and move up if possible,
otherwise right, always keeping below or on the line y = s*x. Write down 0 with a horizontal move,
1 for a vertical move. The first move is necessarily horizontal, so the sequence always begins with
0. If s is irrational this is called a Sturmian word. (Its program: ans = [0]; x = 1; y = 0; at
each step, if y + 1 <= s*x append 1 and increase y, else append 0 and increase x.)
A085369 (Gary W. Adamson), offset 1: Cutting sequence for 1/e. Given the line y = (1/e)*x starting
from (0,0) and passing through an array of squares, a "1" denotes an intersection with a vertical
line, while a "0" denotes an intersection with a horizontal line. Data: 1, 1, 0, 1, 1, 1, 0, ...

Formalization notes:
* `pos s m` is the lattice point (x, y) reached after the moves numbered 0, ..., m of the path of
  slope s (move 0 is the first, horizontal move to (1, 0)), and `sturm s n` is the word: 0 for
  move 0, and for n >= 1, 1 when move n goes up (y + 1 <= s x at `pos s (n - 1)`) and 0 otherwise.
* `cut n` is A085369(n) for n >= 1. Along the line y = x/e the crossing of the horizontal line
  y = k (k >= 1) is at x = k e, so it comes after the crossings of the vertical lines
  x = 1, ..., floor(k e) and after the k - 1 earlier horizontal crossings: it is crossing number
  k + floor(k e). Those crossings are the 0s and every other crossing is a 1. (The line meets no
  lattice point, e being irrational, so no crossing is of both kinds.)
* `main` states a(n) = A085369(n) for every n >= 1, where both sequences are defined.
-/

namespace OMA.S_oeis_a144610

/-- The point (x, y) reached by the path of slope s after the moves 0, ..., m: move 0 goes to
(1, 0); then the path moves up when y + 1 <= s x and right otherwise. -/
noncomputable def pos (s : ℝ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | m + 1 =>
    if (((pos s m).2 + 1 : ℕ) : ℝ) ≤ s * (pos s m).1 then ((pos s m).1, (pos s m).2 + 1)
    else ((pos s m).1 + 1, (pos s m).2)

/-- The Christoffel (Sturmian) word of slope s: 0 for the first move, then 1 for an up move and
0 for a right move. -/
noncomputable def sturm (s : ℝ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => if (((pos s m).2 + 1 : ℕ) : ℝ) ≤ s * (pos s m).1 then 1 else 0

open Classical in
/-- A085369(n), the cutting sequence of the line y = x/e: crossing number n is horizontal (a 0)
exactly when n = k + floor(k e) for some k >= 1. -/
noncomputable def cut (n : ℕ) : ℕ :=
  if ∃ k : ℕ, 1 ≤ k ∧ n = k + ⌊(k : ℝ) * Real.exp 1⌋₊ then 0 else 1

/-- The conjecture (R. J. Mathar): A144610(n) = A085369(n) for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → sturm (Real.exp 1) n = cut n := by
  sorry

end OMA.S_oeis_a144610
