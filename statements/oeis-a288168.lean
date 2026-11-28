import Mathlib

/-!
# OEIS A288168: -1 < 6/5 - a(n)/n < 1

Source: https://oeis.org/A288168 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 07 2017), offset 1: Positions of 0 in A288167; complement of A288169.
Conjecture: -1 < 6/5 - a(n)/n < 1 for n >= 1. Data: 1, 2, 4, 5, 6, 7, 8, 9, ...
A288167 (Clark Kimberling, Jun 07 2017), offset 1: Fixed point of the mapping 00->0010, 1->000,
starting with 00. Its iterates, starting with 00: 00, 0010, 00100000, 0010000001000100, ...
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 0010, 1 -> 000}] with w[0] = 00.

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 0010 and 1 -> 000 over a finite word:
  read from the left, where 00 starts it is replaced by 0010, a letter 1 is replaced by 000, and
  any other letter (a 0 not followed by 0) is copied. The two left sides start with different
  letters, so the order in which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. Each iterate is a prefix of the
  next and iterate n has at least 2n + 2 letters (lemmas `iter_prefix_succ` and `iter_length` of
  the proof), so `W i`, letter i of iterate i + 1, is letter i of every iterate long enough to have
  one: `W` is the fixed point A288167, indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 0 of `W`, so positions count from 1 as in the
  entry; `Nat.nth` counts its argument from 0.
* `main` states the conjecture of the excerpt for every n >= 1, with a(n)/n a real quotient.
-/

namespace OMA.S_oeis_a288168

/-- One pass of StringReplace with the rules 00 -> 0010 and 1 -> 000 over a finite word, read
from the left: where 00 starts it is replaced by 0010, a letter 1 is replaced by 000, and any
other letter is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 0 :: 0 :: 1 :: 0 :: step l
  | 1 :: l => 0 :: 0 :: 0 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A288167 (0-indexed): the fixed point of the mapping, the infinite word of which every iterate
is a prefix; its letter i is read off iterate i + 1, which has more than i letters. -/
def W (i : ℕ) : ℕ := (iter (i + 1)).getD i 0

/-- A288168(n): the position, counted from 1 as in the entry, of the n-th 0 of A288167. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 0) (n - 1) + 1

/-- Kimberling's conjecture: -1 < 6/5 - a(n)/n < 1 for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → -1 < 6 / 5 - (a n : ℝ) / n ∧ 6 / 5 - (a n : ℝ) / n < 1 := by
  sorry

end OMA.S_oeis_a288168
