import Mathlib

/-!
# OEIS A286808: a(n)/n -> 2 and -1 < 2 - a(n)/n < 2

Source: https://oeis.org/A286808 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 06 2017), offset 1: Positions of 0 in A286807; complement of A286809.
Conjecture: a(n)/n-> 2, and -1 < 2 - a(n)/n < 2 for n >= 1. Data: 1, 2, 5, 8, 10, 12, 15, 17, ...
A286807 (Clark Kimberling, Jun 05 2017), offset 1: Fixed point of the mapping 00->001, 1->101,
starting with 00. Its iterates, starting with 00: 00, 001, 001101, 0011011010101, ...
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 001, 1 -> 101}] with w[0] = 00.

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 001 and 1 -> 101 over a finite word:
  read from the left, where 00 starts it is replaced by 001, a letter 1 is replaced by 101, and
  any other letter (a 0 not followed by 0) is copied. The two left sides start with different
  letters, so the order in which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. Each iterate is a prefix of the
  next and iterate i + 1 has more than i letters (lemmas `iter_prefix` and `lt_iter_length` of the
  proof), so `W i`, letter i of iterate i + 1, is letter i of every iterate long enough to have
  one: `W` is the fixed point A286807, indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 0 of `W`, so positions count from 1 as in the
  entry; `Nat.nth` counts its argument from 0.
* `main` is the conjunction of both statements of the excerpt: a(n)/n tends to 2 as a limit of
  real numbers, and -1 < 2 - a(n)/n < 2 for every n >= 1, with a(n)/n a real quotient.
-/

namespace OMA.S_oeis_a286808

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 001 and 1 -> 101 over a finite word, read from
the left: where 00 starts it is replaced by 001, a letter 1 is replaced by 101, and any other
letter is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 0 :: 0 :: 1 :: step l
  | 1 :: l => 1 :: 0 :: 1 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A286807 (0-indexed): the fixed point of the mapping, the infinite word of which every iterate
is a prefix; its letter i is read off iterate i + 1, which has more than i letters. -/
def W (i : ℕ) : ℕ := (iter (i + 1)).getD i 0

/-- A286808(n): the position, counted from 1 as in the entry, of the n-th 0 of A286807. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 0) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n -> 2, and -1 < 2 - a(n)/n < 2 for n >= 1. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 2) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < 2 - (a n : ℝ) / n ∧ 2 - (a n : ℝ) / n < 2 := by
  sorry

end OMA.S_oeis_a286808
