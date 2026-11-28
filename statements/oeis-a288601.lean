import Mathlib

/-!
# OEIS A288601: a(n)/n -> 2 and -1 < 2 - a(n)/n < 1 for n >= 2

Source: https://oeis.org/A288601 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 14 2017), offset 1: Positions of 0 in A288600; complement of A288602.
Conjecture: a(n)/n -> 2, and -1 < 2 - a(n)/n < 1 for n >= 2. Data: 1, 3, 4, 6, 8, 9, 12, 13, ...
A288600 (Clark Kimberling, Jun 14 2017), offset 1: Fixed point of the mapping 00->0101, 10->1001,
starting with 00. Its iterates, starting with 00: 00, 0101, 010011, 01001011, 010010100111, ...
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 0101, 10 -> 1001}] with w[0] = 00.

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 0101 and 10 -> 1001 over a finite
  word: read from the left, where 00 starts it is replaced by 0101, where 10 starts it is replaced
  by 1001, and any other letter is copied. The two left sides start with different letters, so the
  order in which the rules are tried does not matter. The program printed in A288601 writes the
  second rule as 1 -> 1001, but the name and program of A288600 and the data of both entries are
  those of 10 -> 1001.
* `iter n` is the n-th iterate, starting with 00 as in the entry. The iterates are not nested (the
  last letter changes), but each iterate without its last letter is a prefix of the next (lemma
  `iter_dropLast_prefix` of the proof), and letter i is the same in every iterate with more than
  i + 1 letters (lemma `iter_stable`). `W i` reads it off iterate i + 2, which has more than i + 1
  letters, so `W` is the fixed point A288600, indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 0 of `W`, so positions count from 1 as in the
  entry; `Nat.nth` counts its argument from 0.
* `main` is the conjunction of both statements of the excerpt: a(n)/n tends to 2 as a limit of
  real numbers, and -1 < 2 - a(n)/n < 1 for every n >= 2, with a(n)/n a real quotient.
-/

namespace OMA.S_oeis_a288601

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 0101 and 10 -> 1001 over a finite word, read
from the left: where 00 starts it is replaced by 0101, where 10 starts it is replaced by 1001,
and any other letter is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 0 :: 1 :: 0 :: 1 :: step l
  | 1 :: 0 :: l => 1 :: 0 :: 0 :: 1 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A288600 (0-indexed): the fixed point of the mapping, the limit of the iterates. Each iterate
without its last letter is a prefix of the next, so letter i is the same in every iterate with
more than i + 1 letters; it is read off iterate i + 2, which has more than i + 1 letters. -/
def W (i : ℕ) : ℕ := (iter (i + 2)).getD i 0

/-- A288601(n): the position, counted from 1 as in the entry, of the n-th 0 of A288600. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 0) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n -> 2, and -1 < 2 - a(n)/n < 1 for n >= 2. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 2) ∧
    ∀ n : ℕ, 2 ≤ n → -1 < 2 - (a n : ℝ) / n ∧ 2 - (a n : ℝ) / n < 1 := by
  sorry

end OMA.S_oeis_a288601
