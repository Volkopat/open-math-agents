import Mathlib

/-!
# OEIS A287126: a(n)/n -> m = 2.22..., and -2 < m - a(n)/n < 2

Source: https://oeis.org/A287126 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 06 2017), offset 1: Positions of 0 in A287125; complement of A287127.
Conjecture: a(n)/n-> 2.22..., and if m denotes this number, then -2 < m - a(n)/n < 2 for n >= 1.
Data: 1, 2, 6, 9, 12, 13, 16, 19, 20, 23, 26, 27, ...
A287125 (Clark Kimberling, Jun 06 2017), offset 1: Fixed point of the mapping 00->001, 1->110,
starting with 00. Data: 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, ...
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 001, 1 -> 110}] with w[0] = 00.

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 001 and 1 -> 110 over a finite word: read
  from the left, where 00 starts it is replaced by 001, a letter 1 is replaced by 110, and any other
  letter (a 0 not followed by 0) is copied. The two left sides start with different letters, so the
  order in which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. Each iterate is a prefix of the
  next and iterate i + 1 has more than i letters (lemmas `iter_prefix` and `iter_length` of the
  proof), so `W i`, letter i of iterate i + 1, is letter i of the fixed point: `W` is A287125,
  indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 0 of `W`, so positions count from 1 as in the entry;
  `Nat.nth` counts its argument from 0.
* The entry gives the limit only as 2.22..., so `main` asks for a real number m with
  2.22 <= m < 2.23, the numbers whose decimal expansion starts 2.22, such that a(n)/n tends to m as
  a limit of real numbers and -2 < m - a(n)/n < 2 for every n >= 1, with a(n)/n a real quotient.
  This is the conjunction of both parts of the conjecture. The proof takes
  m = 1 + 1/c = lam = 2.22269..., with c = 1/(lam - 1) and lam the root of x^4 - 2x^3 - 2x + 2 in
  [2.22269, 2.2227].
-/

namespace OMA.S_oeis_a287126

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 001 and 1 -> 110 over a finite word, read
from the left: where 00 starts it is replaced by 001, a letter 1 is replaced by 110, and any
other letter is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 0 :: 0 :: 1 :: step l
  | 1 :: l => 1 :: 1 :: 0 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A287125 (0-indexed): the fixed point of the mapping, the infinite word of which every iterate
is a prefix; its letter i is read off iterate i + 1, which has more than i letters. -/
def W (i : ℕ) : ℕ := (iter (i + 1)).getD i 0

/-- A287126(n): the position, counted from 1 as in the entry, of the n-th 0 of A287125. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 0) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n tends to a number m = 2.22..., and -2 < m - a(n)/n < 2
for n >= 1. -/
theorem main : ∃ m : ℝ, (2.22 ≤ m ∧ m < 2.23) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -2 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 2 := by
  sorry

end OMA.S_oeis_a287126
