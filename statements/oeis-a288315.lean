import Mathlib

/-!
# OEIS A288315: a(n)/n -> m = 1.22..., and -1 < m - a(n)/n < 1

Source: https://oeis.org/A288315 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 09 2017), offset 1: Positions of 0 in A288314; complement of A288316.
Conjecture: a(n)/n-> 1.22..., and if m denotes this number, then -1 < m - a(n)/n < 1 for n >= 1.
Data: 1, 2, 3, 5, 6, 7, 8, 9, 10, 12, 13, 14, ...
A288314 (Clark Kimberling, Jun 09 2017), offset 1: Fixed point of the mapping 00->0001, 1->00,
starting with 00. Data: 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, ...
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 0001, 1 -> 00}] with w[0] = 00, and the word is
read off w[11].

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 0001 and 1 -> 00 over a finite word: read
  from the left, where 00 starts it is replaced by 0001, a letter 1 is replaced by 00, and any other
  letter (a 0 before a 1 or at the end) is copied. The two left sides start with different letters,
  so the order in which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. Each iterate is a prefix of the
  next (lemma `iter_prefix` of the proof: a lone final 0 is copied and 00 -> 0001 begins with 0, so
  a pass maps a prefix of a word to a prefix of its image) and iterate i + 1 has more than i letters
  (lemma `iter_length`), so `W i`, letter i of iterate i + 1, is letter i of the fixed point: `W` is
  A288314, indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 0 of `W`, so positions count from 1 as in the entry;
  `Nat.nth` counts its argument from 0.
* The entry gives the limit only as 1.22..., so `main` asks for a real number m with
  1.22 <= m < 1.23, the numbers whose decimal expansion starts 1.22, such that a(n)/n tends to m as
  a limit of real numbers and -1 < m - a(n)/n < 1 for every n >= 1, with a(n)/n a real quotient.
  This is the conjunction of both parts of the conjecture. The proof takes
  m = (1 + c)/c = 1.22668..., with c = lam^2 + lam - 1 and lam = 2 cos(pi/9) = 1.87938... the
  largest root of x^3 - 3x - 1.
-/

namespace OMA.S_oeis_a288315

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 0001 and 1 -> 00 over a finite word, read
from the left: where 00 starts it is replaced by 0001, a letter 1 is replaced by 00, and any
other letter is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 0 :: 0 :: 0 :: 1 :: step l
  | 1 :: l => 0 :: 0 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A288314 (0-indexed): the fixed point of the mapping, the infinite word of which every iterate
is a prefix; its letter i is read off iterate i + 1, which has more than i letters. -/
def W (i : ℕ) : ℕ := (iter (i + 1)).getD i 0

/-- A288315(n): the position, counted from 1 as in the entry, of the n-th 0 of A288314. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 0) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.22..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem main : ∃ m : ℝ, (1.22 ≤ m ∧ m < 1.23) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  sorry

end OMA.S_oeis_a288315
