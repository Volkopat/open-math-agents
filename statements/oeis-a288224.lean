import Mathlib

/-!
# OEIS A288224: a(n)/n -> m = 1.38..., and -1 < m - a(n)/n < 1

Source: https://oeis.org/A288224 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 19 2017), offset 1: Positions of 0 in A288223; complement of A288225.
Conjecture: a(n)/n -> 1.38..., and if m denotes this number, then -1 < m - a(n)/n < 1 for n >= 1.
Data: 1, 3, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, ...
A288223 (Clark Kimberling, 2017), offset 1: 2-limiting word of the mapping 00->1000, 10->010,
starting with 00. Iterates of the mapping, starting with 00: 00, 1000, 0101000, 00100101000,
100001000100101000, ... The 2-limiting word is the limit of the n-th iterates for n == 2 mod 3.
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 1000, 10 -> 010}] with w[0] = 00.

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 1000 and 10 -> 010 over a finite word:
  read from the left, where 00 starts it is replaced by 1000, where 10 starts it is replaced by
  010, and any other letter is copied. The two left sides start with different letters, so the
  order in which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. The iterates converge only
  along each residue of n mod 3; the 2-limiting word is the limit of `iter (3k + 2)`. Letter i
  is the same in every iterate 3k + 2 with k >= i + 1 (lemmas `stable` and `W_eq` of the proof:
  iterate 3(k + 1) + 2 begins with a word Q_m of more than m + 2 letters for every m <= k + 1, and
  Q_m is a prefix of Q_(m+1)), so `W i`, letter i of iterate 3(i + 1) + 2, is letter i of the
  2-limiting word: `W` is A288223, indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 0 of `W`, so positions count from 1 as in the
  entry; `Nat.nth` counts its argument from 0.
* The entry gives the limit only as 1.38..., so `main` asks for a real number m with
  1.38 <= m < 1.39, the numbers whose decimal expansion starts 1.38, such that a(n)/n tends to m
  as a limit of real numbers and -1 < m - a(n)/n < 1 for every n >= 1, with a(n)/n a real
  quotient. This is the conjunction of both parts of the conjecture. The proof takes
  m = 3 - phi = (5 - sqrt 5)/2 = 1.38196..., with phi the golden ratio.
-/

namespace OMA.S_oeis_a288224

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 1000 and 10 -> 010 over a finite word, read
from the left: where 00 starts it is replaced by 1000, where 10 starts it is replaced by 010,
and any other letter is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 1 :: 0 :: 0 :: 0 :: step l
  | 1 :: 0 :: l => 0 :: 1 :: 0 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A288223 (0-indexed): the 2-limiting word, the limit of the iterates whose index is
2 more than a multiple of 3. Letter i is the same in every iterate 3k + 2 with
k >= i + 1, and it is read off iterate 3(i + 1) + 2. -/
def W (i : ℕ) : ℕ := (iter (3 * (i + 1) + 2)).getD i 0

/-- A288224(n): the position, counted from 1 as in the entry, of the n-th 0 of A288223. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 0) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.38..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem main : ∃ m : ℝ, (1.38 ≤ m ∧ m < 1.39) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  sorry

end OMA.S_oeis_a288224
