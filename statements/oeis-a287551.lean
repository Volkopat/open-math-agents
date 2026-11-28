import Mathlib

/-!
# OEIS A287551: a(n)/n -> m = 3.19..., and -1 < m - a(n)/n < 3

Source: https://oeis.org/A287551 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 18 2017), offset 1: Positions of 1 in A287530; complement of A287531.
Conjecture: a(n)/n -> 3.19..., and if m denotes this number, then -1 < m - a(n)/n < 3 for n >= 1.
Data: 1, 5, 8, 9, 13, 19, 22, 24, 27, 28, 32, 36, ...
A287530 (Clark Kimberling, Jun 18 2017), offset 1: 1-limiting word of the mapping 00->1000, 10->001,
starting with 00. Iterates of the mapping, starting with 00: 00, 1000, 0011000, 100010011000,
0011000001010011000, ... The 1-limiting word is the limit of the n-th iterates for odd n.
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 1000, 10 -> 001}] with w[0] = 00.

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 1000 and 10 -> 001 over a finite word:
  read from the left, where 00 starts it is replaced by 1000, where 10 starts it is replaced by 001,
  and any other letter is copied. The two left sides start with different letters, so the order in
  which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. The iterates converge only along
  each residue of n mod 2; the 1-limiting word is the limit of `iter (2k + 1)`. Iterate n + 2 is
  iterate n followed by the word of the tokens tau^n(T2) (lemma `iter_two` of the proof), so iterate
  2k + 1 is a prefix of iterate 2(k + 1) + 1 and has more than k letters; hence letter i is the same
  in every iterate 2k + 1 with k >= i + 1 (lemma `W_eq`), and `W i`, letter i of iterate
  2(i + 1) + 1, is letter i of the 1-limiting word: `W` is A287530, indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 1 of `W`, so positions count from 1 as in the entry;
  `Nat.nth` counts its argument from 0.
* The entry gives the limit only as 3.19..., so `main` asks for a real number m with
  3.19 <= m < 3.20, the numbers whose decimal expansion starts 3.19, such that a(n)/n tends to m as
  a limit of real numbers and -1 < m - a(n)/n < 3 for every n >= 1, with a(n)/n a real quotient.
  This is the conjunction of both parts of the conjecture. The proof takes
  m = 1 + c = (24 + 5 * sqrt(5))/11 = 3.19821..., with c = (8 + 10 phi)/11 and phi the golden ratio.
-/

namespace OMA.S_oeis_a287551

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 1000 and 10 -> 001 over a finite word, read
from the left: where 00 starts it is replaced by 1000, where 10 starts it is replaced by 001,
and any other letter is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 1 :: 0 :: 0 :: 0 :: step l
  | 1 :: 0 :: l => 0 :: 0 :: 1 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A287530 (0-indexed): the 1-limiting word, the limit of the iterates whose index is odd.
Letter i is the same in every iterate 2k + 1 with k >= i + 1, and it is read off iterate
2(i + 1) + 1. -/
def W (i : ℕ) : ℕ := (iter (2 * (i + 1) + 1)).getD i 0

/-- A287551(n): the position, counted from 1 as in the entry, of the n-th 1 of A287530. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 1) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n tends to a number m = 3.19..., and -1 < m - a(n)/n < 3
for n >= 1. -/
theorem main : ∃ m : ℝ, (3.19 ≤ m ∧ m < 3.20) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 3 := by
  sorry

end OMA.S_oeis_a287551
