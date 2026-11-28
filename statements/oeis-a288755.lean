import Mathlib

/-!
# OEIS A288755: a(n)/n -> m = 3.53..., and -1 < m - a(n)/n < 2

Source: https://oeis.org/A288755 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 25 2017), offset 1: Positions of 1 in A288710; complement of A287103.
Conjecture: a(n)/n -> 3.53..., and if m denotes this number, then -1 < m - a(n)/n < 2 for n >= 1.
Data: 4, 5, 13, 14, 18, 22, 23, 30, 31, 38, 39, 46, ...
A288710 (Clark Kimberling, Jun 24 2017), offset 1: 0-limiting word of the mapping 00->1000,
10->0001, starting with 00. Iterates of the mapping, starting with 00: 00, 1000, 00011000,
10000100011000, 00011000000011000100011000, ... The 0-limiting word is the limit of the n-th
iterates for n == 0 mod 2.
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 1000, 10 -> 0001}] with w[0] = 00.

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 1000 and 10 -> 0001 over a finite word:
  read from the left, where 00 starts it is replaced by 1000, where 10 starts it is replaced by
  0001, and any other letter is copied. The two left sides start with different letters, so the
  order in which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. The iterates converge only along
  each residue of n mod 2; the 0-limiting word is the limit of `iter (2k)`. Iterate n + 2 is iterate
  n followed by the word of the tokens tau^n(E) (lemma `iter_two` of the proof), so iterate 2k is a
  prefix of iterate 2(k + 1) and has more than k letters; hence letter i is the same in every
  iterate 2k with k >= i + 1 (lemma `W_eq`), and `W i`, letter i of iterate 2(i + 1), is letter i of
  the 0-limiting word: `W` is A288710, indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 1 of `W`, so positions count from 1 as in the entry;
  `Nat.nth` counts its argument from 0.
* The entry gives the limit only as 3.53..., so `main` asks for a real number m with
  3.53 <= m < 3.54, the numbers whose decimal expansion starts 3.53, such that a(n)/n tends to m as
  a limit of real numbers and -1 < m - a(n)/n < 2 for every n >= 1, with a(n)/n a real quotient.
  This is the conjunction of both parts of the conjecture. The proof takes m = 1 + c = 3.53306...,
  with c = -1/2 - lam/4 - 3 lam^2/4 + lam^3/2 + lam^4/4 and lam = 1.84622... the Perron root of
  x^5 - x^4 - x^3 - 3x + 2.
-/

namespace OMA.S_oeis_a288755

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 1000 and 10 -> 0001 over a finite word, read
from the left: where 00 starts it is replaced by 1000, where 10 starts it is replaced by 0001,
and any other letter is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 1 :: 0 :: 0 :: 0 :: step l
  | 1 :: 0 :: l => 0 :: 0 :: 0 :: 1 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A288710 (0-indexed): the 0-limiting word, the limit of the iterates whose index is even.
Letter i is the same in every iterate 2k with k >= i + 1, and it is read off iterate
2(i + 1). -/
def W (i : ℕ) : ℕ := (iter (2 * (i + 1))).getD i 0

/-- A288755(n): the position, counted from 1 as in the entry, of the n-th 1 of A288710. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 1) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n tends to a number m = 3.53..., and -1 < m - a(n)/n < 2
for n >= 1. -/
theorem main : ∃ m : ℝ, (3.53 ≤ m ∧ m < 3.54) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 2 := by
  sorry

end OMA.S_oeis_a288755
