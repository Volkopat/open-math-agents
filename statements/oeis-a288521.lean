import Mathlib

/-!
# OEIS A288521: a(n)/n -> m = 1.52..., and -1 < m - a(n)/n < 1

Source: https://oeis.org/A288521 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 13 2017), offset 1: Positions of 0 in A288520; complement of A288522.
Conjecture: a(n)/n -> 1.52..., and if m denotes this number, then -1 < m - a(n)/n < 1 for n >= 1.
Data: 1, 2, 4, 5, 7, 8, 10, 11, 13, 15, 17, 18, ...
A288520 (Clark Kimberling, Jun 13 2017), offset 1: 0-limiting word of the mapping 00->0101, 10->010,
starting with 00. The 0-limiting word is the limit taken over even-numbered iterations of the
mapping. Data: 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, ...
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 0101, 10 -> 010}] with w[0] = 00, and the word
is read off w[18].

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 0101 and 10 -> 010 over a finite word:
  read from the left, where 00 starts it is replaced by 0101, where 10 starts it is replaced by 010,
  and any other letter is copied. The two left sides start with different letters, so the order in
  which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. The iterates converge only along
  each residue of n mod 2. Iterate n + 1 is a word X_n followed by a letter 1 (lemma `iter_eq` of
  the proof), and X_n is a prefix of X_(n+2) (lemma `X_two`), so iterate 2k + 2 is X_(2k+1) followed
  by 1, where X_(2k+1) is a prefix of X_(2k+3) and has more than k letters; hence letter i is the
  same in every iterate 2k + 2 with k >= i (lemma `W_eq`), and `W i`, letter i of iterate 2(i + 1),
  is letter i of the 0-limiting word: `W` is A288520, indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 0 of `W`, so positions count from 1 as in the entry;
  `Nat.nth` counts its argument from 0.
* The entry gives the limit only as 1.52..., so `main` asks for a real number m with
  1.52 <= m < 1.53, the numbers whose decimal expansion starts 1.52, such that a(n)/n tends to m as
  a limit of real numbers and -1 < m - a(n)/n < 1 for every n >= 1, with a(n)/n a real quotient.
  This is the conjunction of both parts of the conjecture. The proof takes
  m = (1 + c)/c = lam = 1.52137..., the real root of x^3 - x - 2, with c = (lam^2 + lam)/2.
-/

namespace OMA.S_oeis_a288521

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 0101 and 10 -> 010 over a finite word, read
from the left: where 00 starts it is replaced by 0101, where 10 starts it is replaced by 010,
and any other letter is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 0 :: 1 :: 0 :: 1 :: step l
  | 1 :: 0 :: l => 0 :: 1 :: 0 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A288520 (0-indexed): the 0-limiting word, the limit of the iterates whose index is even.
Letter i is the same in every iterate 2k with k >= i + 1, and it is read off iterate
2(i + 1). -/
def W (i : ℕ) : ℕ := (iter (2 * (i + 1))).getD i 0

/-- A288521(n): the position, counted from 1 as in the entry, of the n-th 0 of A288520. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 0) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.52..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem main : ∃ m : ℝ, (1.52 ≤ m ∧ m < 1.53) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  sorry

end OMA.S_oeis_a288521
