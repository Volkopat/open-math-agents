import Mathlib

/-!
# OEIS A288467: a(n)/n -> m = 1.56..., and -1 < m - a(n)/n < 1

Source: https://oeis.org/A288467 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 11 2017), offset 1: Positions of 0 in A288466; complement of A288468.
Conjecture: a(n)/n->1.56..., and if m denotes this number, then -1 < m - a(n)/n < 1 for n >= 1.
Data: 1, 3, 5, 7, 8, 10, 12, 13, 15, 16, 18, 20, ...
A288466 (Clark Kimberling, Jun 11 2017), offset 1: Fixed point of the mapping 00->0101, 1->010,
starting with 00. Data: 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, ...
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 0101, 1 -> 010}] with w[0] = 00, and the word
is read off w[11].

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 0101 and 1 -> 010 over a finite word:
  read from the left, where 00 starts it is replaced by 0101, a letter 1 is replaced by 010, and any
  other letter (a 0 before a 1 or at the end) is copied. The two left sides start with different
  letters, so the order in which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. The iterates converge only along
  each residue of n mod 2: the even iterates start with 00 and the odd ones with 01 (lemma
  `iter_head` of the proof). Iterate 2k + 1 is a prefix of a word V_k (lemma `iter_odd_prefix`), V_k
  is a prefix of V_(k+1) (lemma `V_prefix`), and iterate n has at least n + 2 letters (lemma
  `iter_length`), so letter i is the same in every iterate 2k + 1 with k >= i (lemma `W_odd`), and
  `W i`, letter i of iterate 2(i + 1) + 1, is letter i of the limit of the odd iterates: `W` is
  A288466, indexed from 0.
* The entry A288466 calls its word the fixed point of the mapping, but the iterates alternate
  between words that start with 00 and words that start with 01; its data, 0, 1, 0, 1, 0, 1, 0, 0,
  1, 0, 1, 0, 0, 1, ..., and its program, which reads the word off w[11], are those of the odd
  iterates, and the data of A288467 and A288468 are the positions of 0 and 1 in these data; `W` is
  this word, the limit of the odd iterates.
* `a n` adds 1 to the 0-based index of the n-th 0 of `W`, so positions count from 1 as in the entry;
  `Nat.nth` counts its argument from 0.
* The entry gives the limit only as 1.56..., so `main` asks for a real number m with
  1.56 <= m < 1.57, the numbers whose decimal expansion starts 1.56, such that a(n)/n tends to m as
  a limit of real numbers and -1 < m - a(n)/n < 1 for every n >= 1, with a(n)/n a real quotient.
  This is the conjunction of both parts of the conjecture. The proof takes
  m = (1 + c)/c = 1.56519..., with c = (lam^2 - 1)/2 and lam = 2.13039... the real root of
  x^3 - x^2 - x - 3.
-/

namespace OMA.S_oeis_a288467

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 0101 and 1 -> 010 over a finite word, read
from the left: where 00 starts it is replaced by 0101, a letter 1 is replaced by 010, and any
other letter is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 0 :: 1 :: 0 :: 1 :: step l
  | 1 :: l => 0 :: 1 :: 0 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A288466 (0-indexed): the limit of the iterates whose index is odd (the entry calls it the
fixed point of the mapping; its data and its program, w[11], are those of the odd iterates).
Letter i is the same in every iterate 2k + 1 with k >= i, and it is read off iterate
2(i + 1) + 1. -/
def W (i : ℕ) : ℕ := (iter (2 * (i + 1) + 1)).getD i 0

/-- A288467(n): the position, counted from 1 as in the entry, of the n-th 0 of A288466. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 0) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.56..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem main : ∃ m : ℝ, (1.56 ≤ m ∧ m < 1.57) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  sorry

end OMA.S_oeis_a288467
