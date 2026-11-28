import Mathlib

/-!
# OEIS A288671: a(n)/n -> m = 1.41..., and -1 < m - a(n)/n < 1

Source: https://oeis.org/A288671 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 15 2017), offset 1: Positions of 0 in A288670; complement of A288672.
Conjecture: a(n)/n -> 1.41..., and if m denotes this number, then -1 < m - a(n)/n < 1 for n >= 1.
Data: 1, 4, 5, 8, 9, 11, 12, 13, 14, 17, 18, 21, ...
A288670 (Clark Kimberling, Jun 15 2017), offset 1: 1-limiting word of the mapping 00->0110, 10->000,
starting with 00. Iterates of the mapping, starting with 00: 00, 0110, 01000, 00000110,
0110011001000, ... The 1-limiting word is the limit of the n-th iterates for n == 1 mod 3.
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 0110, 10 -> 000}] with w[0] = 00.

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 0110 and 10 -> 000 over a finite word:
  read from the left, where 00 starts it is replaced by 0110, where 10 starts it is replaced by 000,
  and any other letter is copied. The two left sides start with different letters, so the order in
  which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. The iterates converge only along
  each residue of n mod 3; the 1-limiting word is the limit of `iter (3k + 1)`. Iterate n + 3 is
  iterate n twice followed by iterate n + 1 (lemma `iter_rec` of the proof), so iterate 3k + 1 is a
  prefix of iterate 3(k + 1) + 1 and has more than k letters; hence letter i is the same in every
  iterate 3k + 1 with k >= i + 1 (lemma `W_eq`), and `W i`, letter i of iterate 3(i + 1) + 1, is
  letter i of the 1-limiting word: `W` is A288670, indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 0 of `W`, so positions count from 1 as in the entry;
  `Nat.nth` counts its argument from 0.
* The entry gives the limit only as 1.41..., so `main` asks for a real number m with
  1.41 <= m < 1.42, the numbers whose decimal expansion starts 1.41, such that a(n)/n tends to m as
  a limit of real numbers and -1 < m - a(n)/n < 1 for every n >= 1, with a(n)/n a real quotient.
  This is the conjunction of both parts of the conjecture. The proof takes
  m = (1 + c)/c = 1.41798..., with c = (6 lam^2 + 10 lam + 2)/13 and lam = 1.52137... the real root
  of x^3 - x - 2.
-/

namespace OMA.S_oeis_a288671

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 0110 and 10 -> 000 over a finite word, read
from the left: where 00 starts it is replaced by 0110, where 10 starts it is replaced by 000,
and any other letter is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 0 :: 1 :: 1 :: 0 :: step l
  | 1 :: 0 :: l => 0 :: 0 :: 0 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A288670 (0-indexed): the 1-limiting word, the limit of the iterates whose index is
1 more than a multiple of 3. Letter i is the same in every iterate 3k + 1 with
k >= i + 1, and it is read off iterate 3(i + 1) + 1. -/
def W (i : ℕ) : ℕ := (iter (3 * (i + 1) + 1)).getD i 0

/-- A288671(n): the position, counted from 1 as in the entry, of the n-th 0 of A288670. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 0) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.41..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem main : ∃ m : ℝ, (1.41 ≤ m ∧ m < 1.42) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  sorry

end OMA.S_oeis_a288671
