import Mathlib

/-!
# OEIS A289240: a(n)/n -> sqrt 2, and -1 < sqrt 2 - a(n)/n <= -1 + sqrt 2

Source: https://oeis.org/A289240 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jul 01 2017), offset 1: Positions of 0 in A289239; complement of A289241.
Conjecture: a(n)/n -> sqrt(2)..., and -1 < sqrt(2)-a(n)/n < = -1+sqrt(2) for n >= 1.
Data: 1, 2, 4, 5, 7, 9, 10, 12, 13, 14, 15, 17, ...
A289239 (Clark Kimberling, Jun 29 2017), offset 1: Fixed point of the mapping 00->0010, 01->100,
10->010, starting with 00.
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 0010, 01 -> 100, 10 -> 010}], read off w[11].

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 0010, 01 -> 100 and 10 -> 010 over a
  finite word: read from the left, where 00, 01 or 10 starts it is replaced by 0010, 100 or 010, and
  any other letter (a 1 before a 1, or a final letter) is copied. The three left sides are the three
  pairs other than 11, so the order in which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. The stable prefixes S_0 = 00,
  S_(k+1) = the pass over the longest prefix of S_k of even length, are prefixes of iterate k and of
  S_(k+1), whether or not the iterates are nested, and S_k has at least k + 2 letters (lemmas
  `SRGen.chain_iter`, `SRGen.chain_prefix`, `SRGen.chain_length` of the proof); so `W i`, letter i
  of iterate i + 1, is letter i of the fixed point: `W` is A289239, indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 0 of `W`, so positions count from 1 as in the entry;
  `Nat.nth` counts its argument from 0.
* The entry gives the limit as the closed form sqrt(2) (followed by dots, which add nothing to a
  closed form), so `main` says that a(n)/n tends to sqrt 2 as a limit of real numbers, and gives
  -1 < sqrt 2 - a(n)/n <= -1 + sqrt 2 for every n >= 1, the right-hand inequality non-strict as
  written (< =). That side says a(n) >= n, which holds for the position of the n-th letter of any
  kind, with equality exactly at n = 1 and n = 2 (the word begins with 001); the left side says
  a(n) < (1 + sqrt 2) n.
-/

namespace OMA.S_oeis_a289240

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 0010, 01 -> 100 and 10 -> 010 over a finite
word, read from the left: where 00, 01 or 10 starts it is replaced by 0010, 100 or 010, and any
other letter (a 1 before a 1, or a final letter) is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 0 :: 0 :: 1 :: 0 :: step l
  | 0 :: 1 :: l => 1 :: 0 :: 0 :: step l
  | 1 :: 0 :: l => 0 :: 1 :: 0 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A289239 (0-indexed): the fixed point of the mapping; its letter i is read off iterate i + 1. -/
def W (i : ℕ) : ℕ := (iter (i + 1)).getD i 0

/-- A289240(n): the position, counted from 1 as in the entry, of the n-th 0 of A289239. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 0) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n tends to sqrt 2, and -1 < sqrt 2 - a(n)/n <= -1 + sqrt 2 for
n >= 1. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (Real.sqrt 2)) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < Real.sqrt 2 - (a n : ℝ) / n ∧
      Real.sqrt 2 - (a n : ℝ) / n ≤ -1 + Real.sqrt 2 := by
  sorry

end OMA.S_oeis_a289240
