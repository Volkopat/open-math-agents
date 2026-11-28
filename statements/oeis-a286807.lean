import Mathlib

/-!
# OEIS A286807: the iterates of 00 -> 001, 1 -> 101 have A132045(n) letters

Source: https://oeis.org/A286807 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 05 2017): Fixed point of the mapping 00->001, 1->101, starting with
00. Comment: Conjecture: The number of letters (0's and 1's) in the n-th iterate of the mapping is
given by A132045. Example: Iterates, starting with 00: 00, 001, 001101, 0011011010101, ...
The entry's program applies the mapping with StringReplace[w, {00 -> 001, 1 -> 101}].
A132045: Row sums of triangle A132044. A132044: Triangle T(n,k) = binomial(n, k) - 1 with
T(n,0) = T(n,n) = 1, read by rows.

Formalization notes:
* Words are lists of the digits 0 and 1. One application of the mapping reads the word from the
  left and, at each position, applies the first rule that matches there (00 before 1), copying any
  other letter, which is what StringReplace with the rule list does; a 0 that is not followed by 0
  starts no rule and is copied.
* `iter 0` is 00, and `iter (n - 1)` is the n-th iterate in the entry's list (00, 001, 001101, ...).
* `main` says: for every n >= 1 the n-th iterate has A132045(n) letters, A132045 being defined as
  the row sums of A132044.
* Controls (proved in the proof file by kernel computation): the four iterates listed in the
  entry, and A132045(0..6) = 1, 2, 3, 6, 13, 28, 59 as in its entry.
-/

namespace OMA.S_oeis_a286807

open Finset

/-- One application of the mapping 00 -> 001, 1 -> 101, read from the left; a letter that starts no
rule (a 0 not followed by 0) is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: t => [0, 0, 1] ++ step t
  | 1 :: t => [1, 0, 1] ++ step t
  | c :: t => c :: step t
  | [] => []

/-- The iterates, starting with 00: `iter 0 = 00`, `iter 1 = 001`, ... -/
def iter (n : ℕ) : List ℕ := step^[n] [0, 0]

/-- A132044: T(n,k) = binomial(n,k) - 1 with T(n,0) = T(n,n) = 1. -/
def T (n k : ℕ) : ℕ := if k = 0 ∨ k = n then 1 else n.choose k - 1

/-- A132045: the row sums of A132044. -/
def A132045 (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), T n k

/-- Kimberling's conjecture: the n-th iterate of the mapping has A132045(n) letters. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (iter (n - 1)).length = A132045 n := by
  sorry

end OMA.S_oeis_a286807
