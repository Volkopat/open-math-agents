import Mathlib

/-!
# OEIS A288997: A288997(n) = A171588(n + 3) for all n > 0

Source: https://oeis.org/A288997 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 25 2017), offset 1: Fixed point of the mapping 00->0010, 01->001,
10->001, starting with 00.
Conjecture: a(n) = A171588(n+3) for all n>0. - Michel Dekking, Mar 21 2022
Data: 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, ...
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 0010, 01 -> 001, 10 -> 001}], read off w[10].
A171588 (Alexis Monnerot-Dumaine, Dec 12 2009), offset 1: The Pell word: Fixed point of the
morphism 0->001, 1->0.
Data: 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, ...

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 0010, 01 -> 001 and 10 -> 001 over a
  finite word: read from the left, where 00, 01 or 10 starts it is replaced by 0010, 001 or 001, and
  any other letter (a 1 before a 1, or a final letter) is copied. The three left sides are the three
  pairs other than 11, so the order in which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. The iterates are not nested, but
  the stable prefixes S_0 = 00, S_(k+1) = the pass over the longest prefix of S_k of even length,
  are prefixes of iterate k and of S_(k+1), and S_k has at least k + 2 letters (lemmas
  `SRGen.chain_iter`, `SRGen.chain_prefix`, `SRGen.chain_length` of the proof); so `W i`, letter i
  of iterate i + 1, is letter i of the fixed point: `W` is A288997 indexed from 0, and `a n` is
  `W (n - 1)`, counted from 1 as in the entry.
* `pell` applies the morphism 0 -> 001, 1 -> 0 letter by letter, and `pellIter n` is its n-th
  power applied to 0. As 001 begins with 0, `pellIter n` is a prefix of `pellIter (n + 1)`, and it
  has at least n + 1 letters, so letter n - 1 of `pellIter n` is letter n - 1 of the fixed point:
  `pellWord n` is A171588(n), counted from 1 as in that entry.
* `main` states the conjecture for every n > 0.
-/

namespace OMA.S_oeis_a288997

/-- One pass of StringReplace with the rules 00 -> 0010, 01 -> 001 and 10 -> 001 over a finite
word, read from the left: where 00, 01 or 10 starts it is replaced by 0010, 001 or 001, and any
other letter (a 1 before a 1, or a final letter) is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 0 :: 0 :: 1 :: 0 :: step l
  | 0 :: 1 :: l => 0 :: 0 :: 1 :: step l
  | 1 :: 0 :: l => 0 :: 0 :: 1 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A288997 (0-indexed): the fixed point of the mapping; its letter i is read off iterate i + 1. -/
def W (i : ℕ) : ℕ := (iter (i + 1)).getD i 0

/-- A288997(n), counted from 1 as in the entry. -/
def a (n : ℕ) : ℕ := W (n - 1)

/-- The Pell morphism 0 -> 001, 1 -> 0, applied letter by letter (other letters are copied). -/
def pell : List ℕ → List ℕ
  | 0 :: l => 0 :: 0 :: 1 :: pell l
  | 1 :: l => 0 :: pell l
  | x :: l => x :: pell l
  | [] => []

/-- The images of 0 under the powers of the Pell morphism: 0, 001, 0010010, ... -/
def pellIter : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => pell (pellIter n)

/-- A171588(n), the Pell word counted from 1: letter n - 1 of the n-th image of 0. -/
def pellWord (n : ℕ) : ℕ := (pellIter n).getD (n - 1) 0

/-- Dekking's conjecture: A288997(n) = A171588(n + 3) for all n > 0. -/
theorem main : ∀ n : ℕ, 0 < n → a n = pellWord (n + 3) := by
  sorry

end OMA.S_oeis_a288997
