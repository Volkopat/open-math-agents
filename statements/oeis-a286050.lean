import Mathlib

/-!
# OEIS A286050: 2n - a(n) is in {0, 1} for the positions of 0 in A286049

Source: https://oeis.org/A286050 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, May 07 2017), offset 1: Positions of 0 in A286049; complement of
A286051. Comment: Conjecture: 2n - a(n) is in {0,1} for n >= 1. Data: 1, 4, 5, 7, 9, 12, ...
A286049 (Clark Kimberling, May 07 2017), offset 1: {110->1}-transform of the Thue-Morse word
A010060. Its program: w1 = StringReplace[w, {110 -> 1}] with w the Thue-Morse word.
A010060 (offset 0): the Thue-Morse sequence 0, 1, 1, 0, 1, 0, 0, 1, ..., a(n) = A000120(n) mod 2.

Formalization notes:
* t(n) is the parity of the number of 1s in the binary expansion of n (A010060, offset 0).
* The transform is StringReplace with the single rule 110 -> 1 applied to the infinite word t:
  read from the left, at each position a 110 starting there is replaced by 1 and skipped, any
  other letter is copied. `pos k` is the position of t read for the output letter k, and the
  output letter is t(pos k) in both cases. (The example line of A286049 says 011 where its name,
  its result and the program say 110.)
* `w` is A286049 indexed from 0, and `a n` adds 1 to the 0-based index of the n-th 0 of `w`,
  so positions count from 1 as in the entries; `Nat.nth` counts its argument from 0.
* `main` states the conjecture with integer subtraction: 2n - a(n) = 0 or 1 for all n >= 1.
* Controls proved in the proof file: w begins 0, 1, 1, 0, 0, 1, 0, 1 (A286049) and
  a(1..4) = 1, 4, 5, 7 (A286050).
-/

namespace OMA.S_oeis_a286050

/-- The Thue-Morse word A010060 (offset 0): t(n) is the parity of the number of 1s in the binary
expansion of n. -/
def tm (n : ℕ) : ℕ := (Nat.digits 2 n).count 1 % 2

/-- The scan of StringReplace with the rule 110 -> 1 on the infinite word t, read from the left:
`pos k` is the position of t at which the output letter k (from 0) is produced; if 110 starts
there it is replaced by 1 and skipped, otherwise the letter is copied. -/
def pos : ℕ → ℕ
  | 0 => 0
  | k + 1 => if tm (pos k) = 1 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 then pos k + 3
      else pos k + 1

/-- A286049 (0-indexed): the k-th letter of the {110 -> 1}-transform of the Thue-Morse word, the
copied letter or the 1 that replaces 110, which is t(pos k) in both cases. -/
def w (k : ℕ) : ℕ := tm (pos k)

/-- A286050(n): the position, counted from 1 as in the entry, of the n-th 0 of A286049. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => w k = 0) (n - 1) + 1

/-- Kimberling's conjecture: 2n - a(n) is in {0, 1} for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (2 * (n : ℤ) - a n = 0 ∨ 2 * (n : ℤ) - a n = 1) := by
  sorry

end OMA.S_oeis_a286050
