import Mathlib

/-!
# OEIS A288309: the n-th iterate of 00 -> 0010, 1 -> 110 has a(n) letters

Source: https://oeis.org/A288309 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, 2017), offset 0: a(n) = 2*a(n-1) + 2*a(n-2) - 3*a(n-3), where a(0) = 2,
a(1) = 4, a(2) = 8. Comment: Conjecture: a(n) is the number of letters (0's and 1's) in the n-th
iteration of the mapping 00->0010, 1->110, starting with 00; see A288306. The program of A288306
applies the mapping as StringReplace[w, {00 -> 0010, 1 -> 110}] and lists the lengths of w[n].

Formalization notes:
* Words are lists of the digits 0 and 1. One application of the mapping reads the word from the
  left and, at each position, applies the first rule that matches there (00 before 1), copying any
  other letter, which is what StringReplace with the rule list does; a 0 that is not followed by 0
  starts no rule and is copied.
* `iter 0` is the starting word 00 and `iter n` is the n-th iteration, so that a(0) = 2 is the
  length of 00, as in the entry's offset and the program's table.
* `main` says: the n-th iteration has a(n) letters for every n, with a defined by its recurrence
  and initial values.
* Controls (proved in the proof file by kernel computation): iter 1 = 0010, iter 2 = 00101100, and
  the lengths of iter 0..6 are 2, 4, 8, 18, 40, 92, 210, the entry's a(0..6).
-/

namespace OMA.S_oeis_a288309

/-- One application of the mapping 00 -> 0010, 1 -> 110, read from the left; a letter that starts
no rule (a 0 not followed by 0) is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: t => [0, 0, 1, 0] ++ step t
  | 1 :: t => [1, 1, 0] ++ step t
  | c :: t => c :: step t
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter (n : ℕ) : List ℕ := step^[n] [0, 0]

/-- A288309: a(n) = 2a(n-1) + 2a(n-2) - 3a(n-3), a(0) = 2, a(1) = 4, a(2) = 8. -/
def A : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | n + 3 => 2 * A (n + 2) + 2 * A (n + 1) - 3 * A n

/-- Kimberling's conjecture: the n-th iteration of the mapping has a(n) letters. -/
theorem main : ∀ n : ℕ, ((iter n).length : ℤ) = A n := by
  sorry

end OMA.S_oeis_a288309
