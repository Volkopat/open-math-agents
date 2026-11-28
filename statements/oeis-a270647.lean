import Mathlib

/-!
# A270647: The sequence a of 1's and 2's starting with (2,2,1,2) such that a(n) is the length of the (n+3)rd run of a.

Source: https://oeis.org/A270647
Credit: @rickmanelius

Conjecture (R. J. Mathar, Jun 21 2025): a(n) = A270643(n+1).

Formalization notes:
* Both sequences are built by the Mathematica program of their entries (Peter J. C. Moses,
  Apr 01 2016): start from the initial word, and at step n (n = 1, 2, 3, ...) append a(n)
  copies (a(n) is letter n of the current word, counting from 1) of the letter opposite to the
  last letter: 2 after a 1, and 1 after a 2 (`opp`). `build w k` is the word after k steps,
  starting from the word w. The letters are always 1 or 2, so every step appends at least one
  letter and the word after k steps has at least k + 4 letters; steps only append, so letter n
  never changes once it is there. `a n` reads letter n, counting from 1 (offset 1), from the
  word after n steps.
* Each step appends a block of the letter opposite to the current last letter, so the blocks
  alternate and each one is a whole run. For A270647 the initial word 2, 2, 1, 2 has three runs
  and the block of step n is the (n+3)rd run, of length a(n), which is the defining property in
  the name. The values a(1), a(2), ... are 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, ..., matching the
  data.
* A270643 is the sequence of 1's and 2's starting with (1,2,2,1) such that a(n) is the length
  of the (n+3)rd run of a. Its entry gives the same program with the initial word 1, 2, 2, 1
  (three runs, so the block of step n is the (n+3)rd run). `A270643 n` reads its letter n,
  counting from 1 (offset 1); the values are 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 2, ..., matching
  its data.
* The conjecture is stated for every n ≥ 1, the offset of A270647; then n + 1 ≥ 2 lies inside
  the offset of A270643.
-/

namespace OMA.S_oeis_a270647

/-- The letter appended after the last letter c: 2 after a 1, and 1 otherwise. -/
def opp (c : ℕ) : ℕ := if c = 1 then 2 else 1

/-- The word after k steps of the program, starting from the word w: step k + 1 appends
letter k + 1 (counting from 1) of the current word many copies of the letter opposite to the
last letter. -/
def build (w : List ℕ) : ℕ → List ℕ
  | 0 => w
  | k + 1 => build w k ++ List.replicate ((build w k).getD k 0) (opp ((build w k).getLastD 0))

/-- A270647(n) for n ≥ 1: letter n, counting from 1, of the word built from 2, 2, 1, 2. -/
def a (n : ℕ) : ℕ := (build [2, 2, 1, 2] n).getD (n - 1) 0

/-- A270643(n) for n ≥ 1: letter n, counting from 1, of the word built from 1, 2, 2, 1. -/
def A270643 (n : ℕ) : ℕ := (build [1, 2, 2, 1] n).getD (n - 1) 0

/-- Mathar's conjecture: a(n) = A270643(n+1) for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = A270643 (n + 1) := by
  sorry

end OMA.S_oeis_a270647
