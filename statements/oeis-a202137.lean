import Mathlib

/-!
# A202137: arbitrarily long runs of k with 24k + 1 neither square nor prime

Source: https://oeis.org/A202137
Credit: @ivillar

Status: known result: the entry notes that the conjecture can be proved (Robert Israel, Jan 25 2018).

A202137 lists the numbers k such that 24k + 1 is neither a square nor a prime; data
6, 9, 11, 16, 20, 21, 23, 27, 29, 30, 31, ...

Conjecture (in the comments of A202137): the sequence contains arbitrarily long runs of
consecutive integers. Robert Israel (Jan 25 2018) notes in the entry that this can be proved
with the Chinese Remainder Theorem and the growth of the gaps between squares.

Formalization: a run of length L is a block k, k + 1, ..., k + L - 1 of terms, so the statement is
that for every L there is such a block. The first runs of lengths 1, 2, 3, 4 in the entry start
at 6, 20, 29, 58.
-/

namespace OMA.S_oeis_a202137

/-- `k` is a term of A202137: `24 k + 1` is neither a square nor a prime. -/
def IsTerm (k : ℕ) : Prop := ¬ IsSquare (24 * k + 1) ∧ ¬ (24 * k + 1).Prime

/-- The sequence contains runs of consecutive integers of every length. -/
theorem main : ∀ L : ℕ, ∃ k : ℕ, ∀ i : ℕ, i < L → IsTerm (k + i) := by
  sorry

end OMA.S_oeis_a202137
