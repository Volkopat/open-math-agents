import Mathlib

/-!
# Erdős Problem 341

Source: https://www.erdosproblems.com/341
Credit: @mattdorman

The source asks (an old problem of Dickson): let `A = {a₁ < ⋯ < a_k}` be a finite set of positive
integers and extend it to an infinite sequence `a₁ < a₂ < ⋯` by defining `a_{n+1}`, for `n ≥ k`,
to be the least integer exceeding `aₙ` which is not of the form `a_i + a_j` with `i, j ≤ n`. Is it
true that the sequence of differences `a_{m+1} - a_m` is eventually periodic?

Reading used here: the sequence is indexed from `0`, so `a i` is `a_{i+1}`; the first `k` terms
(`k ≥ 1`) are the given positive integers in increasing order, and for every `n` with `k ≤ n + 1`
the term `a (n + 1)` is the least integer exceeding `a n` that is not `a i + a j` with `i, j ≤ n`
(`i = j` allowed). These conditions determine the sequence from `A`, so quantifying over every
sequence that satisfies them is the same as speaking of the extension of `A`. Eventually
periodic differences: some period `p > 0` and threshold `N` with `a (m + p + 1) - a (m + p) =
a (m + 1) - a m` for all `m ≥ N`. The statement below is the affirmative answer.
-/

namespace OMA.S_erdos_341

theorem main :
    ∀ (k : ℕ) (a : ℕ → ℕ), 1 ≤ k → 0 < a 0 →
      (∀ i, i + 1 < k → a i < a (i + 1)) →
      (∀ n, k ≤ n + 1 →
        IsLeast {m : ℕ | a n < m ∧ ∀ i ≤ n, ∀ j ≤ n, m ≠ a i + a j} (a (n + 1))) →
      ∃ p : ℕ, 0 < p ∧ ∃ N : ℕ, ∀ m ≥ N,
        a (m + p + 1) - a (m + p) = a (m + 1) - a m := by
  sorry

end OMA.S_erdos_341
