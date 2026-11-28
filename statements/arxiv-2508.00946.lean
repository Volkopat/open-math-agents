import Mathlib

/-!
# Partitioning $[n]$ into parts of size at most $3$ whose sums are powers of $3$

Source: https://arxiv.org/abs/2508.00946
Credit: @SulkBash

## The problem (as the source states it)

Given integers $m > 1$ and $n > 0$, a partition of the set $[n] = \{1, \dots, n\}$ is
*$m$-good* if the number of elements in each part is at most $m$ and their sum is a power of $m$.
For every $n$ there is a unique 2-good partition of $[n]$, and for each $m > 3$ there is no
$m$-good partition for infinitely many $n$. Less is known for $m = 3$.

Conjecture: a 3-good partition of $[n]$ exists for each $n$.

The paper proves that a minimal counterexample, if any, must have the form $n = 3^t + 3k + 2$ with
further restrictions on $k$, and it reports a computer verification.

## Formalization notes

* A partition of $[n]$ is a `Finpartition (Finset.Icc 1 n)`: nonempty, pairwise disjoint parts
  whose union is `{1, …, n}`.
* `IsGood m n P` says that every part `s` has `s.card ≤ m` and `∑ i ∈ s, i = m ^ k` for some
  `k : ℕ`.
* A power of `m` includes `m ^ 0 = 1`. The source needs this: its statement that every `n` has a
  2-good partition already fails for `n = 1` otherwise, since the only partition of `{1}` has
  part sum `1`.
* `n` ranges over positive integers, as in the source (`n > 0`).
-/

namespace OMA.S_arxiv_2508_00946

/-- A partition of `[n] = {1, …, n}` is `m`-good if each part has at most `m` elements and its
sum is a power of `m`. -/
def IsGood (m n : ℕ) (P : Finpartition (Finset.Icc 1 n)) : Prop :=
  ∀ s ∈ P.parts, s.card ≤ m ∧ ∃ k : ℕ, ∑ i ∈ s, i = m ^ k

/-- Every `[n]` with `n > 0` has a 3-good partition. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ P : Finpartition (Finset.Icc 1 n), IsGood 3 n P := by
  sorry

end OMA.S_arxiv_2508_00946
