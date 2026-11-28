import Mathlib

/-!
# A352446: total number of parts in all partitions of n into an even number of consecutive parts

Source: https://oeis.org/A352446 (conjecture of Vaclav Kotesovec, Oct 23 2024)

A partition of `n` into `L` consecutive parts is determined by its smallest part `m >= 1`:
its parts are `m, m+1, ..., m+L-1`. Since `m <= n` and `L <= n` for such a partition, `a(n)`
(offset 1) is the sum of `L` over the pairs `(m, L)` in `[1, n] x [1, n]` with `L` even and
`m + (m+1) + ... + (m+L-1) = n`.

Conjecture: the g.f. of the sequence is `Sum_{k>=1} 2*k*x^(k*(2*k+1))/(1-x^(2*k))`.
Expanding `1/(1-x^(2*k))` as a geometric series, the coefficient of `x^n` in this g.f. is the
sum of `2*k` over the pairs `(k, j)` with `k >= 1`, `j >= 0` and `k*(2*k+1) + 2*k*j = n`
(necessarily `k <= n` and `j <= n`). The statement is this coefficient identity for `n >= 1`.
-/

namespace OMA.S_oeis_a352446

/-- The sum of the `L` consecutive integers starting at `m`. -/
def consecSum (m L : ℕ) : ℕ := ∑ i ∈ Finset.range L, (m + i)

/-- Total number of parts in all partitions of `n` into an even number of consecutive parts. -/
def a (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.Icc 1 n, ∑ L ∈ (Finset.Icc 1 n).filter (fun L => Even L ∧ consecSum m L = n), L

theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = ∑ k ∈ Finset.Icc 1 n, ∑ j ∈ Finset.range (n + 1),
      if k * (2 * k + 1) + 2 * k * j = n then 2 * k else 0 := by
  sorry

end OMA.S_oeis_a352446
