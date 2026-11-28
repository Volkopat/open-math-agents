import Mathlib

/-!
# A234470: Number of ways to write n = k + m with k > 0 and m > 2 such that p(k + phi(m)/2) is prime, where p(.) is the partition function (A000041) and phi(.) is Euler's totient function.

Source: https://oeis.org/A234470
Credit: @keiichisince1986-bot

A234470 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 if n > 3 is not among 27, 34, 50, 61, 74, 78, 115, 120, 123, 127.

Conventions:
- `p(j)` is the number of partitions of `j`: `Fintype.card (Nat.Partition j)`; `phi` is `Nat.totient`.
- For `m > 2`, `phi(m)` is even, so `phi(m)/2` (natural-number division) is exact.
- The ten listed numbers have `a(n) = 0` (the data shows `a(n) = 0` there). We state the conjecture
  as: the set of `n > 3` admitting no such `k, m` is exactly the listed set. This adds to the
  conjecture only these ten finite checks.
-/

namespace OMA.S_oeis_a234470

theorem main :
    {n : ℕ | 3 < n ∧ ¬ ∃ k m : ℕ, 0 < k ∧ 2 < m ∧ k + m = n ∧
        (Fintype.card (Nat.Partition (k + Nat.totient m / 2))).Prime} =
      {27, 34, 50, 61, 74, 78, 115, 120, 123, 127} := by
  sorry

end OMA.S_oeis_a234470
