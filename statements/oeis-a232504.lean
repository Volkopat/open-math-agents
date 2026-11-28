import Mathlib

/-!
# A232504: Number of ways to write n = k + m (k, m > 0) with p(k) + q(m) prime, where p(.) is the partition function (A000041) and q(.) is the strict partition function (A000009).

Source: https://oeis.org/A232504
Credit: @keiichisince1986-bot

A232504 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 1.

Conventions:
- `p(k)` is the number of partitions of `k`: `Fintype.card (Nat.Partition k)`.
- `q(m)` is the number of partitions of `m` into distinct parts: `(Nat.Partition.distincts m).card`,
  where `Nat.Partition.distincts m` is the finset of partitions of `m` whose parts are pairwise
  distinct.
- `a(n) > 0` means that `n = k + m` with `k, m > 0` and `p(k) + q(m)` prime.
-/

namespace OMA.S_oeis_a232504

theorem main :
    ∀ n : ℕ, 1 < n → ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧
      (Fintype.card (Nat.Partition k) + (Nat.Partition.distincts m).card).Prime := by
  sorry

end OMA.S_oeis_a232504
