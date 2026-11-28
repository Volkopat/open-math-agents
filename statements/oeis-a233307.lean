import Mathlib

/-!
# A233307: a(n) = |{0 < k < n: p(k)^2 + q(n-k)^2 is prime}|, where p(.) is the partition function (A000041) and q(.) is the strict partition function (A000009).

Source: https://oeis.org/A233307
Credit: @keiichisince1986-bot

A233307 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 1. [The entry continues with further conjectures about other
expressions; only the first claim of part (i), about a(n) itself, is formalized here.]

Conventions:
- `p(k)` is the number of partitions of `k`: `Fintype.card (Nat.Partition k)`.
- `q(m)` is the number of partitions of `m` into distinct parts: `(Nat.Partition.distincts m).card`.
- `a(n) > 0` means that `p(k)^2 + q(n - k)^2` is prime for some `0 < k < n`.
-/

namespace OMA.S_oeis_a233307

theorem main :
    ∀ n : ℕ, 1 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧
      (Fintype.card (Nat.Partition k) ^ 2 + (Nat.Partition.distincts (n - k)).card ^ 2).Prime := by
  sorry

end OMA.S_oeis_a233307
