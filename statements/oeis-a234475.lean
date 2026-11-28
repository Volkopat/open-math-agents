import Mathlib

/-!
# A234475: Number of ways to write n = k + m with 2 < k <= m such that q(phi(k)*phi(m)/4) + 1 is prime, where phi(.) is Euler's totient function and q(.) is the strict partition function (A000009).

Source: https://oeis.org/A234475
Credit: @keiichisince1986-bot

A234475 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 5.

Conventions:
- `phi` is Euler's totient function `Nat.totient`.
- `q(j)` is the number of partitions of `j` into distinct parts: `(Nat.Partition.distincts j).card`.
- For `k, m > 2` both `phi(k)` and `phi(m)` are even, so `phi(k) * phi(m) / 4` (natural-number division)
  is exact.
-/

namespace OMA.S_oeis_a234475

theorem main :
    ∀ n : ℕ, 5 < n → ∃ k m : ℕ, 2 < k ∧ k ≤ m ∧ k + m = n ∧
      ((Nat.Partition.distincts (Nat.totient k * Nat.totient m / 4)).card + 1).Prime := by
  sorry

end OMA.S_oeis_a234475
