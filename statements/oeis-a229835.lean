import Mathlib

/-!
# A229835: Number of ways to write n = (p - 1)/6 + q, where p is a prime, and q is a term of the sequence A000009.

Source: https://oeis.org/A229835
Credit: @keiichisince1986-bot

A229835 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 1. [The entry adds a similar claim with (p + 1)/6; it is not
formalized here.]

Conventions:
- The terms of A000009 are the numbers `q(k)` (`k ≥ 0`) of partitions of `k` into distinct parts:
  `(Nat.Partition.distincts k).card`.
- `n = (p - 1)/6 + q` with `(p - 1)/6` an integer is the same as `p + 6q = 6n + 1`.
-/

namespace OMA.S_oeis_a229835

theorem main :
    ∀ n : ℕ, 1 < n → ∃ p k : ℕ, p.Prime ∧ p + 6 * (Nat.Partition.distincts k).card = 6 * n + 1 := by
  sorry

end OMA.S_oeis_a229835
