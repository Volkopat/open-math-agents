import Mathlib

/-!
# A238459: Number of primes p < n with q(n-p) + 1 prime, where q(.) is the strict partition function (A000009).

Source: https://oeis.org/A238459
Credit: @eltociear

`a(n)` (offset 1) counts the primes `p < n` such that `q(n - p) + 1` is prime, where `q` is the
strict partition function (partitions into distinct parts). The entry conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n > 2. Also, for each n > 6 there is a prime p < n with q(n-p) - 1 prime.

`main` is the conjunction of the two sentences. `q(m)` is `(Nat.Partition.distincts m).card`, the
number of partitions of `m` with distinct parts. `q(m) - 1` is exact since `q(m) ≥ 1`.
-/

namespace OMA.S_oeis_a238459

/-- The strict partition function `q(m)` (A000009). -/
def q (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- The conjecture in OEIS A238459. -/
theorem main : (∀ n : ℕ, 2 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧ (q (n - p) + 1).Prime) ∧
    (∀ n : ℕ, 6 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧ (q (n - p) - 1).Prime) := by
  sorry

end OMA.S_oeis_a238459
