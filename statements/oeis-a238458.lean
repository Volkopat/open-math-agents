import Mathlib

/-!
# A238458: Number of primes p < n with 2*P(n-p) + 1 prime, where P(.) is the partition function (A000041).

Source: https://oeis.org/A238458
Credit: @eltociear

`a(n)` (offset 1) counts the primes `p < n` such that `2 P(n - p) + 1` is prime, where `P` is the
partition function. The entry conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n > 2. Also, for each n > 3 there is a prime p < n with 2*P(n-p) - 1 prime.

`main` is the conjunction of the two sentences. `P(m)` is the number of partitions of `m`,
`Fintype.card (Nat.Partition m)`. `2 P(m) - 1` is exact since `P(m) ≥ 1`.
-/

namespace OMA.S_oeis_a238458

/-- The partition function `P(m)` (A000041). -/
def P (m : ℕ) : ℕ := Fintype.card (Nat.Partition m)

/-- The conjecture in OEIS A238458. -/
theorem main : (∀ n : ℕ, 2 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧ (2 * P (n - p) + 1).Prime) ∧
    (∀ n : ℕ, 3 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧ (2 * P (n - p) - 1).Prime) := by
  sorry

end OMA.S_oeis_a238458
