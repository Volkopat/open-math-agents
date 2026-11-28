import Mathlib

/-!
# A304916: number of divisors of the central binomial coefficient a power of 2

Source: https://oeis.org/A304916

A304916 lists the numbers k such that the number of divisors of the k-th central binomial
coefficient C(2k, k) is a power of 2: 0, 1, 2, 4, 7, 11, 21, 22, 28, 37, 42, 52, 69, 784.
Its comments state the conjecture: there are no terms beyond 784.

Conventions:
* C(2k, k) is `Nat.centralBinom k`; its number of divisors is `(Nat.centralBinom k).divisors.card`.
* A power of 2 is `2 ^ j` with `j ≥ 0` (k = 0 is a term: C(0, 0) = 1 has 1 = 2^0 divisor).
-/

namespace OMA.S_oeis_a304916

/-- `k` is a term of A304916. -/
def IsTerm (k : ℕ) : Prop := ∃ j : ℕ, (Nat.centralBinom k).divisors.card = 2 ^ j

/-- No term of A304916 exceeds 784. -/
theorem main : ∀ k : ℕ, 784 < k → ¬ IsTerm k := by
  sorry

end OMA.S_oeis_a304916
