import Mathlib

/-!
# A256555: Number of ways to write n as the sum of two (unordered) distinct elements of the set {floor(p/3): p is prime}.

Source: https://oeis.org/A256555
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A256555 (Zhi-Wei Sun, Apr 01 2015): For any integer m > 2, every positive integer can be written as
the sum of two distinct elements of the set {floor(p/m): p is prime}.

Conventions:
* The sequence itself is the case m = 3 (offset 1, data 1, 1, 2, 2, 3, 3, 4, 3, ...): a(n) is
  the number of unordered pairs of distinct elements of {floor(p/3): p prime} with sum n.
  The conjecture in the entry is about every integer m > 2 and is formalized in that
  generality, as an existence statement.
* floor(p/m) is natural number division `p / m`. Two elements of the set are distinct when
  the values floor(p/m) and floor(q/m) differ (not merely the primes p and q).
* Every positive integer means every n >= 1.
-/

namespace OMA.S_oeis_a256555

/-- The set {floor(p/m) : p prime}. -/
def S (m : ℕ) : Set ℕ := {u : ℕ | ∃ p : ℕ, p.Prime ∧ u = p / m}

/-- The conjecture of Sun: for any m > 2, every positive integer is the sum of two distinct
elements of {floor(p/m) : p prime}. -/
theorem main : ∀ m : ℕ, 2 < m → ∀ n : ℕ, 0 < n →
    ∃ u v : ℕ, u ∈ S m ∧ v ∈ S m ∧ u ≠ v ∧ u + v = n := by
  sorry

end OMA.S_oeis_a256555
