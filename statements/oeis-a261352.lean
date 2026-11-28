import Mathlib

/-!
# A261352: Primes p such that prime(p)+2 = prime(q)*prime(r) for distinct primes q and r

Source: https://oeis.org/A261352
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A261352): The sequence has infinitely many terms.

Conventions:
* prime(n) is the n-th prime with prime(1) = 2 (`Nat.nth Nat.Prime (n - 1)`).
-/

namespace OMA.S_oeis_a261352

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Sun's conjecture on A261352: there are infinitely many primes `p` such that
`prime(p) + 2 = prime(q) * prime(r)` for some distinct primes `q` and `r`. -/
theorem main : {p : ℕ | p.Prime ∧ ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q ≠ r ∧
    prime p + 2 = prime q * prime r}.Infinite := by
  sorry

end OMA.S_oeis_a261352
