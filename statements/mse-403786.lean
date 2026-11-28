import Mathlib

/-!
# Infinitely many primes with a prime factorial shift?

Source: https://math.stackexchange.com/questions/403786
Credit: @sassmama27

The question restricts the primes to those congruent to 2 modulo 3.
-/

namespace OMA.S_mse_403786

theorem main :
    Set.Infinite {p : ℕ | p.Prime ∧ p % 3 = 2 ∧ (Nat.factorial (p - 1) + p).Prime} := by
  sorry

end OMA.S_mse_403786
