import Mathlib

/-!
# A230224: Number of ways to write 2*n = p + q + r + s with p <= q <= r <= s such that p, q, r, s are primes in A230223.

Source: https://oeis.org/A230224
Credit: @keiichisince1986-bot

A230224 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 17.

Conventions:
- A230223 lists the primes `p` such that `3p - 4`, `3p - 10` and `3p - 14` are all prime: `InA230223 p`.
- The natural-number subtractions are exact for `p ≥ 5`. For `p = 2` and `p = 3` the truncated value
  `3p - 10 = 0` is not prime, and for `p = 5` the value `3p - 14 = 1` is not prime; so `InA230223`
  holds exactly for the terms `7, 11, 17, 19, 31, …` of A230223.
-/

namespace OMA.S_oeis_a230224

/-- `p` is a term of A230223: `p`, `3p - 4`, `3p - 10` and `3p - 14` are all prime. -/
def InA230223 (p : ℕ) : Prop :=
  p.Prime ∧ (3 * p - 4).Prime ∧ (3 * p - 10).Prime ∧ (3 * p - 14).Prime

theorem main :
    ∀ n : ℕ, 17 < n → ∃ p q r s : ℕ, p ≤ q ∧ q ≤ r ∧ r ≤ s ∧
      InA230223 p ∧ InA230223 q ∧ InA230223 r ∧ InA230223 s ∧ p + q + r + s = 2 * n := by
  sorry

end OMA.S_oeis_a230224
