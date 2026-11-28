import Mathlib

/-!
# A079953: the prime below prime(n) with the greatest remainder is the least prime above prime(n)/2

Source: https://oeis.org/A079953 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A079953, offset 1: Smallest prime p such that prime(n) mod 2*p = prime(n). Data
2, 2, 3, 5, 7, 7, 11, 11, 13, 17, 17, 19, 23, 23, 29, 29, 31, 31, 37, ...
Entry A039734: a(n) = the prime q < prime(n) for which (prime(n) mod q) is maximal.

Formula section of A079953: Conjecture: a(n) = A039734(n), n>=2. - R. J. Mathar, May 03 2021

Formalization notes.
* For n >= 2 the primes prime(n) are the odd primes, so `main` is stated for every prime p >= 3.
* A079953(n) is the least element of the set of the primes q with p mod (2 q) = p, where
  p = prime(n). `main` is stated for every q0 that is the least element of this set (`IsLeast`).
* A039734(n) = q0 means: q0 is a prime below p, and every other prime q below p has a strictly
  smaller remainder p mod q. So the maximum is taken at q0 only.
-/

namespace OMA.S_oeis_a079953

/-- Mathar's conjecture: A079953(n) = A039734(n) for n >= 2. -/
theorem main : ∀ p q0 : ℕ, p.Prime → 3 ≤ p →
    IsLeast {q : ℕ | q.Prime ∧ p % (2 * q) = p} q0 →
    q0.Prime ∧ q0 < p ∧ ∀ q : ℕ, q.Prime → q < p → q ≠ q0 → p % q < p % q0 := by
  sorry

end OMA.S_oeis_a079953
