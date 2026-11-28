import Mathlib

/-!
# A237184: Number of ordered ways to write n = (1+(n mod 2))*p + q with p, q, phi(p+1) - 1 and phi(q-1) + 1 all prime.

Source: https://oeis.org/A237184
Credit: @eltociear

`a(n)` (offset 1) counts the ordered ways to write `n = (1 + (n mod 2)) p + q` with `p`, `q`,
`φ(p + 1) - 1` and `φ(q - 1) + 1` all prime; so `n = p + q` for even `n` and `n = 2p + q` for odd
`n`. The entry conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n > 23.

`main` states that such `p`, `q` exist for every `n > 23`. `φ` is `Nat.totient`. The subtractions
are natural-number subtractions: `φ(p + 1) ≥ 1`, and `q - 1` is exact because `q` is prime.
-/

namespace OMA.S_oeis_a237184


/-- The conjecture in OEIS A237184: for every `n > 23` there are primes `p`, `q` with
`n = (1 + n % 2) p + q`, `φ(p + 1) - 1` prime and `φ(q - 1) + 1` prime. -/
theorem main : ∀ n : ℕ, 23 < n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = (1 + n % 2) * p + q ∧
      (Nat.totient (p + 1) - 1).Prime ∧ (Nat.totient (q - 1) + 1).Prime := by
  sorry

end OMA.S_oeis_a237184
