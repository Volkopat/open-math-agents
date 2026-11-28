import Mathlib

/-!
# A005385: Safe primes p: (p-1)/2 is also prime

Source: https://oeis.org/A005385
Credit: @niclorusso

Conjecture (in the comments of A005385): there is a strengthening of the Bertrand postulate for
n >= 24: the interval (n, 2*n) contains a safe prime. It has been tested by Peter J. C. Moses up to
n = 10^7.

Conventions:
* A safe prime is a prime p such that (p - 1)/2 is also prime (the definition of A005385). Every
  such p is odd, so (p - 1)/2 is an exact division; for p = 2 it gives 0, which is not prime.
* (n, 2n) is the open interval: n < p < 2n.
* n ranges over the natural numbers n >= 24.
-/

namespace OMA.S_oeis_a005385

/-- `p` is a safe prime: `p` and `(p - 1) / 2` are both prime (a term of A005385). -/
def IsSafePrime (p : ℕ) : Prop :=
  p.Prime ∧ ((p - 1) / 2).Prime

/-- The conjectured strengthening of Bertrand's postulate: for every `n >= 24` there is a safe
prime `p` with `n < p < 2n`. -/
theorem main : ∀ n : ℕ, 24 ≤ n → ∃ p : ℕ, n < p ∧ p < 2 * n ∧ IsSafePrime p := by
  sorry

end OMA.S_oeis_a005385
