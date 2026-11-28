import Mathlib

/-!
# A120737: Numbers k whose number of divisors d(k) is divisible by every prime factor of k

Source: https://oeis.org/A120737
Credit: @xor2k

Formalizes the OEIS A120737 conjecture (Ctibor O. Zizka): If A000005(k) divides A007947(k) for
some k, then A007947(k)/A000005(k)=1.

Conventions:
* `k` ranges over the positive integers (the offset of A000005 and A007947 is 1).
* A000005(k), the number of divisors, is `k.divisors.card`.
* A007947(k), the squarefree kernel (largest squarefree divisor, product of the distinct primes
  dividing `k`), is Mathlib's `UniqueFactorizationMonoid.radical k`.
* The quotient is natural-number division; it is exact under the divisibility hypothesis.
-/

namespace OMA.S_oeis_a120737

open UniqueFactorizationMonoid

/-- For every positive `k`, if `d(k)` divides `rad(k)` then `rad(k) / d(k) = 1`. -/
theorem main :
    ∀ k : ℕ, 0 < k → k.divisors.card ∣ radical k → radical k / k.divisors.card = 1 := by
  sorry

end OMA.S_oeis_a120737
