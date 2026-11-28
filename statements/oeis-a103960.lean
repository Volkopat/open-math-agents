import Mathlib

/-!
# A103960: Number of primes p such that prime(n)*p - 2 is prime and p <= prime(n).

Source: https://oeis.org/A103960
Credit: @divmxnd0x

Conjecture (stated in A103960): all items of this sequence are greater than or equal to 1
(tested to `prime(1000000)`).

Formalization notes:
* `prime n` is the `n`-th prime (`prime 1 = 2`); `a(n) ≥ 1` means that there is a prime
  `p ≤ prime n` with `prime n * p - 2` prime.
-/

namespace OMA.S_oeis_a103960

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- For every `n ≥ 1` there is a prime `p ≤ prime n` with `prime n * p - 2` prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ p ≤ prime n ∧ (prime n * p - 2).Prime := by
  sorry

end OMA.S_oeis_a103960
