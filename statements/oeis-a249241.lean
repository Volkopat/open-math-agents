import Mathlib

/-!
# A249241: a(n) = p - prime(n)!/prime(n)#, where p is the smallest prime number > prime(n)!/prime(n)#+1.

Source: https://oeis.org/A249241
Credit: @azmiozgen

Conjecture (from the entry): all terms are prime.

Formalization notes:
* prime(n) = `Nat.nth Nat.Prime (n - 1)` (prime(1) = 2); q# = `primorial q`, the product of the
  primes ≤ q, which divides q!, so x(n) = prime(n)! / prime(n)# is exact.
* p is the least prime with p > x(n) + 1, and a(n) = p - x(n) (offset 1).
* Controls (computed): a(1..19) = 2, 2, 3, 5, 11, 7, 29, 17, 17, 397, 47, 67, 23, 41, 31, 157, 409,
  31, 151, as in the entry; a(n) is prime for n < 40.
-/

namespace OMA.S_oeis_a249241

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `x(n) = prime(n)! / prime(n)#`. -/
noncomputable def x (n : ℕ) : ℕ := (prime n).factorial / primorial (prime n)

/-- A249241(n) = p - x(n), with `p` the least prime greater than `x(n) + 1`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ x n + 1 < p} - x n

/-- All terms are prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n).Prime := by
  sorry

end OMA.S_oeis_a249241
