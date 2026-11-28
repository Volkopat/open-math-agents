import Mathlib

/-!
# A338790: a(n) = rad(n)^2 - sigma(n), where rad(n) is the squarefree kernel of n (A007947) and sigma(n) is the sum of divisors of n (A000203).

Source: https://oeis.org/A338790
Credit: @darealpandaboi

Conjecture: only 1 and 1782 satisfy a(x) = 0.

Translation notes.
* rad(n) is the product of the distinct primes dividing n (rad(1) = 1); sigma(n) is
  ArithmeticFunction.sigma 1 n. a(n) = 0 means rad(n)^2 = sigma(n); n ranges over n >= 1.
* The statement says the set of n >= 1 with rad(n)^2 = sigma(n) is exactly {1, 1782}
  (1782 = 2 * 3^4 * 11: rad = 66, 66^2 = 4356 = sigma(1782)). A computer check up to 2*10^6
  finds only these two.
-/

namespace OMA.S_oeis_a338790

/-- The squarefree kernel: the product of the distinct prime factors of n. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem main : {n : ℕ | 0 < n ∧ rad n ^ 2 = ArithmeticFunction.sigma 1 n} = {1, 1782} := by
  sorry

end OMA.S_oeis_a338790
