import Mathlib

/-!
# A213980: a(n) is the minimum number of iterations of f(n) = n + Omega(n) - 1 that results in a prime number, where Omega(n) is the number of prime factors of n, counted with multiplicity, or A001222(n).

Source: https://oeis.org/A213980
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A213980 (Vladimir Shevelev, Feb 15 2013):
a(n) exists for every n >= 2.

Conventions:
* The sequence has offset 2 (data 0, 0, 1, 0, 1, 0, 2, 2, 1, 0, 4, 0, ...).
* f(m) = m + Omega(m) - 1, where Omega is `ArithmeticFunction.cardFactors` (number of prime
  factors counted with multiplicity). For m >= 2 we have Omega(m) >= 1, so the natural
  subtraction is exact, and f(m) >= m >= 2 again.
* a(n) exists exactly when some iterate f^k(n), k >= 0, is prime (k = 0 when n itself is
  prime, as in a(2) = 0); the iterate is `f^[k] n`. The conjecture is stated in this form.
-/

namespace OMA.S_oeis_a213980

/-- f(m) = m + Omega(m) - 1. -/
def f (m : ℕ) : ℕ := m + ArithmeticFunction.cardFactors m - 1

/-- The conjecture: for every n >= 2 some iterate of f starting at n is prime. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, (f^[k] n).Prime := by
  sorry

end OMA.S_oeis_a213980
