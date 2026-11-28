import Mathlib

/-!
# A349824: a(0) = 0; for n >= 1, a(n) = (number of prime factors, counted with repetition) * (sum of
prime factors, counted with repetition).

Source: https://oeis.org/A349824
Credit: @Squee451

Data (offset 0): 0, 0, 2, 3, 8, 5, 10, 7, 18, 12, 14, 11, 21, 13, 18, 16, 32, 17, 24, 19, 27, 20, 26, 23, 36, ...

The entry's comment: Conjecture (Mike Klein): Iterating n -> a(n) eventually leads to one of the fixed
points {primes union 0, 27, 30} or the loop (28, 33).

Conventions.
* `n.primeFactorsList` is the list of prime factors of `n` with repetition (empty for 0 and 1), so
  `a 0 = a 1 = 0`, as in the data.
* The statement has two parts: the listed values really are fixed points (every prime, 0, 27, 30)
  and 28, 33 really form a loop; and every starting value `n` reaches, after some number of
  iterations (possibly zero), a prime or one of 0, 27, 30, 28, 33.
-/

namespace OMA.S_oeis_a349824

/-- A349824: (number of prime factors with repetition) times (their sum). -/
def a (n : ℕ) : ℕ := n.primeFactorsList.length * n.primeFactorsList.sum

theorem main :
    ((∀ p : ℕ, p.Prime → a p = p) ∧ a 0 = 0 ∧ a 27 = 27 ∧ a 30 = 30 ∧ a 28 = 33 ∧ a 33 = 28) ∧
    ∀ n : ℕ, ∃ t : ℕ, (a^[t] n).Prime ∨ a^[t] n = 0 ∨ a^[t] n = 27 ∨ a^[t] n = 30 ∨
      a^[t] n = 28 ∨ a^[t] n = 33 := by
  sorry

end OMA.S_oeis_a349824
