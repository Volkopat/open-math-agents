import Mathlib

/-!
# A285797: Number of ways to write n as an ordered sum of two numbers that are the product of an odd number of distinct primes.

Source: https://oeis.org/A285797
Credit: @keiichisince1986-bot

A285797 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 57.

Conventions:
- A product of an odd number of distinct primes is a squarefree number with an odd number of
  prime factors (A030059: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 30, 31, …).
- `a(n) > 0` means that `n = a + b` for two such numbers `a, b`.
-/

namespace OMA.S_oeis_a285797

/-- `a` is a product of an odd number of distinct primes. -/
def IsOddDistinctPrimeProduct (a : ℕ) : Prop :=
  Squarefree a ∧ Odd a.primeFactors.card

theorem main :
    ∀ n : ℕ, 57 < n → ∃ a b : ℕ, IsOddDistinctPrimeProduct a ∧ IsOddDistinctPrimeProduct b ∧
        n = a + b := by
  sorry

end OMA.S_oeis_a285797
