import Mathlib

/-!
# Sum of prime and semiprime conjecture

Source: https://www.openproblemgarden.org/op/sum_of_prime_and_semiprime_conjecture
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: the conjecture of Geoffrey Marnell states that every even number greater than `10` can
be represented as the sum of an odd prime number and an odd semiprime, a semiprime being a product
of two primes.

So the proposition formalized below is: every even `n > 10` is `p + s` where `p` is an odd prime and
`s` is the product of two primes, both odd.
-/

namespace OMA.S_opg_sum_of_prime_and_semiprime_conjecture

-- definitions the statement needs (no sorry, no axiom)

/-- `n` is a **semiprime**: a product of two primes. -/
def IsSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p * q = n

/-- The sum of prime and semiprime conjecture. -/
theorem main : ∀ n : ℕ, 10 < n → Even n →
    ∃ p s : ℕ, p.Prime ∧ Odd p ∧ IsSemiprime s ∧ Odd s ∧ p + s = n := by
  sorry

end OMA.S_opg_sum_of_prime_and_semiprime_conjecture
