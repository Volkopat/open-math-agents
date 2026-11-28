import Mathlib

/-!
# Every power of two as a difference of two primes

Source: https://math.stackexchange.com/questions/1861380
Credit: @Andyi955

The question asks (verbatim):

  "Does every power of two arise as the difference of two primes?
  Conjecture: For each `n ∈ ℕ` there are primes `q < p` with `p - q = 2 ^ n`."

## Encoding

* "For each `n ∈ ℕ`" is `∀ n : ℕ`, with no further restriction on `n`.
* "There are primes `q < p` with `p - q = 2 ^ n`" is
  `∃ p q : ℕ, p.Prime ∧ q.Prime ∧ q < p ∧ p - q = 2 ^ n`; since `q < p`, the subtraction `p - q`
  is the ordinary difference of natural numbers.
-/

namespace OMA.S_mse_1861380

theorem main :
    ∀ n : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ q < p ∧ p - q = 2 ^ n := by
  sorry

end OMA.S_mse_1861380
