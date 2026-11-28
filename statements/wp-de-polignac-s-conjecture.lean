import Mathlib

/-!
# De Polignac's conjecture

Source: https://en.wikipedia.org/wiki/De_Polignac%27s_conjecture
Credit: @Andyi955

In number theory, Polignac's conjecture was made by Alphonse de Polignac in 1849 and states: for any
positive even number `n`, there are infinitely many prime gaps of size `n`; in other words, there
are infinitely many cases of two consecutive prime numbers with difference `n`
(Wikipedia, Polignac's conjecture). It is open; `n = 2` is the twin prime conjecture.

## Encoding

* A prime gap of size `n` is a pair of consecutive primes `p < q` with `q - p = n`, written here as
  `q = p + n` together with the requirement that no prime lies strictly between `p` and `p + n`.
  This is the source's second phrasing, which makes consecutiveness explicit.
* `p` determines the pair, so the conjecture is stated as the set of lower members `p` being
  infinite. `p + n` keeps the ordering, so no pair is counted twice.
* `0 < n` and `Even n` are the source's positive even numbers; `Nat.Prime` is Mathlib's prime
  predicate.
-/

namespace OMA.S_wp_de_polignac_s_conjecture

/-- **De Polignac's conjecture**: for every positive even `n` there are infinitely many prime gaps
of size `n`, i.e. infinitely many primes `p` such that `p + n` is the next prime after `p`. -/
theorem main : ∀ n : ℕ, 0 < n → Even n →
    {p : ℕ | p.Prime ∧ (p + n).Prime ∧ ∀ q : ℕ, p < q → q < p + n → ¬ q.Prime}.Infinite := by
  sorry

end OMA.S_wp_de_polignac_s_conjecture
