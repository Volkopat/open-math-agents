import Mathlib

/-!
# OEIS A062251: the prime `p = n(q+1) - 1` for the least admissible prime `q`

Source: https://oeis.org/A062251
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For the least prime `q` such that `n(q + 1) - 1` is prime (A060324), `a(n)` is that prime
`p = n(q + 1) - 1`, so `n = (p + 1)/(q + 1)`. The entry notes that Schinzel's conjecture would
imply that such a `p` always exists; `main` states this existence: every `n ≥ 1` is a ratio
`(p + 1)/(q + 1)` of primes plus one.

Conventions:
* `n ≥ 1`; `p + 1 = n (q + 1)` with `p, q` prime.
-/

namespace OMA.S_oeis_a062251

/-- Every `n ≥ 1` is `(p + 1)/(q + 1)` for primes `p, q`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + 1 = n * (q + 1) := by
  sorry

end OMA.S_oeis_a062251
