import Mathlib

/-!
# OEIS A143898: the least exponent K with a prime in every interval (n^K, (n+1)^K)

Source: https://oeis.org/A143898
`a n` is the number of primes between `n^K` and `(n+1)^K` with `K = log 1151 / log 95`.
Conjecture: this `K` is the least exponent such that there is at least one prime in
`(n^K, (n+1)^K)` for every `n > 0`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a143898

open Real

/-- Every interval `(n^K, (n+1)^K)` with `n ≥ 1` contains a prime. -/
def PrimeInEveryInterval (K : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ (n : ℝ) ^ K < p ∧ (p : ℝ) < ((n : ℝ) + 1) ^ K

theorem main : IsLeast {K : ℝ | PrimeInEveryInterval K} (log 1151 / log 95) := by
  sorry

end OMA.S_oeis_a143898
