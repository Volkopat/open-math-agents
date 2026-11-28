import Mathlib

/-!
# A007850: Giuga numbers and the arithmetic derivative

Source: https://oeis.org/A007850
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A007850): the Giuga numbers are the solutions of the differential equation
`n' = n + 1`, where `n'` is the arithmetic derivative of `n`.

Conventions:
* A Giuga number is a composite `n` such that `p ∣ n/p - 1` for every prime divisor `p` of `n`.
* The arithmetic derivative: `0' = 1' = 0`, `p' = 1` for primes, `(ab)' = a'b + ab'`; for
  `n = ∏ pᵢ^{eᵢ}` it equals `∑ eᵢ n / pᵢ`.
* "Are the solutions": for every positive integer `n`, `n` is a Giuga number iff `n' = n + 1`.
-/

namespace OMA.S_oeis_a007850

/-- The arithmetic derivative of `n ≥ 1`. -/
def arithDeriv (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n.factorization p * (n / p)

/-- Giuga numbers. -/
def IsGiuga (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ p ∈ n.primeFactors, p ∣ n / p - 1

theorem main : ∀ n : ℕ, 0 < n → (IsGiuga n ↔ arithDeriv n = n + 1) := by
  sorry

end OMA.S_oeis_a007850
