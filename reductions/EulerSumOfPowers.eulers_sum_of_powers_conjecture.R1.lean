import FormalConjectures.Wikipedia.EulerSumOfPowers

-- Reduction EulerSumOfPowers.eulers_sum_of_powers_conjecture.R1 of Euler's sum of powers conjecture (k at least 6)
-- Credit: @marcusbuffett

/-!
# Euler's sum of powers conjecture: the two-term case is Fermat's Last Theorem

For `k ≥ 6` the conjecture says that `k` positive `k`-th powers at least are needed to sum to a
`k`-th power. With `n = 2` terms it asserts that `x^k + y^k = b^k` has no positive solution,
which is Fermat's Last Theorem for the exponent `k`.

* `H1` (classical): two terms, exponent divisible by `3` or by `4`. Fermat's Last Theorem for
  the exponents `3` (Euler) and `4` (Fermat) is in Mathlib and passes to multiples.
* `H2` (Wiles, Taylor-Wiles; not available in Lean): two terms, any other exponent `k ≥ 6`.
* `H3` (open): three or more terms.
-/

namespace OMA.R_EulerSumOfPowers_eulers_sum_of_powers_conjecture_R1

/-- Two terms, exponent a multiple of three or of four: no solution. -/
def H1 : Prop :=
  ∀ k b : ℕ, 5 < k → (3 ∣ k ∨ 4 ∣ k) → ∀ a : Fin 2 → ℕ, (∀ i, a i > 0) →
    ∑ i, (a i) ^ k ≠ b ^ k

/-- Two terms, the other exponents: Fermat's Last Theorem. -/
def H2 : Prop :=
  ∀ k b : ℕ, 5 < k → ¬ 3 ∣ k → ¬ 4 ∣ k → ∀ a : Fin 2 → ℕ, (∀ i, a i > 0) →
    ∑ i, (a i) ^ k ≠ b ^ k

/-- The open part: three or more terms. -/
def H3 : Prop :=
  ∀ n k b : ℕ, 2 < n → 5 < k → ∀ a : Fin n → ℕ, (∀ i, a i > 0) →
    ∑ i, (a i) ^ k = b ^ k → k ≤ n

theorem main : H1 → H2 → H3 →
    type_of% @EulerSumOfPowers.eulers_sum_of_powers_conjecture := by
  intro h1 h2 h3 n k b hn hk a ha hsum
  by_cases hn2 : 2 < n
  · exact h3 n k b hn2 hk a ha hsum
  · obtain rfl : n = 2 := by omega
    exfalso
    by_cases hd : 3 ∣ k ∨ 4 ∣ k
    · exact h1 k b hk hd a ha hsum
    · have hd3 : ¬ 3 ∣ k := fun h => hd (Or.inl h)
      have hd4 : ¬ 4 ∣ k := fun h => hd (Or.inr h)
      exact h2 k b hk hd3 hd4 a ha hsum

end OMA.R_EulerSumOfPowers_eulers_sum_of_powers_conjecture_R1
