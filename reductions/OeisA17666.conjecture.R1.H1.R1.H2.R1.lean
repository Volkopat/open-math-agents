import OMAReductions.R_OeisA17666_conjecture_R1_H1_R1

-- Reduction OeisA17666.conjecture.R1.H1.R1.H2.R1 of step OeisA17666.conjecture.R1.H1.R1.H2
-- Credit: @marcusbuffett

/-!
# Odd perfect numbers: exactly three prime factors, and the open rest

The parent step says that no odd `b > 1` with at least three distinct prime factors is perfect.

* `H1` (classical; Peirce 1832, Sylvester 1888): no odd perfect number has exactly three distinct
  prime factors. The bound `2 * ∏ (p - 1) ≤ ∏ p` leaves only the prime supports `{3, 5, 7}`,
  `{3, 5, 11}` and `{3, 5, 13}`; each is excluded by the size of `σ(n) / n` for the admissible
  exponents together with a few divisibility facts (`σ(3^2) = 13`, `σ(3^4) = 11^2`,
  `σ(3^6) = 1093`, `7 ∣ σ(13^c)` for odd `c`, `4 ∣ σ(5^3)`).
* `H2`: no odd perfect number has four or more distinct prime factors. This is the open problem
  and stays open (the literature reaches ten distinct prime factors, Nielsen 2015).
-/

namespace OMA.R_OeisA17666_conjecture_R1_H1_R1_H2_R1

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- No odd perfect number has exactly three distinct prime factors. -/
def H1 : Prop :=
  ∀ b : ℕ, 1 < b → Odd b → b.primeFactors.card = 3 → σ 1 b ≠ 2 * b

/-- The open part: four or more distinct prime factors. -/
def H2 : Prop :=
  ∀ b : ℕ, 1 < b → Odd b → 4 ≤ b.primeFactors.card → σ 1 b ≠ 2 * b

theorem main : H1 → H2 → OMA.R_OeisA17666_conjecture_R1_H1_R1.H2 := by
  intro h1 h2 b hb hodd hc
  by_cases h3 : b.primeFactors.card = 3
  · exact h1 b hb hodd h3
  · exact h2 b hb hodd (by omega)

end OMA.R_OeisA17666_conjecture_R1_H1_R1_H2_R1
