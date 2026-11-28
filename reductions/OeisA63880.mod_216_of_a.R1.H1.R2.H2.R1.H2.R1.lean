import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1

-- Reduction OeisA63880.mod_216_of_a.R1.H1.R2.H2.R1.H2.R1 of step
-- OeisA63880.mod_216_of_a.R1.H1.R2.H2.R1.H2
-- Credit: @Ciphore
-- The powerful-core problem splits by the parity of the exponents. If every exponent
-- is even the core is a perfect square; otherwise some prime occurs to an odd exponent
-- at least three, and the 2-adic valuation structure changes completely.

/-!
## Reduction of the powerful-core step

A powerful odd number either has all prime exponents even — equivalently it is a perfect
square — or it has some prime factor occurring to an odd exponent. The two cases are
attacked by different arithmetic: the perfect-square case by the parity of the divisor
sum, the odd-exponent case by the 2-adic valuation sieve.
-/

namespace OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1_H2_R1

open OeisA63880
open scoped ArithmeticFunction.sigma

/-- The even-exponent case of the powerful-core problem: every prime factor of `d` occurs
    to an even exponent, so `d` is a perfect square. -/
def H1 : Prop := ∀ d : ℕ, Odd d →
  (∀ q : ℕ, q.Prime → q ∣ d → 2 ≤ d.factorization q) →
  (∀ q : ℕ, q.Prime → q ∣ d → Even (d.factorization q)) → ¬ OeisA63880.A d

/-- The odd-exponent case of the powerful-core problem: some prime factor of `d` occurs
    to an odd exponent (necessarily at least three). -/
def H2 : Prop := ∀ d : ℕ, Odd d →
  (∀ q : ℕ, q.Prime → q ∣ d → 2 ≤ d.factorization q) →
  (∃ q : ℕ, q.Prime ∧ q ∣ d ∧ Odd (d.factorization q)) → ¬ OeisA63880.A d

theorem main : H1 → H2 → OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1.H2 := by
  intro heven hodd d hod hpow hA
  by_cases hall : (∀ q : ℕ, q.Prime → q ∣ d → Even (d.factorization q))
  · exact heven d hod hpow hall hA
  · push Not at hall
    obtain ⟨q, hq, hqd, hneven⟩ := hall
    have hoddexp : Odd (d.factorization q) := Nat.not_even_iff_odd.mp hneven
    exact hodd d hod hpow ⟨q, hq, hqd, hoddexp⟩ hA

end OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1_H2_R1
