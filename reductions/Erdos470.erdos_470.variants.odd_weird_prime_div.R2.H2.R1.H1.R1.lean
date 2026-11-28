import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1

-- Reduction Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2.R1.H1.R1
-- Credit: @Ciphore
-- Splits the multiples-of-315 leaf by the size of the remaining prime factors. With the
-- factorizations at 3, 5, 7 fixed (n carries exactly 3^2 * 5 * 7) and one prime in
-- [107, 210), the five-prime-factor count leaves one further prime r below 5565. When a
-- small prime below 210 divides n beyond 3, 5, 7 the divisor lattice is rich and
-- pseudoperfectness is expected from subset-sum structure (this band contains the
-- removable 315r pseudoperfect witnesses of the parent reduction); when no such small
-- prime divides n the remaining primes are large, the abundancy budget is tight, and the
-- ratio constraints force near-exact subset sums. The two regimes are genuinely different
-- arithmetic; each H becomes its own step once this file is accepted.

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H1_R1

/-- The small-prime core: some prime below 210 other than 3, 5, 7 divides n. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card = 5 →
    n.factorization 3 = 2 → n.factorization 5 = 1 → n.factorization 7 = 1 →
    (∃ p : ℕ, p.Prime ∧ 107 ≤ p ∧ p < 210 ∧ p ∣ n) →
    (∀ r ∈ n.primeFactors, r < 5565) →
    (∃ r : ℕ, r.Prime ∧ r < 210 ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ∣ n) → n.Pseudoperfect

/-- The large-prime core: no prime below 210 other than 3, 5, 7 divides n. -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card = 5 →
    n.factorization 3 = 2 → n.factorization 5 = 1 → n.factorization 7 = 1 →
    (∃ p : ℕ, p.Prime ∧ 107 ≤ p ∧ p < 210 ∧ p ∣ n) →
    (∀ r ∈ n.primeFactors, r < 5565) →
    ¬ (∃ r : ℕ, r.Prime ∧ r < 210 ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ∣ n) → n.Pseudoperfect

theorem main : H1 → H2 →
    OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1.H1 := by
  intro hsmall hlarge n odd ab hc h3 h5 h7 hp hr
  by_cases hsmall5 : ∃ r : ℕ, r.Prime ∧ r < 210 ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ∣ n
  · exact hsmall n odd ab hc h3 h5 h7 hp hr hsmall5
  · exact hlarge n odd ab hc h3 h5 h7 hp hr hsmall5

end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H1_R1
