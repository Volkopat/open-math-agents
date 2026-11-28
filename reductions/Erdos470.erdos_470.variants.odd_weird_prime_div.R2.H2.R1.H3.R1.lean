import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1

-- Reduction Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2.R1.H3.R1 of step
-- Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2.R1.H3
-- Credit: @Ciphore
-- The leaf already isolates the two smallest possible extra primes. Their abundancy
-- contributions `12/11` and `14/13` differ enough that the exponent budgets compatible
-- with primitive abundance must be enumerated separately.

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H3_R1

/-- The `11`-witness case of the multiples-of-45 leaf. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card ≤ 5 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 45 ∣ n → ¬7 ∣ n → 11 ∣ n → n.Pseudoperfect

/-- The `13`-witness case of the multiples-of-45 leaf. -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card ≤ 5 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 45 ∣ n → ¬7 ∣ n → 13 ∣ n → n.Pseudoperfect

theorem main : H1 → H2 →
    OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1.H3 := by
  intro h11 h13 n ho ha hc hp h45 h7 hor
  rcases hor with h | h
  · exact h11 n ho ha hc hp h45 h7 h
  · exact h13 n ho ha hc hp h45 h7 h

end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H3_R1
