import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2

-- Reduction Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H1.R1
-- Credit: @Ciphore
-- Splits the multiples-of-15 leaf (3 occurring exactly once) by the presence of the prime 7.
-- When 7 divides m the number is a multiple of 105 with abundancy baseline
-- sigma(105)/105 = 192/105 already close to 2, so the remaining budget is tight and the
-- subset-sum structure must be near-exact; when 7 is absent the abundancy must come from
-- smaller witness primes (11, 13, ...) or higher exponents, giving a richer divisor lattice.
-- The two regimes have genuinely different arithmetic, matching the witness-prime logic of
-- the sibling reductions in this tree. Each H becomes its own step once this file is
-- accepted; proving both proves the step.

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H1_R1

/-- The seven-divisible core: multiples of 105. -/
def H1 : Prop :=
  ∀ m : ℕ, Odd m → m.Abundant → m.primeFactors.card ≤ 5 →
    (∀ d ∈ m.properDivisors, d.Deficient) → 15 ∣ m → ¬ 9 ∣ m → 7 ∣ m → m.Pseudoperfect

/-- The seven-free core: multiples of 15 coprime to 7. -/
def H2 : Prop :=
  ∀ m : ℕ, Odd m → m.Abundant → m.primeFactors.card ≤ 5 →
    (∀ d ∈ m.properDivisors, d.Deficient) → 15 ∣ m → ¬ 9 ∣ m → ¬ 7 ∣ m → m.Pseudoperfect

theorem main : H1 → H2 →
    OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2.H1 := by
  intro h7 hno7 m odd ab hc hp h15 h9
  by_cases h7d : 7 ∣ m
  · exact h7 m odd ab hc hp h15 h9 h7d
  · exact hno7 m odd ab hc hp h15 h9 h7d

end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H1_R1
