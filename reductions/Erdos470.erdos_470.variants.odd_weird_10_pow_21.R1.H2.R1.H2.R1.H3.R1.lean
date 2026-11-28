import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1

/-! Separate the two support sizes, and use divisibility by eleven at support ten. -/

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1_H3_R1

def H1 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 10 → ¬ 11 ∣ n → n.Pseudoperfect

def H2 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 10 → 11 ∣ n → n.Pseudoperfect

def H3 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 11 → n.Pseudoperfect

theorem main : H1 → H2 → H3 →
    OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1.H3 := by
  intro hnotEleven hEleven h11 n hn ho ha hp h3 hlo hhi
  by_cases hten : n.primeFactors.card = 10
  · by_cases h11d : 11 ∣ n
    · exact hEleven n hn ho ha hp h3 hten h11d
    · exact hnotEleven n hn ho ha hp h3 hten h11d
  · exact h11 n hn ho ha hp h3 (by omega)

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1_H3_R1
