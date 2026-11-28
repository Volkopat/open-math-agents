import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1

/-! Separate the support-nine case by the valuation at five. -/

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1_H2_R1

def H1 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 9 → n.factorization 5 ≤ 1 → n.Pseudoperfect

def H2 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 9 → 2 ≤ n.factorization 5 → n.Pseudoperfect

theorem main : H1 → H2 →
    OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1.H2 := by
  intro hlow hraised n hn ho ha hp h3 hc
  by_cases he : n.factorization 5 ≤ 1
  · exact hlow n hn ho ha hp h3 hc he
  · exact hraised n hn ho ha hp h3 hc (by omega)

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1_H2_R1
