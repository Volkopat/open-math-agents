import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1

/-! Divide the support-eight case by the exponent at its least prime, five. -/

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 8 → n.factorization 5 ≤ 8 →
    n.factorization 5 ≠ 2 → n.factorization 5 ≠ 6 → n.Pseudoperfect

def H2 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 8 → n.factorization 5 = 2 → n.Pseudoperfect

def H3 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 8 → n.factorization 5 = 6 → n.Pseudoperfect

def H4 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 8 → 9 ≤ n.factorization 5 → n.Pseudoperfect

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1.H1 := by
  intro h1 h2 h3 h4 n hn ho ha hp h3nd hc
  by_cases htwo : n.factorization 5 = 2
  · exact h2 n hn ho ha hp h3nd hc htwo
  by_cases hsix : n.factorization 5 = 6
  · exact h3 n hn ho ha hp h3nd hc hsix
  by_cases hlarge : 9 ≤ n.factorization 5
  · exact h4 n hn ho ha hp h3nd hc hlarge
  exact h1 n hn ho ha hp h3nd hc (by omega) htwo hsix

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H1_R1
