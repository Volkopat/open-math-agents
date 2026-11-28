import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1

/-! Split the two remaining support sizes, and split support thirteen by the
exponent at five. -/

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1_H4_R1

def H1 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 12 → n.Pseudoperfect

def H2 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 13 → n.factorization 5 ≤ 1 → n.Pseudoperfect

def H3 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 13 → n.factorization 5 = 2 → n.Pseudoperfect

def H4 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 13 → 3 ≤ n.factorization 5 → n.Pseudoperfect

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1.H4 := by
  intro h1 h2 h3 h4 n hn ho ha hp h3nd hlo hhi
  by_cases htwelve : n.primeFactors.card = 12
  · exact h1 n hn ho ha hp h3nd htwelve
  have hthirteen : n.primeFactors.card = 13 := by omega
  by_cases hone : n.factorization 5 ≤ 1
  · exact h2 n hn ho ha hp h3nd hthirteen hone
  by_cases htwo : n.factorization 5 = 2
  · exact h3 n hn ho ha hp h3nd hthirteen htwo
  exact h4 n hn ho ha hp h3nd hthirteen (by omega)

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1_H4_R1
