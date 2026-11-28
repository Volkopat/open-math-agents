import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R2

/-! Separate the four lower support sizes among the multiples of three. -/

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R2_H3_R1

def H1 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    3 ∣ n → n.primeFactors.card = 6 → n.Pseudoperfect

def H2 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    3 ∣ n → n.primeFactors.card = 7 → n.Pseudoperfect

def H3 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    3 ∣ n → n.primeFactors.card = 8 → n.Pseudoperfect

def H4 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    3 ∣ n → n.primeFactors.card = 9 → n.Pseudoperfect

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R2.H3 := by
  intro h6 h7 h8 h9 n hn ho ha hp h3 hlo hhi
  have hcard : n.primeFactors.card = 6 ∨ n.primeFactors.card = 7 ∨
      n.primeFactors.card = 8 ∨ n.primeFactors.card = 9 := by omega
  rcases hcard with h | h | h | h
  · exact h6 n hn ho ha hp h3 h
  · exact h7 n hn ho ha hp h3 h
  · exact h8 n hn ho ha hp h3 h
  · exact h9 n hn ho ha hp h3 h

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R2_H3_R1
