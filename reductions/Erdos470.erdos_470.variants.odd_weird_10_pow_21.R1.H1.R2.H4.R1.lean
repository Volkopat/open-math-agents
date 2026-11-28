import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R2

/-! Separate the four remaining support sizes among the multiples of three. -/

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R2_H4_R1

def H1 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    3 ∣ n → n.primeFactors.card = 10 → n.Pseudoperfect

def H2 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    3 ∣ n → n.primeFactors.card = 11 → n.Pseudoperfect

def H3 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    3 ∣ n → n.primeFactors.card = 12 → n.Pseudoperfect

def H4 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    3 ∣ n → n.primeFactors.card = 13 → n.Pseudoperfect

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R2.H4 := by
  intro h10 h11 h12 h13 n hn ho ha hp h3 hlo hhi
  have hcard : n.primeFactors.card = 10 ∨ n.primeFactors.card = 11 ∨
      n.primeFactors.card = 12 ∨ n.primeFactors.card = 13 := by omega
  rcases hcard with h | h | h | h
  · exact h10 n hn ho ha hp h3 h
  · exact h11 n hn ho ha hp h3 h
  · exact h12 n hn ho ha hp h3 h
  · exact h13 n hn ho ha hp h3 h

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R2_H4_R1
