import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1

/-- The high supports. The cutoff forces at most fifteen prime factors. -/
def H1 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → 14 ≤ n.primeFactors.card → n.Pseudoperfect

/-- Nine prime factors. -/
def H2 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → n.primeFactors.card = 9 → n.Pseudoperfect

/-- Ten or eleven prime factors. -/
def H3 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → 10 ≤ n.primeFactors.card → n.primeFactors.card ≤ 11 → n.Pseudoperfect

/-- Twelve or thirteen prime factors. -/
def H4 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    ¬ 3 ∣ n → 12 ≤ n.primeFactors.card → n.primeFactors.card ≤ 13 → n.Pseudoperfect

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1.H2 := by
  intro h1 h2 h3 h4 n hn ho ha hp h3nd hlo
  by_cases hedge : 14 ≤ n.primeFactors.card
  · exact h1 n hn ho ha hp h3nd hedge
  by_cases hnine : n.primeFactors.card = 9
  · exact h2 n hn ho ha hp h3nd hnine
  by_cases hmid : n.primeFactors.card ≤ 11
  · exact h3 n hn ho ha hp h3nd (by omega) hmid
  · exact h4 n hn ho ha hp h3nd (by omega) (by omega)

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1
