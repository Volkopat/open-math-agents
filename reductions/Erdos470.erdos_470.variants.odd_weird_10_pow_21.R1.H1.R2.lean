import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1

/-! Partition the multiples-of-three case by distinct-prime support. -/

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R2

def H1 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    3 ∣ n → 14 ≤ n.primeFactors.card → n.Pseudoperfect

def H2 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    3 ∣ n → n.primeFactors.card ≤ 5 → n.Pseudoperfect

def H3 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    3 ∣ n → 6 ≤ n.primeFactors.card → n.primeFactors.card ≤ 9 → n.Pseudoperfect

def H4 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) →
    3 ∣ n → 10 ≤ n.primeFactors.card → n.primeFactors.card ≤ 13 → n.Pseudoperfect

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1.H1 := by
  intro h1 h2 h3 h4 n hn ho ha hp hd
  by_cases hhigh : 14 ≤ n.primeFactors.card
  · exact h1 n hn ho ha hp hd hhigh
  by_cases hlow : n.primeFactors.card ≤ 5
  · exact h2 n hn ho ha hp hd hlow
  by_cases hmid : n.primeFactors.card ≤ 9
  · exact h3 n hn ho ha hp hd (by omega) hmid
  · exact h4 n hn ho ha hp hd (by omega) (by omega)

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R2
