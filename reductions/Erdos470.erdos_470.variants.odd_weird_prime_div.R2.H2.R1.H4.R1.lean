import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1
import Mathlib.Data.Nat.Factorization.Basic

/-! Split by the least prime factor after 3 and 5. -/

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H4_R1

def H1 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → 4 ≤ n.primeFactors.card → n.primeFactors.card ≤ 5 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 45 ∣ n → ¬7 ∣ n → ¬11 ∣ n → ¬13 ∣ n →
    17 ∣ n → n.Pseudoperfect

def H2 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → 4 ≤ n.primeFactors.card → n.primeFactors.card ≤ 5 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 45 ∣ n → ¬7 ∣ n → ¬11 ∣ n → ¬13 ∣ n →
    ¬17 ∣ n → 19 ∣ n → n.Pseudoperfect

def H3 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → 4 ≤ n.primeFactors.card → n.primeFactors.card ≤ 5 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 45 ∣ n → ¬7 ∣ n → ¬11 ∣ n → ¬13 ∣ n →
    ¬17 ∣ n → ¬19 ∣ n → (∃ r ∈ ([17,19,23,29,31,37,41,43] : List ℕ), r ∣ n) → n.Pseudoperfect

theorem main : H1 → H2 → H3 → OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1.H4 := by
  intro h1 h2 h3 n ho ha hcardLo hcardHi hp h45 h7 h11 h13 hsmall
  by_cases h17 : 17 ∣ n
  · exact h1 n ho ha hcardLo hcardHi hp h45 h7 h11 h13 h17
  by_cases h19 : 19 ∣ n
  · exact h2 n ho ha hcardLo hcardHi hp h45 h7 h11 h13 h17 h19
  · exact h3 n ho ha hcardLo hcardHi hp h45 h7 h11 h13 h17 h19 hsmall

end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H4_R1
