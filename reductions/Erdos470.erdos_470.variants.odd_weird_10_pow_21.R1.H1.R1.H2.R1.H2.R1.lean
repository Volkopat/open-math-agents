import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1_H2_R1
import Mathlib

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1_H2_R1_H2_R1

open Finset ArithmeticFunction

def H1 : Prop :=
  ∀ b q j : ℕ, 1 < b → q.Prime → 3 ≤ q → b.Coprime q →
    (∀ p ∈ b.primeFactors, p < q) →
    let n := b*q^(j+2)
    n < 10^21 → Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) → 3 ∣ n →
    n.primeFactors.card = 5 →
    let E : ℤ := (sigma 1 n : ℤ) - 2*(n : ℤ)
    let P := ∑ d ∈ b.properDivisors, (d : ℤ)
    let D := (b : ℤ)-P
    let r := (2*P)%D
    0 < D → 0 < r → (q : ℤ) = (2*P)/D+2 →
    r*(q:ℤ)^(j+1) < 2*P+D → 2*P+D < r*(q:ℤ)^(j+2) →
    ∃ s ⊆ n.properDivisors.filter (fun d : ℕ => (d : ℤ) ≤ E), (∑ d ∈ s, (d : ℤ)) = E

def H2 : Prop :=
  ∀ b q j : ℕ, 1 < b → q.Prime → 3 ≤ q → b.Coprime q →
    (∀ p ∈ b.primeFactors, p < q) →
    let n := b*q^(j+2)
    n < 10^21 → Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) → 3 ∣ n →
    5 < n.primeFactors.card →
    let E : ℤ := (sigma 1 n : ℤ) - 2*(n : ℤ)
    let P := ∑ d ∈ b.properDivisors, (d : ℤ)
    let D := (b : ℤ)-P
    let r := (2*P)%D
    let R := fun x : ℤ => ∃ s ⊆ b.properDivisors, (∑ d ∈ s, (d : ℤ)) = x
    let G : ℤ := Nat.gcd (sigma 1 b) (2*b)
    0 < D → 0 < r → (q : ℤ) = (2*P)/D+2 →
    r*(q:ℤ)^(j+1) < 2*P+D → 2*P+D < r*(q:ℤ)^(j+2) →
    (¬ ∃ s ⊆ b.divisors, (∑ d ∈ s, (d : ℤ)) = E) →
    G ∣ E → 0 < E →
    (∀ L g : ℤ, 1 ≤ L → 1 ≤ g → (2*g+1)*(2*L+8*g+8) ≤ P →
      (∀ y : ℤ, L ≤ y → y ≤ P-L → R y) →
      (∀ k : ℤ, 0 ≤ k → k < P → ∃ i : ℤ, R i ∧ k-g < i ∧ i ≤ k) →
      E < L ∧ G < L) →
    ∃ s ⊆ n.properDivisors.filter (fun d : ℕ => (d : ℤ) ≤ E), (∑ d ∈ s, (d : ℤ)) = E

theorem main : H1 → H2 → OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1_H2_R1.H2 := by
  intro exactlyFive moreThanFive b q j bp prime q3 cop largest
  dsimp only
  intro size odd abundant primitive three count dPos rPos quot low high missing divides positive noInterval
  by_cases eq : (b*q^(j+2)).primeFactors.card = 5
  · exact exactlyFive b q j bp prime q3 cop largest size odd abundant primitive three eq
      dPos rPos quot low high
  · exact moreThanFive b q j bp prime q3 cop largest size odd abundant primitive three (by omega)
      dPos rPos quot low high missing divides positive noInterval

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1_H2_R1_H2_R1