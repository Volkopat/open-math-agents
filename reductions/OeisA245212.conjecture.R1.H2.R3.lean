import OMAReductions.R_OeisA245212_conjecture_R1

-- Reduction OeisA245212.conjecture.R1.H2.R3. Credit: @JaviSoto.
-- At each fixed power of two the part with at most two odd primes
-- has an explicit height. H2 is consequently a finite decision for each k,
-- with no odd primes or exponents prescribed. H3 has at least three odd primes.
namespace OMA.R_OeisA245212_conjecture_R1_H2_R3

open scoped ArithmeticFunction.sigma

def H1 : Prop :=
  ∀ k m : ℕ, 1 ≤ k → Odd m → 1 < m → m.primeFactors.card ≤ 2 →
    OeisA245212.a (2 ^ k * m) = (σ 1 (2 ^ k * m) : ℤ) →
    let t := (k + 1) * 2 ^ k
    let q := 2 * t * (6 * t + 1) + 1
    2 ^ k * m ≤ 4 * (2 ^ k * q ^ (8 * t * q)) ^ 7

def H2 : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    let t := (k + 1) * 2 ^ k
    let q := 2 * t * (6 * t + 1) + 1
    ∀ m : ℕ, 2 ^ k * m ≤ 4 * (2 ^ k * q ^ (8 * t * q)) ^ 7 →
      Odd m → 1 < m → m.primeFactors.card ≤ 2 →
      OeisA245212.a (2 ^ k * m) ≠ (σ 1 (2 ^ k * m) : ℤ)

def H3 : Prop :=
  ∀ k m : ℕ, 1 ≤ k → Odd m → 1 < m → 3 ≤ m.primeFactors.card →
    OeisA245212.a (2 ^ k * m) ≠ (σ 1 (2 ^ k * m) : ℤ)

theorem main : H1 → H2 → H3 → OMA.R_OeisA245212_conjecture_R1.H2 := by
  intro boxes finite many k m pos odd gt eq
  by_cases small : m.primeFactors.card ≤ 2
  · exact finite k pos m (boxes k m pos odd gt small eq) odd gt small eq
  · exact many k m pos odd gt (by omega) eq

end OMA.R_OeisA245212_conjecture_R1_H2_R3
