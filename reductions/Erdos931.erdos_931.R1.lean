import FormalConjectures.ErdosProblems.«931»
import Mathlib.Order.Interval.Finset.Nat

/-! Separate the configurations with at most three common prime divisors.
The second block is exactly 8,9,10 and the first block ends at 5 or 6. -/

namespace OMA.R_Erdos931_erdos_931_R1

open Finset

def H1 : Prop :=
  ∀ k₁ k₂ n₁ n₂ : ℕ, 3 ≤ k₂ → k₂ ≤ k₁ → n₁ + k₁ ≤ n₂ →
    (((∏ i ∈ Icc 1 k₁, (n₁+i)).primeFactors = (∏ j ∈ Icc 1 k₂, (n₂+j)).primeFactors ∧
      (∏ j ∈ Icc 1 k₂, (n₂+j)).primeFactors.card ≤ 3) ↔
    n₂ = 7 ∧ k₂ = 3 ∧ (n₁+k₁ = 5 ∨ n₁+k₁ = 6))

def H2 : Prop :=
  ∀ k₁ k₂ : ℕ, 3 ≤ k₂ → k₂ ≤ k₁ →
    {z : ℕ × ℕ | z.1+k₁ ≤ z.2 ∧
      (∏ i ∈ Icc 1 k₁, (z.1+i)).primeFactors = (∏ j ∈ Icc 1 k₂, (z.2+j)).primeFactors ∧
      4 ≤ (∏ j ∈ Icc 1 k₂, (z.2+j)).primeFactors.card}.Finite

section Proof

theorem main : H1 → H2 → type_of% @Erdos931.erdos_931 := by
  intro small large k₁ k₂ hk₂ hk₁
  apply (((Set.finite_Iic (7 : ℕ)).prod (Set.finite_Iic (7 : ℕ))).union
    (large k₁ k₂ hk₂ hk₁)).subset
  rintro ⟨n₁,n₂⟩ ⟨hsep,heq⟩
  by_cases h : (∏ j ∈ Icc 1 k₂, (n₂+j)).primeFactors.card ≤ 3
  · left
    have hb := ((small k₁ k₂ n₁ n₂ hk₂ hk₁ hsep).mp ⟨heq,h⟩).1
    exact ⟨by change n₁ ≤ 7; omega, by change n₂ ≤ 7; omega⟩
  · right
    exact ⟨hsep,heq,by change 4 ≤ (∏ j ∈ Icc 1 k₂, (n₂+j)).primeFactors.card; omega⟩

end Proof

end OMA.R_Erdos931_erdos_931_R1
