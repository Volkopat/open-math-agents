import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R2

-- Reduction Erdos1052.erdos_1052.R2.H2.R2.H1.R1 of step H1 of Erdos1052.erdos_1052.R2.H2.R2
-- Credit: @eltociear
-- Splits the pair bound into the case of two distinct primes of 2^a+1 that both lie in S
-- (H1, the remaining hard case) and everything else (H2, where the bound B := c works:
-- if one of the primes divides c it is at most c, the diagonal case p = r gives p ∣ c,
-- and a prime of 2^a+1 outside S must divide c).

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R1

def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ B : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      ∀ p r : ℕ, p.Prime → r.Prime → p*r ∣ 2^a+1 → p ∈ S → r ∈ S → p ≠ r → min p r ≤ B

def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      ∀ p r : ℕ, p.Prime → r.Prime → p*r ∣ 2^a+1 →
      ¬ (p ∈ S ∧ r ∈ S ∧ p ≠ r) → min p r ≤ c

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R2.H1 := by
  intro h1 h2 c hc hpow
  obtain ⟨B, hB⟩ := h1 c hc hpow
  refine ⟨max B c, ?_⟩
  intro a S b u ha hcard hsub hS heq p r hp hr hpr
  by_cases hhard : p ∈ S ∧ r ∈ S ∧ p ≠ r
  · exact le_trans (hB a S ha hcard hsub hS heq p r hp hr hpr hhard.1 hhard.2.1 hhard.2.2)
      (Nat.le_max_left _ _)
  · exact le_trans (h2 c hc hpow a S ha hcard hsub hS heq p r hp hr hpr hhard)
      (Nat.le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H1_R1
