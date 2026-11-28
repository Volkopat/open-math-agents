import OMAReductions.R_Erdos17_erdos_17_R2

-- Reduction Erdos17.erdos_17.R2.H3.R1 of step Erdos17.erdos_17.R2.H3
-- H1: the analytic counting input (many primes in the block passing the
--     terminal tests, with no packing requirement).
-- H2: the combinatorial packing input (a dense enough subset of a block
--     can be thinned to more than k points separated by 2*k^2).

namespace OMA.R_Erdos17_erdos_17_R2_H3_R1

def H1 : Prop :=
  ∀ N : ℕ, ∃ k ≥ N, ∃ A : Finset ℕ, 4 * k ^ 3 < A.card ∧
    (∀ p ∈ A,
      k ^ 4 ≤ p ∧ p ≤ 2 * k ^ 4 ∧ p.Prime ∧
        ∀ t : ℕ, 3 ≤ t → t ≤ (Nat.log2 (k ^ 4) + 1) ^ 3 → t ≤ p →
          Odd t → ¬ t.Prime → ∃ r : ℕ, r.Prime ∧ (p - t + r).Prime ∧ r ≤ t)

def H2 : Prop :=
  ∀ k : ℕ, ∀ A : Finset ℕ,
    (∀ p ∈ A, k ^ 4 ≤ p ∧ p ≤ 2 * k ^ 4) →
      4 * k ^ 3 < A.card →
        ∃ S : Finset ℕ, S ⊆ A ∧ k < S.card ∧
          ∀ p ∈ S, ∀ q ∈ S, p < q → p + 2 * k ^ 2 ≤ q

theorem main : H1 → H2 → OMA.R_Erdos17_erdos_17_R2.H3 := by
  intro hCount hPack N
  obtain ⟨k, hkN, A, hAcard, hA⟩ := hCount N
  obtain ⟨S, hSA, hScard, hsep⟩ := hPack k A (by
    intro p hp
    exact ⟨(hA p hp).1, (hA p hp).2.1⟩) hAcard
  refine ⟨k, hkN, S, hScard, ?_, hsep⟩
  intro p hp
  exact hA p (hSA hp)

end OMA.R_Erdos17_erdos_17_R2_H3_R1
