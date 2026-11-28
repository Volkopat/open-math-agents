import OMAReductions.R_Erdos848_erdos_848_R3_H3_R1
/- MacchaCat/erdos848 99b8d9bf40fdd090a2a117328c5707ca21ec748e (Apache-2.0).
Below the breakpoint the elementary Chebyshev estimate is insufficient for these rows. -/
namespace OMA.R_Erdos848_erdos_848_R3_H3_R1_H1_R1
def H1 : Prop := ∀ N : ℕ, 160000000 ≤ N → N ≤ 1618722525 → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
  (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a*b+1)) → A.card ≤ (N+18)/25
def H2 : Prop := ∀ N : ℕ, 1618722525 ≤ N → N ≤ 10^60 → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
  (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a*b+1)) → A.card ≤ (N+18)/25
theorem main : H1 → H2 → OMA.R_Erdos848_erdos_848_R3_H3_R1.H1 := by
  intro low high N hN hM
  by_cases h : N ≤ 1618722525
  · exact low N hN h
  · exact high N (by omega) hM
end OMA.R_Erdos848_erdos_848_R3_H3_R1_H1_R1
