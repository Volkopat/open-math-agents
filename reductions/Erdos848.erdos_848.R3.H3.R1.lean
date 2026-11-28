import OMAReductions.R_Erdos848_erdos_848_R3
/- MacchaCat/erdos848 99b8d9bf40fdd090a2a117328c5707ca21ec748e (Apache-2.0).
The finite interval uses sieving certificates; beyond its right endpoint the
uniform fourth-root and Pell estimates apply without additional interval rows. -/
namespace OMA.R_Erdos848_erdos_848_R3_H3_R1

def H1 : Prop := ∀ N : ℕ, 160000000 ≤ N → N ≤ 10^60 → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
  (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a*b+1)) → A.card ≤ (N+18)/25

def H2 : Prop := ∀ N : ℕ, 10^60 ≤ N → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
  (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a*b+1)) → A.card ≤ (N+18)/25

theorem main : H1 → H2 → OMA.R_Erdos848_erdos_848_R3.H3 := by
  intro mid tail N hn
  by_cases h : N ≤ 10^60
  · exact mid N hn h
  · exact tail N (Nat.le_of_not_ge h)

end OMA.R_Erdos848_erdos_848_R3_H3_R1
