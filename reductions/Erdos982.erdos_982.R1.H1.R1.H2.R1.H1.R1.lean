import OMAReductions.R_Erdos982_erdos_982_R1_H1_R1_H2_R1

namespace OMA.R_Erdos982_erdos_982_R1_H1_R1_H2_R1_H1_R1

private structure MaskClaim (P : Prop) where
  expect : Nat → Prop
  eq : P = (∀ m ∈ [3, 5], expect m)

private def claim : MaskClaim OMA.R_Erdos982_erdos_982_R1_H1_R1_H2_R1.H1 := by
  unfold OMA.R_Erdos982_erdos_982_R1_H1_R1_H2_R1.H1
  exact ⟨_, rfl⟩

def H1 : Prop := claim.expect 3

def H2 : Prop := claim.expect 5

theorem main : H1 → H2 → OMA.R_Erdos982_erdos_982_R1_H1_R1_H2_R1.H1 := by
  intro h1 h2
  apply claim.eq.mpr
  intro m member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact h1
  · exact h2

end OMA.R_Erdos982_erdos_982_R1_H1_R1_H2_R1_H1_R1