import OMAReductions.R_Erdos982_erdos_982_R1_H1_R1_H2_R1

namespace OMA.R_Erdos982_erdos_982_R1_H1_R1_H2_R1_H3_R1

private structure MaskClaim (P : Prop) where
  expect : Nat → Prop
  eq : P = (∀ m ∈ [515, 832, 19, 42], expect m)

private def claim : MaskClaim OMA.R_Erdos982_erdos_982_R1_H1_R1_H2_R1.H3 := by
  unfold OMA.R_Erdos982_erdos_982_R1_H1_R1_H2_R1.H3
  exact ⟨_, rfl⟩

def H1 : Prop := claim.expect 515

def H2 : Prop := claim.expect 832

def H3 : Prop := claim.expect 19

def H4 : Prop := claim.expect 42

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos982_erdos_982_R1_H1_R1_H2_R1.H3 := by
  intro h1 h2 h3 h4
  apply claim.eq.mpr
  intro m member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

end OMA.R_Erdos982_erdos_982_R1_H1_R1_H2_R1_H3_R1