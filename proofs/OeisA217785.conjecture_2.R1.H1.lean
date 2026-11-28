import OMAReductions.R_OeisA217785_conjecture_2_R1

open OeisA217785

theorem OMA.solution : OMA.R_OeisA217785_conjecture_2_R1.H1 := by
  intro n s _ hns hp hs
  let A : Set ℕ := {t | n < t ∧ Nat.Prime (polyP n t)}
  have hmem : s ∈ A := ⟨hns, hp⟩
  have hleast : sInf A ≤ s :=
    csInf_le ⟨0, fun t _ => Nat.zero_le t⟩ hmem
  refine ⟨sInf A, hleast.trans_lt hs, ?_⟩
  rw [a, if_pos ⟨s, hns, hp⟩]