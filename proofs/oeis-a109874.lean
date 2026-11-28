import OMAStatements.S_oeis_a109874

open OMA.S_oeis_a109874 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a109874.main) := by
  intro H
  have := H.2.2 15 (by norm_num) ⟨7, rfl⟩ (by norm_num)
  have h := Nat.findGreatest_spec (P := (15 ^ · ∣ P 15)) (n := P 15) (Nat.zero_le _) (by simp)
  unfold a at this
  rw [show Nat.findGreatest _ _ = 13 by omega] at h
  revert h
  decide +kernel
