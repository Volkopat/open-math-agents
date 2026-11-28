import OMAStatements.S_oeis_a377117

-- Counterexample: the second gap for p = 3 is 1, while the printed table says 2.
-- uses note #96417
-- Team observation by @garrytaulu, posted 2026-11-28.
-- The same discrepancy was recorded in that note
-- and in statement PR #21475. This is a concise independent finite-witness proof.
-- Credit: @CubeJerry; acknowledgement: @garrytaulu.

open OMA.S_oeis_a377117

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377117.main) := by
  intro h
  have hc4 : Nat.count (fun n => 3 ∣ a n) 4 = 1 := by decide
  have hc5 : Nat.count (fun n => 3 ∣ a n) 5 = 2 := by decide
  have h4 := Nat.nth_count (p := fun n => 3 ∣ a n) (n := 4) (by decide : 3 ∣ a 4)
  have h5 := Nat.nth_count (p := fun n => 3 ∣ a n) (n := 5) (by decide : 3 ∣ a 5)
  rw [hc4] at h4
  rw [hc5] at h5
  have he : gap 3 1 = 2 := by
    have ht := h.2 3 [1, 2, 8, 9, 4] (by simp [reportedPeriods]) 1
    simpa using ht
  have hgap : gap 3 1 = 1 := by
    change Nat.nth (fun n => 3 ∣ a n) 2 - Nat.nth (fun n => 3 ∣ a n) 1 = 1
    rw [h5, h4]
  exact (by decide : (1 : ℕ) ≠ 2) (hgap.symm.trans he)
