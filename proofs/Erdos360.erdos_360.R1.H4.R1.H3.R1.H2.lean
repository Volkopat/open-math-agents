import OMAReductions.R_Erdos360_erdos_360_R1_H4_R1_H3_R1

open Finset

theorem OMA.solution : OMA.R_Erdos360_erdos_360_R1_H4_R1_H3_R1.H2 := by
  classical
  intro n S I T a w D p hdis hD hend hcover
  revert hdis hend
  induction T using Finset.induction_on with
  | empty =>
    intro _ _
    exact ⟨a, by simpa using hcover⟩
  | @insert j T hj ih =>
    intro hdis hend
    obtain ⟨hjI, hdisT⟩ := disjoint_insert_right.mp hdis
    obtain ⟨b, hb⟩ := ih hdisT fun i hi => hend i (mem_insert_of_mem hi)
    obtain ⟨x, hx, y, hy, hgap, hwidth⟩ := hend j (mem_insert_self j T)
    have hjU : j ∉ I ∪ T := by simp [hjI, hj]
    refine ⟨b + x, ?_⟩
    rw [card_insert_of_notMem hj, Nat.succ_mul, union_insert]
    intro t ht
    obtain ⟨htlo, hthi⟩ := mem_Icc.mp ht
    -- The old interval translated by x and by y covers the required interval.
    have choice : ∃ z ∈ S j, b ≤ t - z ∧ t - z ≤ b + (w + T.card * p) ∧ z + (t - z) = t := by
      by_cases h : t ≤ b + (w + T.card * p) + x
      · exact ⟨x, hx, by omega, by omega, by omega⟩
      · exact ⟨y, hy, by omega, by omega, by omega⟩
    obtain ⟨z, hz, hlo, hhi, ht'⟩ := choice
    obtain ⟨f, hf, hsum⟩ := hb (t - z) (mem_Icc.mpr ⟨hlo, hhi⟩)
    refine ⟨Function.update f j z, ?_, ?_⟩
    · intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · simpa using hz
      · have hij : i ≠ j := fun e => hjU (e ▸ hi)
        simpa [Function.update_of_ne hij] using hf i hi
    · rw [sum_insert hjU, Function.update_self, sum_update_of_notMem hjU, hsum, ht']
