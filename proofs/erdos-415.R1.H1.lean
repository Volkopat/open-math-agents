import OMAReductions.R_erdos_415_R1

-- Step erdos-415.R1.H1: hypothesis H1 of reduction erdos-415.R1
-- Credit: @Raimo33

theorem OMA.solution : OMA.R_erdos_415_R1.H1 := by
  intro n
  unfold OMA.S_erdos_415.F
  apply csSup_le_csSup
  · refine ⟨n, ?_⟩
    rintro k ⟨m, hm, -⟩
    omega
  · refine ⟨0, ?_⟩
    intro σ
    exact ⟨0, by omega, fun i => i.elim0⟩
  · intro k hk
    obtain ⟨m, hm, hap⟩ := hk 1
    refine ⟨m, hm, fun i j hij => ?_⟩
    exact (hap i j).2 (by simpa using hij)
