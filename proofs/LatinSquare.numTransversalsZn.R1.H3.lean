import OMAReductions.R_LatinSquare_numTransversalsZn_R1

/-! The shifted sequence together with its limit is compact and stays in the open unit interval. -/
open Filter Set
open scoped Topology

theorem OMA.solution : OMA.R_LatinSquare_numTransversalsZn_R1.H3 := by
  intro u x hu hx hub
  let S := insert x (range (fun n : ℕ => u (n + 1)))
  have hc : IsCompact S := (hu.comp (tendsto_add_atTop_nat 1)).isCompact_insert_range
  have hi : ∀ y ∈ S, y ∈ Ioo (0 : ℝ) 1 := by
    rintro y (rfl | ⟨n, rfl⟩)
    · exact hx
    · exact hub _ (by omega)
  obtain ⟨a, ha, hamin⟩ := hc.exists_isLeast (insert_nonempty _ _)
  obtain ⟨b, hb, hbmax⟩ := hc.exists_isGreatest (insert_nonempty _ _)
  obtain ⟨hap, ha1⟩ := hi a ha
  obtain ⟨hbp, hb1⟩ := hi b hb
  have hab := hamin hb
  refine ⟨a / 2, (b + 1) / 2, by linarith, by linarith, by linarith, ?_⟩
  intro n hn
  have hm : u n ∈ S := Or.inr ⟨n - 1, by simp [Nat.sub_add_cancel hn]⟩
  exact ⟨by linarith [hamin hm], by linarith [hbmax hm]⟩
