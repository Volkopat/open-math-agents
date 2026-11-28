import OMAReductions.R_Erdos997_erdos_997_variants_irrational_R1_H1_R1

-- Step Erdos997.erdos_997.variants.irrational.R1.H1.R1.H2
-- Credit: @caa1982

theorem OMA.solution : OMA.R_Erdos997_erdos_997_variants_irrational_R1_H1_R1.H2 := by
  rintro good k hk ⟨m, hm⟩
  refine ⟨m, m + k, ?_⟩
  have noBad : (Finset.Ico m (m + k)).filter (fun i => good i = false) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun i hi => by simp [hm i hi]
  simpa [noBad, Finset.filter_true_of_mem hm, Nat.card_Ico] using Nat.sub_lt hk Nat.zero_lt_one
