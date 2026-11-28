import OMAReductions.R_Erdos186_erdos_186_variants_pham_zakharov_R1

-- Step Erdos186.erdos_186.variants.pham_zakharov.R1.H2: hypothesis H2 of reduction Erdos186.erdos_186.variants.pham_zakharov.R1
-- Credit: @Albin0903
-- H2 := ∀ N : ℕ, ∃ A : Finset ℕ,     A ⊆ Finset.Icc 1 N ∧ Erdos186.NonAveraging A ∧ A.card = Erdos186.F N

theorem OMA.solution : OMA.R_Erdos186_erdos_186_variants_pham_zakharov_R1.H2 := by
  intro N
  let family := (Finset.Icc 1 N).powerset.filter Erdos186.NonAveraging
  have hfamily : family.Nonempty := by
    exact ⟨∅, by simp [family, Erdos186.NonAveraging]⟩
  obtain ⟨A, hA, hcard⟩ := Finset.exists_mem_eq_sup family hfamily Finset.card
  obtain ⟨hsub, hna⟩ := Finset.mem_filter.mp hA
  exact ⟨A, Finset.mem_powerset.mp hsub, hna, hcard.symm⟩
