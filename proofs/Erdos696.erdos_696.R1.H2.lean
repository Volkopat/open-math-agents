import OMAReductions.R_Erdos696_erdos_696_R1

/-! For disjoint S and T the partial densities add up to the partial density of S ∪ T, which is
at most 1. Densities 1 and δ would make this sum tend to 1 + δ > 1. -/

open Filter Topology in
theorem OMA.solution : OMA.R_Erdos696_erdos_696_R1.H2 := by
  intro S T δ hδ hT hST hS
  have key : ∀ b : ℕ, S.partialDensity Set.univ b + T.partialDensity Set.univ b ≤ 1 := by
    intro b
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
    rw [← add_div]
    apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
    have hfin : (Set.Iio b).Finite := Set.finite_Iio b
    have hd : Disjoint (S ∩ Set.Iio b) (T ∩ Set.Iio b) :=
      Disjoint.mono Set.inter_subset_left Set.inter_subset_left hST
    rw [← Nat.cast_add, ← Set.ncard_union_eq hd (hfin.subset Set.inter_subset_right)
      (hfin.subset Set.inter_subset_right)]
    exact_mod_cast Set.ncard_le_ncard
      (Set.union_subset Set.inter_subset_right Set.inter_subset_right) hfin
  have hS' : Tendsto (fun b : ℕ => S.partialDensity Set.univ b) atTop (𝓝 1) := hS
  have hT' : Tendsto (fun b : ℕ => T.partialDensity Set.univ b) atTop (𝓝 δ) := hT
  have hle := le_of_tendsto' (hS'.add hT') key
  linarith
