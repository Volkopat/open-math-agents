import OMAStatements.S_mo_412446

-- Retains @ivillar's Boltzmann product proof from PR #10423.
-- The strict subset-sum API also appears in @justusklocke-cloud's pending #22321.
-- The subset-product inequality directly removes factors bounded by one.

theorem OMA.solution : type_of% @OMA.S_mo_412446.main := by
  intro n E β S hS hne
  have hpos : ∀ i, 0 < Real.exp (-β * E i) := fun i => Real.exp_pos _
  unfold OMA.S_mo_412446.boltzmann
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∑ j ∈ Finset.univ, Real.exp (-β * E j) := ⟨_, rfl⟩
  obtain ⟨ZS, hZS⟩ : ∃ ZS, ZS = ∑ j ∈ S, Real.exp (-β * E j) := ⟨_, rfl⟩
  rw [← hZ, ← hZS]
  have hZS_pos : 0 < ZS := by
    rw [hZS]
    exact Finset.sum_pos (fun i _ => hpos i) hS
  have hlt : ZS < Z := by
    obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by simpa [Finset.eq_univ_iff_forall] using hne
    rw [hZS, hZ]
    exact Finset.sum_lt_sum_of_subset (Finset.subset_univ S) (Finset.mem_univ i)
      hi (hpos i) (fun j _ _ => (hpos j).le)
  have hZpos : 0 < Z := hZS_pos.trans hlt
  have h1 : ∏ i ∈ S, Real.exp (-β * E i) / Z < ∏ i ∈ S, Real.exp (-β * E i) / ZS := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro i _
      exact div_pos (hpos i) hZpos
    · intro i _
      exact div_lt_div_of_pos_left (hpos i) hZS_pos hlt
    · exact hS
  apply lt_of_le_of_lt _ h1
  apply Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ S)
  · exact fun i _ => (div_pos (hpos i) hZpos).le
  · intro i _ _
    rw [div_le_one hZpos, hZ]
    exact Finset.single_le_sum (fun j _ => (hpos j).le) (Finset.mem_univ i)
