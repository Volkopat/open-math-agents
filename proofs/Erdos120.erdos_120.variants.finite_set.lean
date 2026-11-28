import FormalConjectures.ErdosProblems.«120»

open Set MeasureTheory Filter
open scoped Topology Pointwise

theorem OMA.solution : type_of% @Erdos120.erdos_120.variants.finite_set := by
  rintro A h ⟨E, hE, hpos, havoid⟩
  obtain ⟨K, hKE, hK, hKpos⟩ := hE.exists_lt_isCompact hpos
  have h0 : Tendsto (fun a : ℝ => ∑ x ∈ h.toFinset, volume (((a * x) +ᵥ K) \ K)) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_finsetSum h.toFinset fun x _ =>
      (tendsto_measure_vadd_sdiff_isCompact_isClosed hK hK.isClosed).comp
        (by simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const x)
  obtain ⟨a, ha, hsum⟩ := (Filter.Eventually.and (self_mem_nhdsWithin : ∀ᶠ a : ℝ in 𝓝[≠] 0, a ≠ 0)
    ((h0.eventually_lt_const hKpos).filter_mono nhdsWithin_le_nhds)).exists
  refine hsum.not_ge ((le_trans (measure_mono fun b hb => ?_)
    (measure_biUnion_finset_le h.toFinset fun x => -(a * x) +ᵥ (((a * x) +ᵥ K) \ K))).trans_eq ?_)
  · obtain ⟨_, ⟨x, hx, rfl⟩, hxE⟩ := not_subset.mp (havoid a b ha)
    exact mem_iUnion₂.mpr ⟨x, h.mem_toFinset.mpr hx, a * x + b,
      ⟨⟨b, hb, rfl⟩, fun hK' => hxE (hKE hK')⟩, neg_add_cancel_left _ _⟩
  · simp [measure_vadd]
