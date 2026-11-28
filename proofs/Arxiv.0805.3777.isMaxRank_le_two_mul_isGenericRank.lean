import FormalConjectures.Arxiv.«0805.3777».TensorRank

/-! Write a tensor as the sum of two tensors from the dense open rank stratum. -/

open scoped Arxiv.«0805.3777»

theorem OMA.solution : type_of% @Arxiv.«0805.3777».isMaxRank_le_two_mul_isGenericRank := by
  classical
  rintro ds r R ⟨U, ho, hd, hr⟩ ⟨⟨T, rfl⟩, _⟩
  have hcont : Continuous (fun X : Holor ℂ ds => T - X) :=
    show Continuous (fun X : HolorIndex ds → ℂ => (fun i => T i) - X) from
      continuous_const.sub continuous_id
  obtain ⟨Y, hY⟩ := hd.nonempty
  obtain ⟨X, hX, hTX⟩ := hd.exists_mem_open (ho.preimage hcont)
    ⟨T - Y, by simpa only [Set.mem_preimage, sub_sub_cancel] using hY⟩
  have bound (Y : Holor ℂ ds) (hY : Y ∈ U) : Holor.CPRankMax r Y := by
    rw [← hr Y hY]
    exact Nat.find_spec (p := (Holor.CPRankMax · Y)) ⟨_, Holor.cprankMax_upper_bound Y⟩
  rw [two_mul]
  apply Nat.find_min'
  simpa only [sub_add_cancel] using Holor.cprankMax_add (bound (T - X) hTX) (bound X hX)
