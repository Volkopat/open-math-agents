import OMAStatements.S_mse_4462775
open Set Filter Topology
theorem OMA.solution : type_of% @OMA.S_mse_4462775.main := by
  intro 𝕜 X Y _ _ _ _ _ _ _ T hT ⟨D, hD, hTD⟩
  let L : X →L[𝕜] Y := ⟨T, IsCompactOperator.continuous
    ⟨D, hD, mem_of_superset (Metric.ball_mem_nhds 0 one_pos) fun x hx => hTD ⟨x, hx, rfl⟩⟩⟩
  have := hD.locallyCompactSpace_of_mem_nhds_of_addGroup <| mem_of_superset
    ((L.isOpenMap hT _ Metric.isOpen_ball).mem_nhds ⟨0, by simp, map_zero L⟩) hTD
  exact FiniteDimensional.of_locallyCompactSpace 𝕜
