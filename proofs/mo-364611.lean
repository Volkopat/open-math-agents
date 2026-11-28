import OMAStatements.S_mo_364611

theorem OMA.solution : type_of% @OMA.S_mo_364611.main := by
  refine ⟨Empty, Empty, inferInstance, inferInstance, id,
    inferInstance, inferInstance, inferInstance,
    Topology.IsQuotientMap.id, inferInstance, inferInstance, ?_⟩
  intro y
  exact Empty.elim y
