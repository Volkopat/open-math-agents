import OMAStatements.S_mse_1197076

open Set OMA.S_mse_1197076

theorem OMA.solution : type_of% @OMA.S_mse_1197076.main := by
  intro claim
  let G := Multiplicative (ZMod 2)
  let E := ULift.{0} G
  let _ : TopologicalSpace G := ⊥
  let _ : DiscreteTopology G := ⟨rfl⟩
  let _ : TopologicalSpace E := ⊤
  let _ : IndiscreteTopology E := ⟨rfl⟩
  let _ : MulAction G E :=
    { smul := fun g x => ⟨g * x.down⟩
      one_smul := fun x => by cases x; simp
      mul_smul := fun g h x => congrArg (fun y : G => (⟨y⟩ : E)) (mul_assoc g h x.down) }
  let _ : ContinuousSMul G E := ⟨continuous_of_indiscreteTopology⟩
  let e : E := ⟨1⟩
  have contractible : IsWeaklyContractible E := by
    refine ⟨⟨e⟩, fun n f => ⟨e, ?_⟩⟩
    refine ⟨{
      toFun := fun x => if x.1 = 0 then f x.2 else e
      continuous_toFun := continuous_of_indiscreteTopology
      map_zero_left := fun x => by simp
      map_one_left := fun x => by simp }⟩
  have hfree : ∀ (g : G) (x : E), g • x = x → g = 1 := by
    intro g x hx
    have heq : g * x.down = x.down := congrArg ULift.down hx
    exact mul_right_cancel (show g * x.down = 1 * x.down by simpa using heq)
  let q := Quotient.mk (MulAction.orbitRel G E)
  have hq (x : E) : q x = q e := by
    apply Quotient.sound
    refine ⟨x.down, ?_⟩
    change (⟨x.down * 1⟩ : E) = x
    cases x
    simp
  obtain ⟨U, _, he, φ, _, hequiv⟩ := claim G E contractible hfree (q e)
  have hu (x : E) : q x ∈ U := (hq x).symm ▸ he
  let T : E → G := fun x => (φ ⟨x, hu x⟩).2
  have hT : Continuous T :=
    continuous_snd.comp (φ.continuous.comp (continuous_id.subtype_mk hu))
  have same (x : E) : T x = T e := by
    let W := T ⁻¹' ({T e} : Set G)
    have hopen : IsOpen W := (isOpen_discrete _).preimage hT
    have he' : e ∈ W := by simp [W]
    rcases (IndiscreteTopology.isOpen_iff W).mp hopen with hEmpty | hAll
    · rw [hEmpty] at he'
      exact (Set.notMem_empty e he').elim
    · have hx : x ∈ W := hAll.symm ▸ Set.mem_univ x
      exact hx
  let g : G := Multiplicative.ofAdd (1 : ZMod 2)
  have hg : g ≠ 1 := by decide
  have hmul : T (g • e) = g * T e :=
    congrArg Prod.snd (hequiv g ⟨e, hu e⟩ (hu (g • e)))
  rw [same] at hmul
  exact hg (mul_right_cancel (show g * T e = 1 * T e by simpa using hmul.symm))