import OMAStatements.S_mo_309993

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_309993.main) := by
  classical
  intro h
  let F := RatFunc ℂ
  let G := ULift.{_} Fˣ
  let V := ULift.{_} F
  let A := MonoidAlgebra ℂ G
  have hall := (h G).mp ⟨⊤, inferInstance, fun x y => mul_comm x y⟩
  let f : G →* V :=
    { toFun := fun g => ULift.up (g.down : F)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let φ : A →ₐ[ℂ] V := MonoidAlgebra.lift ℂ V G f
  have onto : Function.Surjective φ := by
    intro v
    by_cases hv : v.down = 0
    · exact ⟨0, (map_zero φ).trans (ULift.ext _ _ hv.symm)⟩
    · let g : G := ULift.up (Units.mk0 v.down hv)
      refine ⟨MonoidAlgebra.single g 1, ?_⟩
      change MonoidAlgebra.lift ℂ V G f _ = v
      rw [MonoidAlgebra.lift_single, one_smul]
      rfl
  let : Module A V := Module.compHom V φ.toRingHom
  have hs : IsSimpleModule A V := by
    refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstance, ?_⟩
    intro v hv w
    obtain ⟨a, ha⟩ := onto (w / v)
    exact ⟨a, show φ a * v = w by rw [ha, div_mul_cancel₀ _ hv]⟩
  have hfin := hall V hs
  let : Module ℂ V := Module.compHom V (algebraMap ℂ A)
  let down : V →ₗ[ℂ] F :=
    { toFun := ULift.down
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro c v
        change (φ (algebraMap ℂ A c) * v).down = c • v.down
        rw [φ.commutes]
        exact (Algebra.smul_def c v.down).symm }
  let : FiniteDimensional ℂ V := hfin
  let : FiniteDimensional ℂ F :=
    Module.Finite.of_surjective down (fun x => ⟨ULift.up x, rfl⟩)
  exact RatFunc.transcendental_X (Algebra.IsAlgebraic.isAlgebraic (R := ℂ) (RatFunc.X : F))
