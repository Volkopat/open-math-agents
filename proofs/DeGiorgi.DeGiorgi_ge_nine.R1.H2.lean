import OMAReductions.R_DeGiorgi_DeGiorgi_ge_nine_R1

/-!
# Proof of `DeGiorgi.DeGiorgi_ge_nine.R1.H2`

Cylindrical dimension-lifting for De Giorgi's conjecture: if `DeGiorgi_conclusion (m + 1)` holds,
then `DeGiorgi_conclusion m` also holds.

Given a bounded classical solution `u : ℝ^m → ℝ` of `Δu + u - u^3 = 0` with `∂₁u > 0`, define
`v := u ∘ π : ℝ^(m + 1) → ℝ` where `π` drops the last coordinate. Then `v` is `C^2`, bounded,
satisfies `Δv(x) = Δu(π x)` (hence `Δv + v - v^3 = 0`), and `∂₁v(x) = ∂₁u(π x) > 0`.
If every level set `v⁻¹ {y}` is an affine hyperplane `S ⊆ ℝ^(m + 1)` of dimension `m`, then `S`
is translation-invariant along `e_last`, so `e_last ∈ S.direction \ range ι`. Hence
`S.direction ⊔ range ι = ⊤`, and by Grassmann's formula `S.direction ⊓ range ι` has dimension
`m - 1`. Pulling back `S` along the section `ι : ℝ^m → ℝ^(m + 1)` gives an affine subspace
`T = S.comap ι` equal to `u⁻¹ {y}` with `finrank T.direction = m - 1`.
-/

open ContDiff Set InnerProductSpace EuclideanGeometry
open scoped Laplacian

private noncomputable def projCLM (m : ℕ) : ℝ^(m + 1) →L[ℝ] ℝ^m :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i : Fin m => x i.castSucc)
      map_add' := fun x y => by ext i; rfl
      map_smul' := fun c x => by ext i; rfl }

private noncomputable def embCLM (m : ℕ) : ℝ^m →L[ℝ] ℝ^(m + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (Fin.snoc (fun i : Fin m => y i) (0 : ℝ))
      map_add' := fun x y => by
        ext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp [Fin.snoc_last]
        · simp [Fin.snoc_castSucc]
      map_smul' := fun c x => by
        ext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp [Fin.snoc_last]
        · simp [Fin.snoc_castSucc] }

private lemma proj_emb (m : ℕ) (y : ℝ^m) : projCLM m (embCLM m y) = y := by
  ext i
  simp [projCLM, embCLM, Fin.snoc_castSucc]

private lemma proj_single_castSucc (m : ℕ) (i : Fin m) :
    projCLM m (EuclideanSpace.single i.castSucc (1 : ℝ)) = EuclideanSpace.single i (1 : ℝ) := by
  ext j
  simp only [projCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.single_apply]
  by_cases h : j = i
  · subst h; simp
  · have h' : j.castSucc ≠ i.castSucc := fun hc => h (Fin.castSucc_injective m hc)
    simp [h, h']

private lemma proj_single_last (m : ℕ) :
    projCLM m (EuclideanSpace.single (Fin.last m) (1 : ℝ)) = 0 := by
  ext j
  simp only [projCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.zero_apply, PiLp.single_apply]
  have h : j.castSucc ≠ Fin.last m := Fin.castSucc_ne_last j
  simp [h]

private lemma proj_single_zero (m : ℕ) [NeZero m] :
    projCLM m (EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℝ)) =
      EuclideanSpace.single (0 : Fin m) (1 : ℝ) := by
  have h0 : (0 : Fin (m + 1)) = (0 : Fin m).castSucc := by
    ext
    simp
  rw [h0]
  exact proj_single_castSucc m 0

private lemma laplacian_comp_proj {m : ℕ} {u : ℝ^m → ℝ} (hu : ContDiff ℝ 2 u) (x : ℝ^(m + 1)) :
    (Δ (u ∘ projCLM m) x) = Δ u (projCLM m x) := by
  have hL1 := laplacian_eq_iteratedFDeriv_orthonormalBasis (u ∘ projCLM m)
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)
  have hL2 := laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin m) ℝ)
  rw [congrFun hL1 x, congrFun hL2 (projCLM m x)]
  have hcomp : ∀ w : Fin 2 → ℝ^(m + 1),
      iteratedFDeriv ℝ 2 (u ∘ projCLM m) x w =
        iteratedFDeriv ℝ 2 u (projCLM m x) (projCLM m ∘ w) := by
    intro w
    have h := (projCLM m).iteratedFDeriv_comp_right (i := 2) hu x (by norm_num)
    simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_def] using congrFun (congrArg DFunLike.coe h) w
  simp_rw [hcomp]
  rw [Fin.sum_univ_castSucc]
  have hlast : iteratedFDeriv ℝ 2 u (projCLM m x)
      (projCLM m ∘ ![EuclideanSpace.basisFun (Fin (m + 1)) ℝ (Fin.last m),
        EuclideanSpace.basisFun (Fin (m + 1)) ℝ (Fin.last m)]) = 0 := by
    refine ContinuousMultilinearMap.map_coord_zero _ (0 : Fin 2) ?_
    simp [EuclideanSpace.basisFun_apply, proj_single_last]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ext k
  fin_cases k <;> simp [EuclideanSpace.basisFun_apply, proj_single_castSucc]

theorem OMA.solution : OMA.R_DeGiorgi_DeGiorgi_ge_nine_R1.H2 := by
  intro m hm_ne _ hnot hsucc
  apply hnot
  intro u ⟨hu_sol, hu_pos⟩
  let π := projCLM m
  let ι := embCLM m
  let v : ℝ^(m + 1) → ℝ := u ∘ π
  have hv_sol : DeGiorgi.IsBoundedSolution v := by
    refine ⟨hu_sol.regular.comp π.contDiff, ?_, ?_⟩
    · obtain ⟨C, hC⟩ := hu_sol.bounded
      exact ⟨C, fun x => hC (π x)⟩
    · intro x
      dsimp only [v]
      rw [laplacian_comp_proj hu_sol.regular x]
      exact hu_sol.solution (π x)
  have hv_pos : DeGiorgi.HasPositiveDeriv v := by
    intro x
    have hud : DifferentiableAt ℝ u (π x) :=
      (hu_sol.regular.differentiable (by norm_num)) (π x)
    have hvd : DifferentiableAt ℝ v x := hud.comp x π.differentiableAt
    rw [hvd.lineDeriv_eq_fderiv]
    have hfd : fderiv ℝ v x = (fderiv ℝ u (π x)).comp π := by
      have := HasFDerivAt.comp x hud.hasFDerivAt π.hasFDerivAt
      exact this.fderiv
    rw [hfd, ContinuousLinearMap.comp_apply, proj_single_zero m,
      ← hud.lineDeriv_eq_fderiv]
    exact hu_pos (π x)
  have hv_hyp : DeGiorgi.HasHyperplaneLevelSets v := hsucc v ⟨hv_sol, hv_pos⟩
  intro y hy
  obtain ⟨x₀, rfl⟩ := Set.mem_range.mp hy
  have hy_v : u x₀ ∈ Set.range v := ⟨ι x₀, by simp [v, π, ι, proj_emb]⟩
  obtain ⟨S, hS_eq, hS_dim⟩ := hv_hyp (u x₀) hy_v
  let T : AffineSubspace ℝ (ℝ^m) := S.comap ι.toLinearMap.toAffineMap
  have hT_mem : ∀ z : ℝ^m, z ∈ T ↔ ι z ∈ S := fun z => Iff.rfl
  have hT_set : u ⁻¹' {u x₀} = (T : Set (ℝ^m)) := by
    ext z
    change u z = u x₀ ↔ z ∈ T
    rw [hT_mem]
    change u z = u x₀ ↔ ι z ∈ (S : Set (ℝ^(m + 1)))
    rw [← hS_eq]
    simp [v, π, ι, proj_emb]
  refine ⟨T, hT_set, ?_⟩
  have hx₀T : x₀ ∈ T := by
    change x₀ ∈ (T : Set (ℝ^m))
    rw [← hT_set]
    rfl
  have hx₀S : ι x₀ ∈ S := (hT_mem x₀).mp hx₀T
  have hT_dir : T.direction = S.direction.comap ι.toLinearMap := by
    ext w
    rw [Submodule.mem_comap, ← AffineSubspace.vadd_mem_iff_mem_direction w hx₀T,
      ← AffineSubspace.vadd_mem_iff_mem_direction (ι.toLinearMap w) hx₀S, hT_mem]
    simp [vadd_eq_add, map_add]
  have hι_inj : Function.Injective ι.toLinearMap := by
    intro a b h
    have := congrArg π h
    simpa [π, ι, proj_emb] using this
  let elast : ℝ^(m + 1) := EuclideanSpace.single (Fin.last m) (1 : ℝ)
  have hx₀_shift : elast +ᵥ ι x₀ ∈ S := by
    change elast +ᵥ ι x₀ ∈ (S : Set (ℝ^(m + 1)))
    rw [← hS_eq]
    simp [v, π, ι, elast, vadd_eq_add, map_add, proj_single_last, proj_emb]
  have helast_S : elast ∈ S.direction := by
    have := AffineSubspace.vsub_mem_direction hx₀_shift hx₀S
    simpa [vadd_vsub] using this
  have helast_not_range : elast ∉ LinearMap.range ι.toLinearMap := by
    rintro ⟨a, ha⟩
    have hcoord := congrArg (fun z : ℝ^(m + 1) => z (Fin.last m)) ha
    simp [ι, embCLM, elast, Fin.snoc_last] at hcoord
  have hrange_dim : Module.finrank ℝ ↥(LinearMap.range ι.toLinearMap) = m := by
    rw [LinearMap.finrank_range_of_inj hι_inj, finrank_euclideanSpace_fin]
  have hlt : LinearMap.range ι.toLinearMap < S.direction ⊔ LinearMap.range ι.toLinearMap := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro heq
    have : elast ∈ LinearMap.range ι.toLinearMap := by
      rw [heq]; exact Submodule.mem_sup_left helast_S
    exact helast_not_range this
  have hsup_gt : m < Module.finrank ℝ ↥(S.direction ⊔ LinearMap.range ι.toLinearMap) := by
    have h := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hsup_le : Module.finrank ℝ ↥(S.direction ⊔ LinearMap.range ι.toLinearMap) ≤ m + 1 := by
    have := Submodule.finrank_le (S.direction ⊔ LinearMap.range ι.toLinearMap)
    rwa [finrank_euclideanSpace_fin] at this
  have hsup_eq : Module.finrank ℝ ↥(S.direction ⊔ LinearMap.range ι.toLinearMap) = m + 1 := by omega
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq S.direction (LinearMap.range ι.toLinearMap)
  have hinf_dim : Module.finrank ℝ ↥(S.direction ⊓ LinearMap.range ι.toLinearMap) = m - 1 := by
    simp only [Nat.add_sub_cancel] at hS_dim
    omega
  have hemb_proj_of_range : ∀ z ∈ LinearMap.range ι.toLinearMap, ι (π z) = z := by
    rintro z ⟨a, rfl⟩
    change ι (π (ι a)) = ι a
    rw [proj_emb]
  let e : ↥(S.direction.comap ι.toLinearMap) ≃ₗ[ℝ]
      ↥(S.direction ⊓ LinearMap.range ι.toLinearMap) :=
    { toFun := fun w => ⟨ι w.1, w.2, w.1, rfl⟩
      invFun := fun z => ⟨π z.1, by
        show ι (π z.1) ∈ S.direction
        rw [hemb_proj_of_range z.1 z.2.2]
        exact z.2.1⟩
      map_add' := fun a b => by ext; simp [map_add]
      map_smul' := fun c a => by ext; simp [map_smul]
      left_inv := fun w => Subtype.ext (proj_emb m w.1)
      right_inv := fun z => by
        apply Subtype.ext
        exact hemb_proj_of_range z.1 z.2.2 }
  have hcomap_dim : Module.finrank ℝ ↥(S.direction.comap ι.toLinearMap) =
      Module.finrank ℝ ↥(S.direction ⊓ LinearMap.range ι.toLinearMap) :=
    e.finrank_eq
  rw [hT_dir, hcomap_dim, hinf_dim]
