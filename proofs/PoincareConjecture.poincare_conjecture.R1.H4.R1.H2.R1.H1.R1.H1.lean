import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R1

section PoincareOrientableH1

open Bundle Manifold Set Topology
open scoped Manifold ContDiff EuclideanGeometry Topology unitInterval

private lemma orientation_map_trans {E₁ E₂ E₃ : Type*}
    [AddCommGroup E₁] [Module ℝ E₁] [AddCommGroup E₂] [Module ℝ E₂] [AddCommGroup E₃] [Module ℝ E₃]
    (e₁ : E₁ ≃ₗ[ℝ] E₂) (e₂ : E₂ ≃ₗ[ℝ] E₃) (o : Orientation ℝ E₁ (Fin 3)) :
    Orientation.map (Fin 3) (e₁.trans e₂) o = Orientation.map (Fin 3) e₂ (Orientation.map (Fin 3) e₁ o) := by
  induction o using Module.Ray.ind with
  | h v hv =>
    simp only [Orientation.map_apply]
    congr 1

private lemma orient_map_eqRec
    {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M]
    (t : Trivialization (ℝ^3) (π (ℝ^3) (TangentSpace (𝓡 3) (M := M))))
    [t.IsLinear ℝ] {x y : M} (h : x = y) (hx : x ∈ t.baseSet) (hy : y ∈ t.baseSet)
    (o : Orientation ℝ (TangentSpace (𝓡 3) (M := M) x) (Fin 3)) :
    Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ y hy).toLinearEquiv (h ▸ o) =
      Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ x hx).toLinearEquiv o := by
  subst h; rfl

private lemma continuousOn_det_coordChangeL
    {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M]
    (t₁ t₂ : Trivialization (ℝ^3) (π (ℝ^3) (TangentSpace (𝓡 3) (M := M))))
    [MemTrivializationAtlas t₁] [MemTrivializationAtlas t₂] :
    ContinuousOn
      (fun b => LinearMap.det (t₁.coordChangeL ℝ t₂ b).toLinearMap)
      (t₁.baseSet ∩ t₂.baseSet) := by
  let B : Module.Basis (Fin 3) ℝ (ℝ^3) := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hmat : ∀ b, LinearMap.det (t₁.coordChangeL ℝ t₂ b).toLinearMap =
      Matrix.det (LinearMap.toMatrix B B (t₁.coordChangeL ℝ t₂ b).toLinearMap) :=
    fun b => (LinearMap.det_toMatrix B _).symm
  simp_rw [hmat, Matrix.det_apply]
  refine continuousOn_finset_sum _ fun perm _ => ?_
  refine ContinuousOn.const_smul ?_ _
  refine continuousOn_finset_prod _ fun i _ => ?_
  have hcc : ContinuousOn (fun b => t₁.coordChangeL ℝ t₂ b (B i)) (t₁.baseSet ∩ t₂.baseSet) :=
    (continuousOn_coordChange (R := ℝ) (F := ℝ^3) (E := TangentSpace (𝓡 3) (M := M)) t₁ t₂).clm_apply
      continuousOn_const
  have hproj : Continuous (fun v : ℝ^3 => B.repr v (perm i)) :=
    (B.coord (perm i)).continuous_of_finiteDimensional
  simpa [LinearMap.toMatrix_apply, Function.comp_def] using hproj.comp_continuousOn hcc

private lemma coordChange_orient_eventuallyEq
    {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M]
    (t₁ t₂ : Trivialization (ℝ^3) (π (ℝ^3) (TangentSpace (𝓡 3) (M := M))))
    [MemTrivializationAtlas t₁] [MemTrivializationAtlas t₂]
    {b₀ : M} (hb₀ : b₀ ∈ t₁.baseSet ∩ t₂.baseSet) (q : Orientation ℝ (ℝ^3) (Fin 3)) :
    ∃ W ∈ 𝓝 b₀, W ⊆ t₁.baseSet ∩ t₂.baseSet ∧
      ∀ b (hb : b ∈ W),
        Orientation.map (Fin 3) (t₁.coordChangeL ℝ t₂ b).toLinearEquiv q =
          Orientation.map (Fin 3) (t₁.coordChangeL ℝ t₂ b₀).toLinearEquiv q := by
  let f : M → ℝ := fun b =>
    LinearMap.det (t₁.coordChangeL ℝ t₂ b).toLinearMap
  have hopen : IsOpen (t₁.baseSet ∩ t₂.baseSet) := t₁.open_baseSet.inter t₂.open_baseSet
  have hcont : ContinuousAt f b₀ :=
    (continuousOn_det_coordChangeL t₁ t₂).continuousAt (hopen.mem_nhds hb₀)
  have hdim : Fintype.card (Fin 3) = Module.finrank ℝ (ℝ^3) := by
    simp [finrank_euclideanSpace]
  have hmap : ∀ b, Orientation.map (Fin 3) (t₁.coordChangeL ℝ t₂ b).toLinearEquiv q =
      (LinearEquiv.det (t₁.coordChangeL ℝ t₂ b).toLinearEquiv)⁻¹ • q :=
    fun b => Orientation.map_eq_det_inv_smul q _ hdim
  have hval : ∀ b, ((LinearEquiv.det (t₁.coordChangeL ℝ t₂ b).toLinearEquiv : ℝˣ) : ℝ) = f b :=
    fun b => LinearEquiv.coe_det _
  have hne : f b₀ ≠ 0 := by
    rw [← hval b₀]
    exact Units.ne_zero _
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hW : {b | f b < 0} ∈ 𝓝 b₀ := hcont.eventually (Iio_mem_nhds hneg)
    refine ⟨(t₁.baseSet ∩ t₂.baseSet) ∩ {b | f b < 0},
      Filter.inter_mem (hopen.mem_nhds hb₀) hW, inter_subset_left, ?_⟩
    intro b hb
    rw [hmap b, hmap b₀]
    have h1 : ((LinearEquiv.det (t₁.coordChangeL ℝ t₂ b).toLinearEquiv)⁻¹ : ℝˣ).1 < 0 := by
      simp only [Units.val_inv_eq_inv_val, inv_lt_zero, hval b]
      exact hb.2
    have h2 : ((LinearEquiv.det (t₁.coordChangeL ℝ t₂ b₀).toLinearEquiv)⁻¹ : ℝˣ).1 < 0 := by
      simp only [Units.val_inv_eq_inv_val, inv_lt_zero, hval b₀]
      exact hneg
    rw [units_smul_eq_neg_iff.mpr h1, units_smul_eq_neg_iff.mpr h2]
  · have hW : {b | 0 < f b} ∈ 𝓝 b₀ := hcont.eventually (Ioi_mem_nhds hpos)
    refine ⟨(t₁.baseSet ∩ t₂.baseSet) ∩ {b | 0 < f b},
      Filter.inter_mem (hopen.mem_nhds hb₀) hW, inter_subset_left, ?_⟩
    intro b hb
    rw [hmap b, hmap b₀]
    have h1 : 0 < ((LinearEquiv.det (t₁.coordChangeL ℝ t₂ b).toLinearEquiv)⁻¹ : ℝˣ).1 := by
      simp only [Units.val_inv_eq_inv_val, inv_pos, hval b]
      exact hb.2
    have h2 : 0 < ((LinearEquiv.det (t₁.coordChangeL ℝ t₂ b₀).toLinearEquiv)⁻¹ : ℝˣ).1 := by
      simp only [Units.val_inv_eq_inv_val, inv_pos, hval b₀]
      exact hpos
    rw [units_smul_eq_self_iff.mpr h1, units_smul_eq_self_iff.mpr h2]

private lemma map_triv_eq_coordChange_map
    {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M]
    (t₁ t₂ : Trivialization (ℝ^3) (π (ℝ^3) (TangentSpace (𝓡 3) (M := M))))
    [t₁.IsLinear ℝ] [t₂.IsLinear ℝ]
    {b : M} (hb₁ : b ∈ t₁.baseSet) (hb₂ : b ∈ t₂.baseSet)
    (o : Orientation ℝ (TangentSpace (𝓡 3) (M := M) b) (Fin 3)) :
    Orientation.map (Fin 3) (t₂.continuousLinearEquivAt ℝ b hb₂).toLinearEquiv o =
      Orientation.map (Fin 3) (t₁.coordChangeL ℝ t₂ b).toLinearEquiv
        (Orientation.map (Fin 3) (t₁.continuousLinearEquivAt ℝ b hb₁).toLinearEquiv o) := by
  have heq : (t₂.continuousLinearEquivAt ℝ b hb₂).toLinearEquiv =
      (t₁.continuousLinearEquivAt ℝ b hb₁).toLinearEquiv.trans
        (t₁.coordChangeL ℝ t₂ b).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change (t₂ ⟨b, v⟩).2 = t₁.coordChangeL ℝ t₂ b (t₁ ⟨b, v⟩).2
    rw [t₁.coordChangeL_apply t₂ ⟨hb₁, hb₂⟩, t₁.symm_apply_apply_mk hb₁]
  rw [heq]
  exact orientation_map_trans _ _ o

private def IsLocConstOrient
    {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M]
    {X : Type*} [TopologicalSpace X]
    (f : X → M) (s : ∀ x : X, Orientation ℝ (TangentSpace (𝓡 3) (M := M) (f x)) (Fin 3)) : Prop :=
  ∀ x : X, ∃ t : Trivialization (ℝ^3) (π (ℝ^3) (TangentSpace (𝓡 3) (M := M))),
    ∃ _ : MemTrivializationAtlas t,
    ∃ U ∈ 𝓝 x, ∃ hU : ∀ y ∈ U, f y ∈ t.baseSet, ∃ q : Orientation ℝ (ℝ^3) (Fin 3),
      ∀ y (hy : y ∈ U),
        Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (f y) (hU y hy)).toLinearEquiv (s y) = q

private lemma isLocConstOrient_in_chart
    {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M]
    {X : Type*} [TopologicalSpace X] {f : X → M} (hf : Continuous f)
    {s : ∀ x : X, Orientation ℝ (TangentSpace (𝓡 3) (M := M) (f x)) (Fin 3)}
    (hs : IsLocConstOrient f s) {x : X}
    (t : Trivialization (ℝ^3) (π (ℝ^3) (TangentSpace (𝓡 3) (M := M))))
    [MemTrivializationAtlas t] (hfx : f x ∈ t.baseSet) :
    ∃ U ∈ 𝓝 x, ∃ hU : ∀ y ∈ U, f y ∈ t.baseSet,
      ∀ y (hy : y ∈ U),
        Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (f y) (hU y hy)).toLinearEquiv (s y) =
          Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (f x) hfx).toLinearEquiv (s x) := by
  obtain ⟨t₁, ht₁, U₁, hU₁_nhds, hU₁_sub, q₁, hq₁⟩ := hs x
  have hfx₁ : f x ∈ t₁.baseSet := hU₁_sub x (mem_of_mem_nhds hU₁_nhds)
  obtain ⟨W, hW_nhds, hW_sub, hW_eq⟩ := coordChange_orient_eventuallyEq t₁ t ⟨hfx₁, hfx⟩ q₁
  have hfW : f ⁻¹' W ∈ 𝓝 x := hf.continuousAt.preimage_mem_nhds hW_nhds
  refine ⟨U₁ ∩ f ⁻¹' W, Filter.inter_mem hU₁_nhds hfW, fun y hy => (hW_sub hy.2).2, ?_⟩
  intro y hy
  have hy₁ : f y ∈ t₁.baseSet := hU₁_sub y hy.1
  have hy₂ : f y ∈ t.baseSet := (hW_sub hy.2).2
  rw [map_triv_eq_coordChange_map t₁ t hy₁ hy₂ (s y),
      map_triv_eq_coordChange_map t₁ t hfx₁ hfx (s x),
      hq₁ y hy.1, hq₁ x (mem_of_mem_nhds hU₁_nhds)]
  exact hW_eq (f y) hy.2

private lemma isLocConstOrient_unique
    {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M]
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X] {f : X → M} (hf : Continuous f)
    {s₁ s₂ : ∀ x : X, Orientation ℝ (TangentSpace (𝓡 3) (M := M) (f x)) (Fin 3)}
    (hs₁ : IsLocConstOrient f s₁) (hs₂ : IsLocConstOrient f s₂)
    {x₀ : X} (heq : s₁ x₀ = s₂ x₀) :
    ∀ x : X, s₁ x = s₂ x := by
  let S : Set X := {x | s₁ x = s₂ x}
  have hclopen : IsClopen S := by
    refine ⟨?_, ?_⟩
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro x hx
      let t := trivializationAt (ℝ^3) (TangentSpace (𝓡 3) (M := M)) (f x)
      have hfx : f x ∈ t.baseSet := mem_baseSet_trivializationAt (ℝ^3) _ (f x)
      obtain ⟨U₁, hU₁, hU₁_sub, h1⟩ := isLocConstOrient_in_chart hf hs₁ t hfx
      obtain ⟨U₂, hU₂, hU₂_sub, h2⟩ := isLocConstOrient_in_chart hf hs₂ t hfx
      filter_upwards [Filter.inter_mem hU₁ hU₂] with y hy heqy
      apply hx
      have hmap_eq : Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (f x) hfx).toLinearEquiv (s₁ x) =
          Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (f x) hfx).toLinearEquiv (s₂ x) := by
        rw [← h1 y hy.1, ← h2 y hy.2, heqy]
      exact (Orientation.map (Fin 3) _).injective hmap_eq
    · rw [isOpen_iff_mem_nhds]
      intro x hx
      let t := trivializationAt (ℝ^3) (TangentSpace (𝓡 3) (M := M)) (f x)
      have hfx : f x ∈ t.baseSet := mem_baseSet_trivializationAt (ℝ^3) _ (f x)
      obtain ⟨U₁, hU₁, hU₁_sub, h1⟩ := isLocConstOrient_in_chart hf hs₁ t hfx
      obtain ⟨U₂, hU₂, hU₂_sub, h2⟩ := isLocConstOrient_in_chart hf hs₂ t hfx
      filter_upwards [Filter.inter_mem hU₁ hU₂] with y hy
      have hmap_eq : Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (f y) (hU₁_sub y hy.1)).toLinearEquiv (s₁ y) =
          Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (f y) (hU₁_sub y hy.1)).toLinearEquiv (s₂ y) := by
        rw [h1 y hy.1, h2 y hy.2, hx]
      exact (Orientation.map (Fin 3) _).injective hmap_eq
  have huniv : S = Set.univ := hclopen.eq_univ ⟨x₀, heq⟩
  intro x
  have : x ∈ S := by rw [huniv]; trivial
  exact this

private lemma isLocConstOrient_const_in_chart
    {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M]
    {X : Type*} [TopologicalSpace X] {f : X → M}
    (t : Trivialization (ℝ^3) (π (ℝ^3) (TangentSpace (𝓡 3) (M := M))))
    [ht : MemTrivializationAtlas t] (hf : ∀ x : X, f x ∈ t.baseSet)
    (q : Orientation ℝ (ℝ^3) (Fin 3)) :
    IsLocConstOrient f (fun x =>
      (Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (f x) (hf x)).toLinearEquiv).symm q) := by
  intro x
  refine ⟨t, ht, Set.univ, Filter.univ_mem, fun y _ => hf y, q, fun y _ => ?_⟩
  exact Equiv.apply_symm_apply _ q

private lemma isLocConstOrient_comp
    {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M]
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → M} {g : X → Y} (hg : Continuous g)
    {s : ∀ y : Y, Orientation ℝ (TangentSpace (𝓡 3) (M := M) (f y)) (Fin 3)}
    (hs : IsLocConstOrient f s) :
    IsLocConstOrient (f ∘ g) (fun x => s (g x)) := by
  intro x
  obtain ⟨t, ht, U, hU_nhds, hU_sub, q, hq⟩ := hs (g x)
  exact ⟨t, ht, g ⁻¹' U, hg.continuousAt.preimage_mem_nhds hU_nhds,
    fun y hy => hU_sub (g y) hy, q, fun y hy => hq (g y) hy⟩

private lemma isLocConstOrient_const_inside_chart
    {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M]
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X] {f : X → M} (hf : Continuous f)
    {s : ∀ x : X, Orientation ℝ (TangentSpace (𝓡 3) (M := M) (f x)) (Fin 3)}
    (hs : IsLocConstOrient f s)
    (t : Trivialization (ℝ^3) (π (ℝ^3) (TangentSpace (𝓡 3) (M := M))))
    [MemTrivializationAtlas t] (hsub : ∀ x : X, f x ∈ t.baseSet)
    (x₁ x₂ : X) :
    Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (f x₁) (hsub x₁)).toLinearEquiv (s x₁) =
      Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (f x₂) (hsub x₂)).toLinearEquiv (s x₂) := by
  let q := Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (f x₁) (hsub x₁)).toLinearEquiv (s x₁)
  let s' : ∀ x : X, Orientation ℝ (TangentSpace (𝓡 3) (M := M) (f x)) (Fin 3) :=
    fun x => (Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (f x) (hsub x)).toLinearEquiv).symm q
  have hs' := isLocConstOrient_const_in_chart t hsub q
  have heq : s x₁ = s' x₁ := (Equiv.symm_apply_apply _ (s x₁)).symm
  have hall := isLocConstOrient_unique hf hs hs' heq x₂
  rw [hall]
  exact (Equiv.apply_symm_apply _ q).symm

private lemma exists_grid_triv_unitInterval
    {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M]
    {γ : I → M} (hγ : Continuous γ) :
    ∃ N : ℕ, 0 < N ∧ ∀ k : Fin N,
      ∃ t : Trivialization (ℝ^3) (π (ℝ^3) (TangentSpace (𝓡 3) (M := M))),
        ∃ _ : MemTrivializationAtlas t,
        ∀ u : I, (k.val : ℝ) / (N : ℝ) ≤ (u : ℝ) → (u : ℝ) ≤ ((k.val + 1 : ℕ) : ℝ) / (N : ℝ) →
          γ u ∈ t.baseSet := by
  let T := {t : Trivialization (ℝ^3) (π (ℝ^3) (TangentSpace (𝓡 3) (M := M))) // MemTrivializationAtlas t}
  let c : T → Set I := fun t => γ ⁻¹' t.1.baseSet
  have hc_open : ∀ t : T, IsOpen (c t) := fun t => t.1.open_baseSet.preimage hγ
  have hc_cov : (Set.univ : Set I) ⊆ ⋃ t : T, c t := by
    intro u _
    let t := trivializationAt (ℝ^3) (TangentSpace (𝓡 3) (M := M)) (γ u)
    have hmem : u ∈ c ⟨t, inferInstance⟩ :=
      mem_baseSet_trivializationAt (ℝ^3) (TangentSpace (𝓡 3) (M := M)) (γ u)
    exact mem_iUnion.mpr ⟨⟨t, inferInstance⟩, hmem⟩
  obtain ⟨δ, hδ_pos, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc_open hc_cov
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  have hN_pos : 0 < N := by
    by_contra h0
    have hN0 : N = 0 := by omega
    subst hN0
    have : (0 : ℝ) < 2 / δ := by positivity
    linarith
  have hstep : (1 : ℝ) / (N : ℝ) < δ / 2 := by
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
    rw [div_lt_div_iff₀ hNR (by norm_num)]
    have h2 : 2 < δ * (N : ℝ) := by
      have := mul_lt_mul_of_pos_left hN hδ_pos
      rwa [mul_div_cancel₀ _ hδ_pos.ne'] at this
    linarith
  refine ⟨N, hN_pos, fun k => ?_⟩
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hk_lt : (k.val : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNR]
    exact_mod_cast k.isLt.le
  let u₀ : I := ⟨(k.val : ℝ) / (N : ℝ), div_nonneg (Nat.cast_nonneg _) hNR.le, hk_lt⟩
  obtain ⟨t, ht_ball⟩ := hleb u₀ (mem_univ _)
  refine ⟨t.1, t.2, fun u hu1 hu2 => ?_⟩
  apply ht_ball
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
  have hsub : (u : ℝ) - (u₀ : ℝ) ≤ 1 / (N : ℝ) := by
    dsimp only [u₀]
    have : ((k.val + 1 : ℕ) : ℝ) / (N : ℝ) - (k.val : ℝ) / (N : ℝ) = 1 / (N : ℝ) := by
      push_cast; ring
    linarith
  have hnonneg : 0 ≤ (u : ℝ) - (u₀ : ℝ) := by dsimp only [u₀]; linarith
  rw [abs_of_nonneg hnonneg]
  linarith

private lemma exists_path_section
    {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M]
    {γ : I → M} (hγ : Continuous γ)
    (o₀ : Orientation ℝ (TangentSpace (𝓡 3) (M := M) (γ 0)) (Fin 3)) :
    ∃ s : ∀ u : I, Orientation ℝ (TangentSpace (𝓡 3) (M := M) (γ u)) (Fin 3),
      IsLocConstOrient γ s ∧ s 0 = o₀ := by
  obtain ⟨N, hN_pos, hgrid⟩ := exists_grid_triv_unitInterval hγ
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  suffices hstep : ∀ k : ℕ, (hk : k ≤ N) →
      ∃ s : ∀ u : {u : I // (u : ℝ) ≤ (k : ℝ) / (N : ℝ)},
        Orientation ℝ (TangentSpace (𝓡 3) (M := M) (γ u.1)) (Fin 3),
        IsLocConstOrient (fun u : {u : I // (u : ℝ) ≤ (k : ℝ) / (N : ℝ)} => γ u.1) s ∧
        s ⟨0, by positivity⟩ = o₀ by
    obtain ⟨s, hs, hs0⟩ := hstep N le_rfl
    have hall : ∀ u : I, (u : ℝ) ≤ (N : ℝ) / (N : ℝ) := fun u => by
      rw [div_self hNR.ne']; exact u.2.2
    let e : I → {u : I // (u : ℝ) ≤ (N : ℝ) / (N : ℝ)} := fun u => ⟨u, hall u⟩
    have he_cont : Continuous e := continuous_id.subtype_mk hall
    refine ⟨fun u => s (e u), isLocConstOrient_comp he_cont hs, ?_⟩
    exact hs0
  intro k
  induction k with
  | zero =>
    intro _
    let t := trivializationAt (ℝ^3) (TangentSpace (𝓡 3) (M := M)) (γ 0)
    have h0 : γ 0 ∈ t.baseSet := mem_baseSet_trivializationAt (ℝ^3) _ (γ 0)
    have hsub : ∀ u : {u : I // (u : ℝ) ≤ (0 : ℕ) / (N : ℝ)}, u.1 = 0 := fun u => by
      ext
      have h1 : (u.1 : ℝ) ≤ 0 := by simpa using u.2
      exact le_antisymm h1 u.1.2.1
    refine ⟨fun u => (congrArg γ (hsub u).symm) ▸ o₀, ?_, rfl⟩
    intro u
    refine ⟨t, inferInstance, Set.univ, Filter.univ_mem,
      fun y _ => by dsimp only; rw [hsub y]; exact h0,
      Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (γ 0) h0).toLinearEquiv o₀,
      fun y _ => orient_map_eqRec t (congrArg γ (hsub y).symm) h0 _ o₀⟩
  | succ k ih =>
    intro hk_le
    obtain ⟨s_prev, hs_prev, hs_prev0⟩ := ih (by omega)
    obtain ⟨t, ht, ht_cov⟩ := hgrid ⟨k, by omega⟩
    let a : ℝ := (k : ℝ) / (N : ℝ)
    let b : ℝ := ((k + 1 : ℕ) : ℝ) / (N : ℝ)
    have ha_le1 : a ≤ 1 := by
      dsimp only [a]
      rw [div_le_one hNR]
      exact_mod_cast (by omega : k ≤ N)
    let ua : I := ⟨a, div_nonneg (Nat.cast_nonneg _) hNR.le, ha_le1⟩
    have hua_mem : γ ua ∈ t.baseSet := ht_cov ua le_rfl (by
      dsimp only [ua, a]; apply div_le_div_of_nonneg_right _ hNR.le; norm_cast; omega)
    let qa : Orientation ℝ (ℝ^3) (Fin 3) :=
      Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (γ ua) hua_mem).toLinearEquiv
        (s_prev ⟨ua, le_rfl⟩)
    let S_prev := {u : I // (u : ℝ) ≤ a}
    let S_cur := {u : I // (u : ℝ) ≤ b}
    let s_cur : ∀ u : S_cur, Orientation ℝ (TangentSpace (𝓡 3) (M := M) (γ u.1)) (Fin 3) :=
      fun u =>
        if h : (u.1 : ℝ) ≤ a then
          s_prev ⟨u.1, h⟩
        else
          (Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (γ u.1)
            (ht_cov u.1 (le_of_not_ge h) u.2)).toLinearEquiv).symm qa
    have hs_cur0 : s_cur ⟨0, by positivity⟩ = o₀ := by
      dsimp only [s_cur]
      rw [dif_pos (show ((0 : I) : ℝ) ≤ a by dsimp only [a]; positivity)]
      exact hs_prev0
    refine ⟨s_cur, ?_, hs_cur0⟩
    intro u
    by_cases hlt : (u.1 : ℝ) < a
    · have hU_open : IsOpen {y : S_cur | (y.1 : ℝ) < a} :=
        isOpen_lt (continuous_subtype_val.comp continuous_subtype_val) continuous_const
      obtain ⟨t₁, ht₁, U₁, hU₁_nhds, hU₁_sub, q₁, hq₁⟩ := hs_prev ⟨u.1, hlt.le⟩
      have hU₁_nhds' : {y : S_cur | ∃ h : (y.1 : ℝ) ≤ a, (⟨y.1, h⟩ : S_prev) ∈ U₁} ∈ 𝓝 u := by
        rw [mem_nhds_iff] at hU₁_nhds ⊢
        obtain ⟨V, hVU, hVopen, huV⟩ := hU₁_nhds
        rw [isOpen_induced_iff] at hVopen
        obtain ⟨W, hWopen, hWpre⟩ := hVopen
        refine ⟨(Subtype.val ⁻¹' W) ∩ {y : S_cur | (y.1 : ℝ) < a}, ?_,
          (hWopen.preimage continuous_subtype_val).inter hU_open, ?_⟩
        · intro y hy
          refine ⟨hy.2.le, hVU ?_⟩
          have : (⟨y.1, hy.2.le⟩ : S_prev) ∈ Subtype.val ⁻¹' W := hy.1
          rwa [hWpre] at this
        · refine ⟨?_, hlt⟩
          have : (⟨u.1, hlt.le⟩ : S_prev) ∈ Subtype.val ⁻¹' W := by rwa [hWpre]
          exact this
      refine ⟨t₁, ht₁, _, hU₁_nhds', fun y hy => hU₁_sub ⟨y.1, hy.1⟩ hy.2, q₁, fun y hy => ?_⟩
      dsimp only [s_cur]
      rw [dif_pos hy.1]
      exact hq₁ ⟨y.1, hy.1⟩ hy.2
    · by_cases hgt : a < (u.1 : ℝ)
      · have hU_open : IsOpen {y : S_cur | a < (y.1 : ℝ)} :=
          isOpen_lt continuous_const (continuous_subtype_val.comp continuous_subtype_val)
        refine ⟨t, ht, {y : S_cur | a < (y.1 : ℝ)}, hU_open.mem_nhds hgt,
          fun y hy => ht_cov y.1 hy.le y.2, qa, fun y hy => ?_⟩
        dsimp only [s_cur]
        rw [dif_neg (not_le_of_gt hy)]
        exact Equiv.apply_symm_apply _ qa
      · have hua : u.1 = ua := by ext; dsimp only [ua]; linarith
        have hprev_cont : Continuous (fun y : S_prev => γ y.1) := hγ.comp continuous_subtype_val
        have hua_mem' : γ (⟨ua, le_rfl⟩ : S_prev).1 ∈ t.baseSet := hua_mem
        obtain ⟨U₁, hU₁_nhds, hU₁_sub, h1⟩ :=
          isLocConstOrient_in_chart hprev_cont hs_prev t hua_mem'
        rw [mem_nhds_iff] at hU₁_nhds
        obtain ⟨V, hVU, hVopen, huaV⟩ := hU₁_nhds
        rw [isOpen_induced_iff] at hVopen
        obtain ⟨W, hWopen, hWpre⟩ := hVopen
        have hW_nhds : Subtype.val ⁻¹' W ∈ 𝓝 u := by
          apply (hWopen.preimage continuous_subtype_val).mem_nhds
          have : (⟨ua, le_rfl⟩ : S_prev) ∈ Subtype.val ⁻¹' W := by rwa [hWpre]
          change u.1 ∈ W
          rw [hua]
          exact this
        let U := (Subtype.val ⁻¹' W : Set S_cur)
        have hU_sub : ∀ y ∈ U, γ y.1 ∈ t.baseSet := fun y hy => by
          by_cases hya : (y.1 : ℝ) ≤ a
          · have hyV : (⟨y.1, hya⟩ : S_prev) ∈ V := by rw [← hWpre]; exact hy
            exact hU₁_sub ⟨y.1, hya⟩ (hVU hyV)
          · exact ht_cov y.1 (le_of_not_ge hya) y.2
        refine ⟨t, ht, U, hW_nhds, hU_sub, qa, fun y hy => ?_⟩
        dsimp only [s_cur]
        by_cases hya : (y.1 : ℝ) ≤ a
        · rw [dif_pos hya]
          have hyV : (⟨y.1, hya⟩ : S_prev) ∈ V := by rw [← hWpre]; exact hy
          exact h1 ⟨y.1, hya⟩ (hVU hyV)
        · rw [dif_neg hya]
          exact Equiv.apply_symm_apply _ qa

private lemma homotopy_transport_eq
    {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ^3) M] [IsManifold (𝓡 3) ∞ M]
    {x₀ x₁ : M} {γ₁ γ₂ : Path x₀ x₁} (H : Path.Homotopy γ₁ γ₂)
    {s₁ : ∀ v : I, Orientation ℝ (TangentSpace (𝓡 3) (M := M) (γ₁ v)) (Fin 3)}
    {s₂ : ∀ v : I, Orientation ℝ (TangentSpace (𝓡 3) (M := M) (γ₂ v)) (Fin 3)}
    (hs₁ : IsLocConstOrient γ₁ s₁) (hs₂ : IsLocConstOrient γ₂ s₂)
    (heq0 : (γ₁.source ▸ s₁ 0 : Orientation ℝ (TangentSpace (𝓡 3) (M := M) x₀) (Fin 3)) =
      γ₂.source ▸ s₂ 0) :
    (γ₁.target ▸ s₁ 1 : Orientation ℝ (TangentSpace (𝓡 3) (M := M) x₁) (Fin 3)) =
      γ₂.target ▸ s₂ 1 := by
  let o₀ : Orientation ℝ (TangentSpace (𝓡 3) (M := M) x₀) (Fin 3) :=
    γ₁.source ▸ s₁ 0
  let slice (u : I) : I → M := fun v => H (u, v)
  have hslice_cont (u : I) : Continuous (slice u) :=
    H.continuous.comp (continuous_const.prodMk continuous_id)
  have hslice0 (u : I) : slice u 0 = x₀ := H.source u
  have hslice1 (u : I) : slice u 1 = x₁ := H.target u
  let sec (u : I) : ∀ v : I, Orientation ℝ (TangentSpace (𝓡 3) (M := M) (slice u v)) (Fin 3) :=
    (exists_path_section (hslice_cont u) ((hslice0 u).symm ▸ o₀)).choose
  have hsec_loc (u : I) : IsLocConstOrient (slice u) (sec u) :=
    (exists_path_section (hslice_cont u) ((hslice0 u).symm ▸ o₀)).choose_spec.1
  have hsec_0 (u : I) : sec u 0 = (hslice0 u).symm ▸ o₀ :=
    (exists_path_section (hslice_cont u) ((hslice0 u).symm ▸ o₀)).choose_spec.2
  let endOrient (u : I) : Orientation ℝ (TangentSpace (𝓡 3) (M := M) x₁) (Fin 3) :=
    (hslice1 u) ▸ sec u 1
  have hloc : ∀ u₀ : I, ∃ U ∈ 𝓝 u₀, ∀ u ∈ U, endOrient u = endOrient u₀ := by
    intro u₀
    obtain ⟨N, hN_pos, hgrid⟩ := exists_grid_triv_unitInterval (hslice_cont u₀)
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
    let t_of (k : Fin N) := (hgrid k).choose
    have ht_atlas (k : Fin N) : MemTrivializationAtlas (t_of k) := (hgrid k).choose_spec.choose
    have ht_cov (k : Fin N) : ∀ v : I, (k.val : ℝ) / (N : ℝ) ≤ (v : ℝ) →
        (v : ℝ) ≤ ((k.val + 1 : ℕ) : ℝ) / (N : ℝ) → slice u₀ v ∈ (t_of k).baseSet :=
      (hgrid k).choose_spec.choose_spec
    have htube : ∀ k : Fin N, ∃ U ∈ 𝓝 u₀, ∀ u ∈ U, ∀ v : I,
        (k.val : ℝ) / (N : ℝ) ≤ (v : ℝ) → (v : ℝ) ≤ ((k.val + 1 : ℕ) : ℝ) / (N : ℝ) →
          H (u, v) ∈ (t_of k).baseSet := by
      intro k
      let J : Set I := {v : I | (k.val : ℝ) / (N : ℝ) ≤ (v : ℝ) ∧ (v : ℝ) ≤ ((k.val + 1 : ℕ) : ℝ) / (N : ℝ)}
      have hJ_comp : IsCompact J :=
        (isClosed_le continuous_const continuous_subtype_val).inter
          (isClosed_le continuous_subtype_val continuous_const) |>.isCompact
      have hopen : IsOpen (H ⁻¹' (t_of k).baseSet) := (t_of k).open_baseSet.preimage H.continuous
      have hsub : ({u₀} : Set I) ×ˢ J ⊆ H ⁻¹' (t_of k).baseSet := by
        rintro ⟨u, v⟩ ⟨rfl, hv1, hv2⟩
        exact ht_cov k v hv1 hv2
      obtain ⟨U, V, hUopen, _, hu₀U, hJV, hUV⟩ :=
        generalized_tube_lemma isCompact_singleton hJ_comp hopen hsub
      exact ⟨U, hUopen.mem_nhds (hu₀U rfl), fun u hu v hv1 hv2 => hUV ⟨hu, hJV ⟨hv1, hv2⟩⟩⟩
    let U_all : Set I := ⋂ k : Fin N, (htube k).choose
    have hU_all_nhds : U_all ∈ 𝓝 u₀ := Filter.iInter_mem.mpr fun k => (htube k).choose_spec.1
    have hU_all_cov : ∀ k : Fin N, ∀ u ∈ U_all, ∀ v : I,
        (k.val : ℝ) / (N : ℝ) ≤ (v : ℝ) → (v : ℝ) ≤ ((k.val + 1 : ℕ) : ℝ) / (N : ℝ) →
          H (u, v) ∈ (t_of k).baseSet :=
      fun k u hu => (htube k).choose_spec.2 u (mem_iInter.mp hu k)
    let vk (k : ℕ) (hk : k ≤ N) : I :=
      ⟨(k : ℝ) / (N : ℝ), div_nonneg (Nat.cast_nonneg _) hNR.le,
        (div_le_one hNR).mpr (by exact_mod_cast hk)⟩
    have hind : ∀ k : ℕ, (hk : k < N) →
        ∃ W ∈ 𝓝 u₀, ∃ hW : W ⊆ U_all, ∀ u (hu : u ∈ W),
          Orientation.map (Fin 3)
            ((t_of ⟨k, hk⟩).continuousLinearEquivAt ℝ (slice u (vk (k + 1) (by omega)))
              (hU_all_cov ⟨k, hk⟩ u (hW hu) (vk (k + 1) (by omega))
                (by dsimp only [vk]; apply div_le_div_of_nonneg_right _ hNR.le; norm_cast; omega)
                le_rfl)).toLinearEquiv (sec u (vk (k + 1) (by omega))) =
          Orientation.map (Fin 3)
            ((t_of ⟨k, hk⟩).continuousLinearEquivAt ℝ (slice u₀ (vk (k + 1) (by omega)))
              (ht_cov ⟨k, hk⟩ (vk (k + 1) (by omega))
                (by dsimp only [vk]; apply div_le_div_of_nonneg_right _ hNR.le; norm_cast; omega)
                le_rfl)).toLinearEquiv (sec u₀ (vk (k + 1) (by omega))) := by
      intro k
      induction k with
      | zero =>
        intro h0
        refine ⟨U_all, hU_all_nhds, subset_rfl, fun u hu => ?_⟩
        let J0 := {v : I // (v : ℝ) ≤ (1 : ℝ) / (N : ℝ)}
        have hJ0_conn : ConnectedSpace J0 := by
          have : IsPreconnected {v : I | (v : ℝ) ≤ (1 : ℝ) / (N : ℝ)} := by
            have heq : {v : I | (v : ℝ) ≤ (1 : ℝ) / (N : ℝ)} =
                Set.Icc (0 : I) (vk 1 (by omega)) := by
              ext v
              simp only [Set.mem_setOf_eq, Set.mem_Icc, vk, Nat.cast_one]
              exact ⟨fun h => ⟨v.2.1, h⟩, fun h => h.2⟩
            rw [heq]
            exact isPreconnected_Icc
          exact Subtype.connectedSpace ⟨⟨0, by change ((0 : I) : ℝ) ≤ (1 : ℝ) / (N : ℝ); positivity⟩, this⟩
        have hconst_u := isLocConstOrient_const_inside_chart (X := J0)
          ((hslice_cont u).comp continuous_subtype_val)
          (isLocConstOrient_comp continuous_subtype_val (hsec_loc u))
          (t_of ⟨0, h0⟩)
          (fun v : J0 => hU_all_cov ⟨0, h0⟩ u hu v.1 (by simpa using v.1.2.1) (by simpa using v.2))
          (⟨vk 1 (by omega), by dsimp only [vk]; simp⟩ : J0)
          (⟨0, by positivity⟩ : J0)
        have hconst_u0 := isLocConstOrient_const_inside_chart (X := J0)
          ((hslice_cont u₀).comp continuous_subtype_val)
          (isLocConstOrient_comp continuous_subtype_val (hsec_loc u₀))
          (t_of ⟨0, h0⟩)
          (fun v : J0 => ht_cov ⟨0, h0⟩ v.1 (by simpa using v.1.2.1) (by simpa using v.2))
          (⟨vk 1 (by omega), by dsimp only [vk]; simp⟩ : J0)
          (⟨0, by positivity⟩ : J0)
        dsimp only [Function.comp_apply] at hconst_u hconst_u0
        rw [hconst_u, hconst_u0]
        have hx0_mem : x₀ ∈ (t_of ⟨0, h0⟩).baseSet := by
          have := ht_cov ⟨0, h0⟩ 0 (by simp) (by positivity)
          rwa [hslice0 u₀] at this
        have h0_eq : ∀ w : I, ∀ hw : slice w 0 ∈ (t_of ⟨0, h0⟩).baseSet,
            Orientation.map (Fin 3) ((t_of ⟨0, h0⟩).continuousLinearEquivAt ℝ (slice w 0) hw).toLinearEquiv (sec w 0) =
            Orientation.map (Fin 3) ((t_of ⟨0, h0⟩).continuousLinearEquivAt ℝ x₀ hx0_mem).toLinearEquiv o₀ := by
          intro w hw
          rw [hsec_0 w]
          exact orient_map_eqRec (t_of ⟨0, h0⟩) (hslice0 w).symm hx0_mem hw o₀
        rw [h0_eq u _, h0_eq u₀ _]
      | succ k ih =>
        intro hk1
        obtain ⟨W_prev, hW_prev_nhds, hW_prev_sub, hW_prev_eq⟩ := ih (by omega)
        let t₁ := t_of ⟨k, by omega⟩
        let t₂ := t_of ⟨k + 1, hk1⟩
        haveI : MemTrivializationAtlas t₁ := ht_atlas ⟨k, by omega⟩
        haveI : MemTrivializationAtlas t₂ := ht_atlas ⟨k + 1, hk1⟩
        let v_mid := vk (k + 1) (by omega)
        have hv1 : slice u₀ v_mid ∈ t₁.baseSet :=
          ht_cov ⟨k, by omega⟩ v_mid
            (by dsimp only [v_mid, vk]; apply div_le_div_of_nonneg_right _ hNR.le; norm_cast; omega)
            le_rfl
        have hv2 : slice u₀ v_mid ∈ t₂.baseSet :=
          ht_cov ⟨k + 1, hk1⟩ v_mid le_rfl
            (by dsimp only [v_mid, vk]; apply div_le_div_of_nonneg_right _ hNR.le; norm_cast; omega)
        let q_mid := Orientation.map (Fin 3) (t₁.continuousLinearEquivAt ℝ (slice u₀ v_mid) hv1).toLinearEquiv
          (sec u₀ v_mid)
        obtain ⟨W_cc, hW_cc_nhds, hW_cc_sub, hW_cc_eq⟩ :=
          coordChange_orient_eventuallyEq t₁ t₂ ⟨hv1, hv2⟩ q_mid
        have hcont_mid : Continuous (fun u : I => H (u, v_mid)) :=
          H.continuous.comp (continuous_id.prodMk continuous_const)
        have hpre : (fun u : I => H (u, v_mid)) ⁻¹' W_cc ∈ 𝓝 u₀ :=
          hcont_mid.continuousAt.preimage_mem_nhds hW_cc_nhds
        refine ⟨W_prev ∩ (fun u : I => H (u, v_mid)) ⁻¹' W_cc,
          Filter.inter_mem hW_prev_nhds hpre, inter_subset_left.trans hW_prev_sub, fun u hu => ?_⟩
        have hu_all : u ∈ U_all := hW_prev_sub hu.1
        let Jk := {v : I // ((k + 1 : ℕ) : ℝ) / (N : ℝ) ≤ (v : ℝ) ∧ (v : ℝ) ≤ ((k + 2 : ℕ) : ℝ) / (N : ℝ)}
        have hJk_conn : ConnectedSpace Jk := by
          have heq : {v : I | ((k + 1 : ℕ) : ℝ) / (N : ℝ) ≤ (v : ℝ) ∧ (v : ℝ) ≤ ((k + 2 : ℕ) : ℝ) / (N : ℝ)} =
              Set.Icc (vk (k + 1) (by omega)) (vk (k + 2) (by omega)) := by
            ext v
            simp only [Set.mem_setOf_eq, Set.mem_Icc, vk]
            rfl
          have hpreconn : IsPreconnected {v : I | ((k + 1 : ℕ) : ℝ) / (N : ℝ) ≤ (v : ℝ) ∧ (v : ℝ) ≤ ((k + 2 : ℕ) : ℝ) / (N : ℝ)} := by
            rw [heq]; exact isPreconnected_Icc
          have hne : ({v : I | ((k + 1 : ℕ) : ℝ) / (N : ℝ) ≤ (v : ℝ) ∧ (v : ℝ) ≤ ((k + 2 : ℕ) : ℝ) / (N : ℝ)}).Nonempty :=
            ⟨vk (k + 1) (by omega), le_rfl, by dsimp only [vk]; apply div_le_div_of_nonneg_right _ hNR.le; norm_cast; omega⟩
          exact Subtype.connectedSpace ⟨hne, hpreconn⟩
        have hconst_u := isLocConstOrient_const_inside_chart (X := Jk)
          ((hslice_cont u).comp continuous_subtype_val)
          (isLocConstOrient_comp continuous_subtype_val (hsec_loc u))
          t₂
          (fun v : Jk => hU_all_cov ⟨k + 1, hk1⟩ u hu_all v.1 v.2.1 v.2.2)
          (⟨vk (k + 2) (by omega),
            by dsimp only [vk]; apply div_le_div_of_nonneg_right _ hNR.le; norm_cast; omega, le_rfl⟩ : Jk)
          (⟨v_mid, le_rfl,
            by dsimp only [v_mid, vk]; apply div_le_div_of_nonneg_right _ hNR.le; norm_cast; omega⟩ : Jk)
        have hconst_u0 := isLocConstOrient_const_inside_chart (X := Jk)
          ((hslice_cont u₀).comp continuous_subtype_val)
          (isLocConstOrient_comp continuous_subtype_val (hsec_loc u₀))
          t₂
          (fun v : Jk => ht_cov ⟨k + 1, hk1⟩ v.1 v.2.1 v.2.2)
          (⟨vk (k + 2) (by omega),
            by dsimp only [vk]; apply div_le_div_of_nonneg_right _ hNR.le; norm_cast; omega, le_rfl⟩ : Jk)
          (⟨v_mid, le_rfl,
            by dsimp only [v_mid, vk]; apply div_le_div_of_nonneg_right _ hNR.le; norm_cast; omega⟩ : Jk)
        dsimp only [Function.comp_apply] at hconst_u hconst_u0
        change Orientation.map (Fin 3)
            (t₂.continuousLinearEquivAt ℝ (slice u (vk (k + 2) (by omega)))
              (hU_all_cov ⟨k + 1, hk1⟩ u hu_all (vk (k + 2) (by omega))
                (by dsimp only [vk]; apply div_le_div_of_nonneg_right _ hNR.le; norm_cast; omega)
                le_rfl)).toLinearEquiv (sec u (vk (k + 2) (by omega))) =
          Orientation.map (Fin 3)
            (t₂.continuousLinearEquivAt ℝ (slice u₀ (vk (k + 2) (by omega)))
              (ht_cov ⟨k + 1, hk1⟩ (vk (k + 2) (by omega))
                (by dsimp only [vk]; apply div_le_div_of_nonneg_right _ hNR.le; norm_cast; omega)
                le_rfl)).toLinearEquiv (sec u₀ (vk (k + 2) (by omega)))
        rw [hconst_u, hconst_u0]
        have huv1 : slice u v_mid ∈ t₁.baseSet := (hW_cc_sub hu.2).1
        have huv2 : slice u v_mid ∈ t₂.baseSet := (hW_cc_sub hu.2).2
        rw [map_triv_eq_coordChange_map t₁ t₂ huv1 huv2 (sec u v_mid),
            map_triv_eq_coordChange_map t₁ t₂ hv1 hv2 (sec u₀ v_mid),
            hW_prev_eq u hu.1]
        exact hW_cc_eq (slice u v_mid) hu.2
    obtain ⟨W, hW_nhds, hW_sub, hW_eq⟩ := hind (N - 1) (by omega)
    refine ⟨W, hW_nhds, fun u hu => ?_⟩
    have hN_eq : vk (N - 1 + 1) (by omega) = 1 := by
      ext; dsimp only [vk]
      have : N - 1 + 1 = N := by omega
      rw [this, div_self hNR.ne']; rfl
    have hmap_eq := hW_eq u hu
    let t_last := t_of ⟨N - 1, by omega⟩
    have hx1_mem : x₁ ∈ t_last.baseSet := by
      have := ht_cov ⟨N - 1, by omega⟩ (vk (N - 1 + 1) (by omega))
        (by dsimp only [vk]; apply div_le_div_of_nonneg_right _ hNR.le; norm_cast; omega) le_rfl
      rw [hN_eq, hslice1 u₀] at this
      exact this
    have htr : ∀ w : I, ∀ hw : slice w (vk (N - 1 + 1) (by omega)) ∈ t_last.baseSet,
        Orientation.map (Fin 3) (t_last.continuousLinearEquivAt ℝ (slice w (vk (N - 1 + 1) (by omega))) hw).toLinearEquiv
          (sec w (vk (N - 1 + 1) (by omega))) =
        Orientation.map (Fin 3) (t_last.continuousLinearEquivAt ℝ x₁ hx1_mem).toLinearEquiv (endOrient w) := by
      intro w hw
      dsimp only [endOrient]
      rw [orient_map_eqRec t_last (hslice1 w) (by rw [← hN_eq]; exact hw) hx1_mem (sec w 1)]
      have hsec_eq : ∀ {v₁ v₂ : I} (h : v₁ = v₂), (congrArg (slice w) h ▸ sec w v₁) = sec w v₂ := by
        intro v₁ v₂ h; subst h; rfl
      exact (orient_map_eqRec t_last (congrArg (slice w) hN_eq) hw (by rw [← hN_eq]; exact hw) _).symm.trans
        (by rw [hsec_eq hN_eq])
    rw [htr u _, htr u₀ _] at hmap_eq
    exact (Orientation.map (Fin 3) _).injective hmap_eq
  have hconst : ∀ u : I, endOrient u = endOrient 0 := by
    let S : Set I := {u | endOrient u = endOrient 0}
    have hclopen : IsClopen S := by
      refine ⟨?_, ?_⟩
      · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
        intro u hu
        obtain ⟨U, hU, heq⟩ := hloc u
        filter_upwards [hU] with w hw heqw
        exact hu ((heq w hw).symm.trans heqw)
      · rw [isOpen_iff_mem_nhds]
        intro u hu
        obtain ⟨U, hU, heq⟩ := hloc u
        filter_upwards [hU] with w hw
        exact (heq w hw).trans hu
    have huniv : S = Set.univ := hclopen.eq_univ ⟨0, rfl⟩
    intro u
    have : u ∈ S := by rw [huniv]; trivial
    exact this
  have hs1_eq : endOrient 0 = γ₁.target ▸ s₁ 1 := by
    have hγ1 : ∀ v : I, slice 0 v = γ₁ v := fun v => H.apply_zero v
    have huniq : ∀ v : I, (hγ1 v) ▸ sec 0 v = s₁ v := by
      refine isLocConstOrient_unique γ₁.continuous ?_ hs₁ (x₀ := 0) ?_
      · intro v
        obtain ⟨t, ht, U, hU, hU_sub, q, hq⟩ := hsec_loc 0 v
        refine ⟨t, ht, U, hU, fun y hy => by rw [← hγ1 y]; exact hU_sub y hy, q, fun y hy => ?_⟩
        rw [orient_map_eqRec t (hγ1 y) (hU_sub y hy) _ (sec 0 y)]
        exact hq y hy
      · rw [hsec_0 0]
        dsimp only [o₀]
        have : ∀ {a b c : M} (h1 : a = b) (h2 : c = a) (h3 : b = c)
            (z : Orientation ℝ (TangentSpace (𝓡 3) (M := M) b) (Fin 3)),
            (h1 ▸ (h2 ▸ (h3 ▸ z))) = z := by
          intro a b c h1 h2 h3 z; subst h1; subst h2; rfl
        exact this (hγ1 0) (hslice0 0).symm γ₁.source (s₁ 0)
    have hv1 := huniq 1
    dsimp only [endOrient]
    rw [← hv1]
    have : ∀ {a b c : M} (h1 : a = c) (h2 : a = b) (h3 : b = c)
        (z : Orientation ℝ (TangentSpace (𝓡 3) (M := M) a) (Fin 3)),
        (h1 ▸ z) = (h3 ▸ (h2 ▸ z)) := by
      intro a b c h1 h2 h3 z; subst h2; subst h3; rfl
    exact this (hslice1 0) (hγ1 1) γ₁.target (sec 0 1)
  have hs2_eq : endOrient 1 = γ₂.target ▸ s₂ 1 := by
    have hγ2 : ∀ v : I, slice 1 v = γ₂ v := fun v => H.apply_one v
    have huniq : ∀ v : I, (hγ2 v) ▸ sec 1 v = s₂ v := by
      refine isLocConstOrient_unique γ₂.continuous ?_ hs₂ (x₀ := 0) ?_
      · intro v
        obtain ⟨t, ht, U, hU, hU_sub, q, hq⟩ := hsec_loc 1 v
        refine ⟨t, ht, U, hU, fun y hy => by rw [← hγ2 y]; exact hU_sub y hy, q, fun y hy => ?_⟩
        rw [orient_map_eqRec t (hγ2 y) (hU_sub y hy) _ (sec 1 y)]
        exact hq y hy
      · rw [hsec_0 1]
        dsimp only [o₀]
        rw [heq0]
        have : ∀ {a b c : M} (h1 : a = b) (h2 : c = a) (h3 : b = c)
            (z : Orientation ℝ (TangentSpace (𝓡 3) (M := M) b) (Fin 3)),
            (h1 ▸ (h2 ▸ (h3 ▸ z))) = z := by
          intro a b c h1 h2 h3 z; subst h1; subst h2; rfl
        exact this (hγ2 0) (hslice0 1).symm γ₂.source (s₂ 0)
    have hv1 := huniq 1
    dsimp only [endOrient]
    rw [← hv1]
    have : ∀ {a b c : M} (h1 : a = c) (h2 : a = b) (h3 : b = c)
        (z : Orientation ℝ (TangentSpace (𝓡 3) (M := M) a) (Fin 3)),
        (h1 ▸ z) = (h3 ▸ (h2 ▸ z)) := by
      intro a b c h1 h2 h3 z; subst h2; subst h3; rfl
    exact this (hslice1 1) (hγ2 1) γ₂.target (sec 1 1)
  have h10 := hconst 1
  rw [hs1_eq, hs2_eq] at h10
  exact h10.symm

theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R1.H1 := by
  intro M _ _ _ _
  let V := TangentSpace (𝓡 3) (M := M)
  have : PathConnectedSpace M := inferInstance
  obtain ⟨x₀⟩ := PathConnectedSpace.nonempty (X := M)
  let t₀ := trivializationAt (ℝ^3) V x₀
  have hx₀ : x₀ ∈ t₀.baseSet := mem_baseSet_trivializationAt (ℝ^3) V x₀
  let q₀ : Orientation ℝ (ℝ^3) (Fin 3) := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation
  let o₀ : Orientation ℝ (V x₀) (Fin 3) :=
    (Orientation.map (Fin 3) (t₀.continuousLinearEquivAt ℝ x₀ hx₀).toLinearEquiv).symm q₀
  let transport {x : M} (γ : Path x₀ x) : Orientation ℝ (V x) (Fin 3) :=
    γ.target ▸ (exists_path_section γ.continuous (γ.source.symm ▸ o₀)).choose 1
  have htransport_indep : ∀ {x : M} (γ₁ γ₂ : Path x₀ x), transport γ₁ = transport γ₂ := by
    intro x γ₁ γ₂
    obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic γ₁ γ₂
    let s₁ := (exists_path_section γ₁.continuous (γ₁.source.symm ▸ o₀)).choose
    let s₂ := (exists_path_section γ₂.continuous (γ₂.source.symm ▸ o₀)).choose
    have hs₁ := (exists_path_section γ₁.continuous (γ₁.source.symm ▸ o₀)).choose_spec
    have hs₂ := (exists_path_section γ₂.continuous (γ₂.source.symm ▸ o₀)).choose_spec
    have hcast_inv : ∀ {a b : M} (h : a = b) (z : Orientation ℝ (V b) (Fin 3)),
        (h ▸ (h.symm ▸ z)) = z := by
      intro a b h z; subst h; rfl
    have heq0 : (γ₁.source ▸ s₁ 0 : Orientation ℝ (V x₀) (Fin 3)) = γ₂.source ▸ s₂ 0 := by
      dsimp only [s₁, s₂]
      rw [hs₁.2, hs₂.2, hcast_inv, hcast_inv]
    exact homotopy_transport_eq H hs₁.1 hs₂.1 heq0
  let o : ∀ x : M, Orientation ℝ (V x) (Fin 3) :=
    fun x => transport (PathConnectedSpace.somePath x₀ x)
  refine ⟨o, fun x => ?_⟩
  let t := trivializationAt (ℝ^3) V x
  have hx_t : x ∈ t.baseSet := mem_baseSet_trivializationAt (ℝ^3) V x
  let e := chartAt (ℝ^3) x
  have hx_e : x ∈ e.source := mem_chart_source (ℝ^3) x
  have hW_open : IsOpen (e.target ∩ e.symm ⁻¹' t.baseSet) := by
    have h1 : IsOpen (e.source ∩ t.baseSet) := e.open_source.inter t.open_baseSet
    have h2 : e.target ∩ e.symm ⁻¹' t.baseSet = e.target ∩ e.symm ⁻¹' (e.source ∩ t.baseSet) := by
      ext z; constructor
      · rintro ⟨hz1, hz2⟩; exact ⟨hz1, e.map_target hz1, hz2⟩
      · rintro ⟨hz1, _, hz2⟩; exact ⟨hz1, hz2⟩
    rw [h2]
    exact e.continuousOn_symm.isOpen_inter_preimage e.open_target h1
  have hex_mem : e x ∈ e.target ∩ e.symm ⁻¹' t.baseSet :=
    ⟨e.map_source hx_e, by simpa [e.left_inv hx_e] using hx_t⟩
  obtain ⟨r, hr_pos, hball⟩ := Metric.isOpen_iff.mp hW_open (e x) hex_mem
  let U : Set M := e.source ∩ e ⁻¹' Metric.ball (e x) r
  have hU_open : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  have hx_U : x ∈ U := ⟨hx_e, Metric.mem_ball_self hr_pos⟩
  have hU_sub : U ⊆ t.baseSet := fun y hy => by
    have h1 := hball hy.2
    simpa [e.left_inv hy.1] using h1.2
  refine ⟨t, inferInstance, U, hU_open.mem_nhds hx_U, hU_sub,
    Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ x hx_t).toLinearEquiv (o x), ?_⟩
  intro y hy
  let seg : I → ℝ^3 := fun u => (1 - (u : ℝ)) • e x + (u : ℝ) • e y
  have hseg_cont : Continuous seg :=
    ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)
  have hseg_ball : ∀ u : I, seg u ∈ Metric.ball (e x) r := fun u =>
    (convex_ball (e x) r) (Metric.mem_ball_self hr_pos) hy.2
      (sub_nonneg.mpr u.2.2) u.2.1 (by ring)
  have hseg_target : ∀ u : I, seg u ∈ e.target := fun u => (hball (hseg_ball u)).1
  have hseg_t : ∀ u : I, e.symm (seg u) ∈ t.baseSet := fun u => (hball (hseg_ball u)).2
  let γ_xy : Path x y :=
    { toFun := fun u => e.symm (seg u)
      continuous_toFun := e.continuousOn_symm.comp_continuous hseg_cont hseg_target
      source' := by simp [seg, e.left_inv hx_e]
      target' := by simp [seg, e.left_inv hy.1] }
  let γ₀ := PathConnectedSpace.somePath x₀ x
  let γ₁ := γ₀.trans γ_xy
  have hoy : o y = transport γ₁ := htransport_indep _ γ₁
  rw [hoy]
  let s₁ := (exists_path_section γ₁.continuous (γ₁.source.symm ▸ o₀)).choose
  have hs₁ := (exists_path_section γ₁.continuous (γ₁.source.symm ▸ o₀)).choose_spec
  let half1 : I → I := fun u => ⟨(u : ℝ) / 2, by linarith [u.2.1], by linarith [u.2.2]⟩
  let half2 : I → I := fun u => ⟨(1 + (u : ℝ)) / 2, by linarith [u.2.1], by linarith [u.2.2]⟩
  have hhalf1_cont : Continuous half1 :=
    (continuous_subtype_val.div_const 2).subtype_mk _
  have hhalf2_cont : Continuous half2 :=
    ((continuous_const.add continuous_subtype_val).div_const 2).subtype_mk _
  have hγ1_half1 : ∀ u : I, γ₁ (half1 u) = γ₀ u := fun u => by
    change (γ₀.trans γ_xy) (half1 u) = γ₀ u
    rw [Path.trans_apply]
    have hle : (half1 u : ℝ) ≤ 1 / 2 := by dsimp only [half1]; linarith [u.2.2]
    rw [dif_pos hle]
    congr 1; ext; dsimp only [half1]; ring
  have hγ1_half2 : ∀ u : I, γ₁ (half2 u) = γ_xy u := fun u => by
    change (γ₀.trans γ_xy) (half2 u) = γ_xy u
    rw [Path.trans_apply]
    by_cases h0 : (u : ℝ) = 0
    · have hu0 : u = 0 := Subtype.ext h0
      subst hu0
      have hle : (half2 0 : ℝ) ≤ 1 / 2 := by dsimp only [half2]; norm_num
      rw [dif_pos hle]
      have h1 : (⟨2 * (half2 0 : ℝ), by dsimp only [half2]; norm_num, by dsimp only [half2]; norm_num⟩ : I) = 1 := by
        ext; dsimp only [half2]; norm_num
      rw [h1, γ₀.target, γ_xy.source]
    · have hgt : ¬ (half2 u : ℝ) ≤ 1 / 2 := by
        dsimp only [half2]; have := lt_of_le_of_ne u.2.1 (Ne.symm h0); linarith
      rw [dif_neg hgt]
      congr 1; ext; dsimp only [half2]; ring
  let s₀ := (exists_path_section γ₀.continuous (γ₀.source.symm ▸ o₀)).choose
  have hs₀ := (exists_path_section γ₀.continuous (γ₀.source.symm ▸ o₀)).choose_spec
  have hmid : (hγ1_half1 1) ▸ s₁ (half1 1) = s₀ 1 := by
    have hall : ∀ u : I, (hγ1_half1 u) ▸ s₁ (half1 u) = s₀ u := by
      refine isLocConstOrient_unique γ₀.continuous ?_ hs₀.1 (x₀ := 0) ?_
      · intro u
        obtain ⟨t', ht', U', hU', hU'_sub, q', hq'⟩ := (isLocConstOrient_comp hhalf1_cont hs₁.1) u
        refine ⟨t', ht', U', hU', fun w hw => by rw [← hγ1_half1 w]; exact hU'_sub w hw, q', fun w hw => ?_⟩
        rw [orient_map_eqRec t' (hγ1_half1 w) (hU'_sub w hw) _ (s₁ (half1 w))]
        exact hq' w hw
      · have h0 : half1 0 = 0 := by ext; dsimp only [half1]; norm_num
        have heq_s1 : ∀ {u v : I} (h : u = v), (congrArg γ₁ h ▸ s₁ u) = s₁ v := by
          intro u v h; subst h; rfl
        have hs1_0 : (congrArg γ₁ h0 ▸ s₁ (half1 0)) = γ₁.source.symm ▸ o₀ := by
          rw [heq_s1 h0]
          exact hs₁.2
        have hcomp : ∀ {a b c d : M} (h1 : a = b) (h2 : a = c) (h3 : d = c) (h4 : d = b)
            (x : Orientation ℝ (V a) (Fin 3)) (z : Orientation ℝ (V d) (Fin 3)),
            (h2 ▸ x) = (h3 ▸ z) → (h1 ▸ x) = (h4 ▸ z) := by
          intro a b c d h1 h2 h3 h4 x z hxz
          subst h1; subst h2; subst h3; exact hxz
        exact hcomp (hγ1_half1 0) (congrArg γ₁ h0) γ₁.source.symm γ₀.source.symm
          (s₁ (half1 0)) o₀ hs1_0 |>.trans hs₀.2.symm
    exact hall 1
  have hconst2 := isLocConstOrient_const_inside_chart
    (γ₁.continuous.comp hhalf2_cont)
    (isLocConstOrient_comp hhalf2_cont hs₁.1)
    t
    (fun u => by change γ₁ (half2 u) ∈ t.baseSet; rw [hγ1_half2 u]; exact hseg_t u)
    1 0
  have hh2_1 : half2 1 = 1 := by ext; dsimp only [half2]; norm_num
  have hh2_0 : half2 0 = half1 1 := by ext; dsimp only [half2, half1]; norm_num
  have heq_sec : ∀ {u v : I} (h : u = v), (congrArg γ₁ h ▸ s₁ u) = s₁ v := by
    intro u v h; subst h; rfl
  dsimp only [transport, o]
  have hleft : Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ y (hU_sub hy)).toLinearEquiv
      (γ₁.target ▸ s₁ 1) =
      Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (γ₁ (half2 1))
        (by rw [hγ1_half2 1]; exact hseg_t 1)).toLinearEquiv (s₁ (half2 1)) := by
    rw [orient_map_eqRec t γ₁.target (by rw [← hh2_1, hγ1_half2 1]; exact hseg_t 1) (hU_sub hy) (s₁ 1)]
    rw [← heq_sec hh2_1]
    exact orient_map_eqRec t (congrArg γ₁ hh2_1) (by rw [hγ1_half2 1]; exact hseg_t 1) _ (s₁ (half2 1))
  have hright : Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ x hx_t).toLinearEquiv
      (γ₀.target ▸ s₀ 1) =
      Orientation.map (Fin 3) (t.continuousLinearEquivAt ℝ (γ₁ (half2 0))
        (by rw [hγ1_half2 0]; exact hseg_t 0)).toLinearEquiv (s₁ (half2 0)) := by
    rw [← hmid]
    rw [orient_map_eqRec t γ₀.target (by rw [← hγ1_half1 1, ← hh2_0, hγ1_half2 0]; exact hseg_t 0) hx_t _]
    rw [orient_map_eqRec t (hγ1_half1 1) (by rw [← hh2_0, hγ1_half2 0]; exact hseg_t 0) _ _]
    rw [← heq_sec hh2_0]
    exact orient_map_eqRec t (congrArg γ₁ hh2_0) (by rw [hγ1_half2 0]; exact hseg_t 0) _ (s₁ (half2 0))
  rw [hleft, hright]
  exact hconst2

end PoincareOrientableH1
