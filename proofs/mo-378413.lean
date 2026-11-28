import OMAStatements.S_mo_378413
import Mathlib

open Set Metric

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def annulus : Set Plane := {x | ‖x‖ ∈ Ioo (1 : ℝ) 2}

private theorem closureAnnulus :
    closure annulus = {x : Plane | ‖x‖ ∈ Icc (1 : ℝ) 2} := by
  refine Subset.antisymm (closure_minimal (fun _ hx => ⟨hx.1.le, hx.2.le⟩)
    (isClosed_Icc.preimage continuous_norm)) ?_
  intro x hx
  have hn : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx.1
  let f := fun t : ℝ => (t / ‖x‖) • x
  have hf : Continuous f := (continuous_id.div_const _).smul continuous_const
  have hmaps : f '' Ioo (1 : ℝ) 2 ⊆ annulus := by
    rintro _ ⟨t, ht, rfl⟩
    have ht0 : 0 < t := zero_lt_one.trans ht.1
    have he : ‖f t‖ = t := by
      change ‖(t / ‖x‖) • x‖ = t
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg ht0.le hn.le), div_mul_cancel₀ _ hn.ne']
    change ‖f t‖ ∈ Ioo (1 : ℝ) 2
    rwa [he]
  have hx' : ‖x‖ ∈ closure (Ioo (1 : ℝ) 2) := by
    rw [closure_Ioo (by norm_num : (1 : ℝ) ≠ 2)]
    exact hx
  have heq : f ‖x‖ = x := by simp [f, hn.ne']
  exact closure_mono hmaps (image_closure_subset_closure_image hf ⟨‖x‖, hx', heq⟩)

private theorem boundaryLPC :
    LocallyPathConnectedSpace (sphere (0 : Plane) 1 ∪ sphere (0 : Plane) 2 : Set Plane) := by
  let T := sphere (0 : Plane) 1
  let U := sphere (0 : Plane) 1 ∪ sphere (0 : Plane) 2
  let _ : LocallyPathConnectedSpace T := ChartedSpace.locallyPathConnectedSpace
    (EuclideanSpace ℝ (Fin 1)) T
  let _ : CompactSpace T := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let f₁ : T → U := fun x => ⟨x, Or.inl x.property⟩
  let f₂ : T → U := fun x => ⟨(2 : ℝ) • (x : Plane), Or.inr (by
    have hx : ‖(x : Plane)‖ = 1 := by simpa [mem_sphere, dist_zero_right] using x.property
    rw [mem_sphere, dist_zero_right, norm_smul, hx]
    norm_num)⟩
  have h₁ : Continuous f₁ := continuous_subtype_val.subtype_mk _
  have h₂' : Continuous (fun x : T => (2 : ℝ) • (x : Plane)) :=
    (continuous_subtype_val : Continuous (Subtype.val : T → Plane)).const_smul (2 : ℝ)
  have h₂ : Continuous f₂ := h₂'.subtype_mk _
  let f : T ⊕ T → U := Sum.elim f₁ f₂
  have hf : Continuous f := h₁.sumElim h₂
  have hs : Function.Surjective f := by
    intro x
    rcases x.property with hx | hx
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · have hx' : ‖(x : Plane)‖ = 2 := by simpa [mem_sphere, dist_zero_right] using hx
      have hunit : (1/2 : ℝ) • (x : Plane) ∈ T := by
        change _ ∈ sphere (0 : Plane) 1
        rw [mem_sphere, dist_zero_right, norm_smul, hx']
        norm_num
      refine ⟨Sum.inr ⟨_, hunit⟩, Subtype.ext ?_⟩
      change (2 : ℝ) • ((1/2 : ℝ) • (x : Plane)) = x
      rw [smul_smul, show (2 : ℝ) * (1/2) = 1 by norm_num, one_smul]
  exact (hf.isClosedMap.isQuotientMap hf hs).locallyPathConnectedSpace

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_378413.main) := by
  intro h
  let B := ball (0 : Plane) 1
  let U := annulus ∪ B
  let S := sphere (0 : Plane) 1 ∪ sphere (0 : Plane) 2
  have hA : IsOpen annulus := isOpen_Ioo.preimage continuous_norm
  have hU : IsOpen U := hA.union isOpen_ball
  have hsub : annulus ⊆ ball (0 : Plane) 2 := by
    intro x hx
    rw [mem_ball, dist_zero_right]
    exact hx.2
  have hAb : Bornology.IsBounded annulus := isBounded_ball.subset hsub
  have hUb : Bornology.IsBounded U := hAb.union isBounded_ball
  have hfA : frontier annulus = S := by
    rw [frontier, hA.interior_eq, closureAnnulus]
    ext x
    change (‖x‖ ∈ Icc (1 : ℝ) 2 ∧ ¬ ‖x‖ ∈ Ioo (1 : ℝ) 2) ↔
      x ∈ sphere (0 : Plane) 1 ∪ sphere (0 : Plane) 2
    simp only [mem_Icc, mem_Ioo, mem_union, mem_sphere, dist_zero_right]
    constructor
    · intro z
      rcases lt_or_eq_of_le z.1.1 with h₁ | h₁
      · exact Or.inr (le_antisymm z.1.2 (le_of_not_gt fun h₂ => z.2 ⟨h₁, h₂⟩))
      · exact Or.inl h₁.symm
    · rintro (e | e) <;> rw [e] <;> norm_num
  have hfU : frontier U = S := by
    rw [frontier, hU.interior_eq]
    dsimp only [U, B]
    rw [closure_union, closureAnnulus, closure_ball _ one_ne_zero]
    ext x
    change ((‖x‖ ∈ Icc (1 : ℝ) 2 ∨ x ∈ closedBall (0 : Plane) 1) ∧
      ¬ (‖x‖ ∈ Ioo (1 : ℝ) 2 ∨ x ∈ ball (0 : Plane) 1)) ↔
      x ∈ sphere (0 : Plane) 1 ∪ sphere (0 : Plane) 2
    simp only [mem_Icc, mem_Ioo, mem_closedBall, mem_ball, mem_union, mem_sphere, dist_zero_right]
    constructor
    · intro z
      have hlo : 1 ≤ ‖x‖ := le_of_not_gt (fun e => z.2 (Or.inr e))
      have hhi : ‖x‖ ≤ 2 := z.1.elim And.right (fun e => e.trans (by norm_num))
      rcases lt_or_eq_of_le hlo with h₁ | h₁
      · exact Or.inr (le_antisymm hhi (le_of_not_gt fun h₂ => z.2 (Or.inl ⟨h₁, h₂⟩)))
      · exact Or.inl h₁.symm
    · rintro (e | e) <;> rw [e] <;> norm_num
  have hlpc : LocallyPathConnectedSpace (frontier annulus) := hfA.symm ▸ boundaryLPC
  have he := h annulus U hA hU hAb hUb (hfA.trans hfU.symm) hlpc
  have hz : (0 : Plane) ∈ U := Or.inr (by simp [B, mem_ball])
  have hnz : (0 : Plane) ∉ annulus := by simp [annulus]
  exact hnz (he.symm ▸ hz)