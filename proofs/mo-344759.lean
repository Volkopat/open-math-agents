import OMAStatements.S_mo_344759

namespace OMA.S_mo_344759
noncomputable section
private def homogenize {n : ℕ} (f : Point n →ᵃ[ℝ] ℝ) : Homogeneous n →ₗ[ℝ] ℝ :=
  (f 0 • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).coprod f.linear

private theorem homogenize_eval {n : ℕ} (f : Point n →ᵃ[ℝ] ℝ) (x : Point n) :
    homogenize f (1,x) = f x := by
  have h := congrFun f.decomp x
  simpa [homogenize,LinearMap.coprod_apply,add_comm] using h.symm

private def restrictAffine {n : ℕ} (F : Homogeneous n →ₗ[ℝ] ℝ) : Point n →ᵃ[ℝ] ℝ :=
  F.toAffineMap.comp ((AffineMap.const ℝ (Point n) (1:ℝ)).prod (AffineMap.id ℝ (Point n)))

private theorem sum_marked {ι : Type*} {n : ℕ} (i : ι) (x : Point n) :
    coordinateSum ι n (marked i x) = (1,x) :=
  Finsupp.lsum_single ℝ _ _ _

private theorem marked_mem {ι : Type*} {n : ℕ} {A : ι → Set (Point n)} {i x} (hx : x ∈ A i) :
    marked i x ∈ pointSpan A :=
  Submodule.subset_span ⟨i,x,hx,rfl⟩

private theorem overlap_mem {ι : Type*} {n : ℕ} {A : ι → Set (Point n)} {i j x}
    (hi : x ∈ A i) (hj : x ∈ A j) : marked i x-marked j x ∈ overlapSpan A :=
  Submodule.subset_span ⟨i,j,x,hi,hj,rfl⟩

end
end OMA.S_mo_344759

namespace OMA.S_mo_344759
noncomputable section

private theorem criterion {ι : Type*} {n : ℕ} (A : ι → Set (Point n)) :
    (∀ f : ι → Point n →ᵃ[ℝ] ℝ,
      (∀ i j x, x ∈ A i → x ∈ A j → f i x = f j x) →
      ∃ g : Point n →ᵃ[ℝ] ℝ, ∀ i x, x ∈ A i → g x = f i x) ↔
    pointSpan A ⊓ LinearMap.ker (coordinateSum ι n) ≤ overlapSpan A := by
  classical
  let T := coordinateSum ι n
  constructor
  · intro h v hv
    by_contra hn
    obtain ⟨F,hF,hker⟩ := Submodule.exists_le_ker_of_notMem hn
    let f (i : ι) := restrictAffine (F.comp (Finsupp.lsingle i))
    have hf (i j : ι) (x : Point n) (hi : x ∈ A i) (hj : x ∈ A j) : f i x = f j x := by
      have hu := hker (overlap_mem hi hj)
      change F (marked i x-marked j x) = 0 at hu
      exact sub_eq_zero.mp ((map_sub F _ _).symm.trans hu)
    obtain ⟨g,hg⟩ := h f hf
    let G := homogenize g
    have agree : pointSpan A ≤ LinearMap.ker (F - G.comp T) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,x,hi,rfl⟩
      change F (marked i x) - G (coordinateSum ι n (marked i x)) = 0
      rw [sum_marked,sub_eq_zero,homogenize_eval]
      exact (hg i x hi).symm
    obtain ⟨hvS,hvT⟩ := hv
    have he := agree hvS
    change F v - G (T v) = 0 at he
    change T v = 0 at hvT
    exact hF (by simpa [hvT] using he)
  · intro h f hf
    let F : Copies ι n →ₗ[ℝ] ℝ := Finsupp.lsum ℝ (fun i => homogenize (f i))
    have hm (i : ι) (x : Point n) : F (marked i x) = f i x := by
      rw [show F (marked i x) = homogenize (f i) (1,x) from Finsupp.lsum_single ℝ _ _ _,
        homogenize_eval]
    have vanish : overlapSpan A ≤ LinearMap.ker F := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,j,x,hi,hj,rfl⟩
      change F (marked i x-marked j x) = 0
      rw [map_sub,hm,hm,hf i j x hi hj,sub_self]
    let U := pointSpan A
    let L := T.comp U.subtype
    let φ := F.comp U.subtype
    have hr : φ ∈ LinearMap.range L.dualMap := by
      have he := LinearMap.range_dualMap_eq_dualAnnihilator_ker (K := ℝ)
        (V₁ := ↥U) (V₂ := Homogeneous n) L
      rw [he, Submodule.mem_dualAnnihilator]
      intro v hv
      exact vanish (h ⟨v.property,hv⟩)
    obtain ⟨G,hG⟩ := hr
    refine ⟨restrictAffine G,fun i x hi => ?_⟩
    have hh := DFunLike.congr_fun hG (⟨marked i x,marked_mem hi⟩ : U)
    change G (coordinateSum ι n (marked i x)) = F (marked i x) at hh
    rw [sum_marked,hm] at hh
    exact hh

end
end OMA.S_mo_344759

theorem OMA.solution : type_of% @OMA.S_mo_344759.main := by
  intro ι n A _
  exact OMA.S_mo_344759.criterion A
