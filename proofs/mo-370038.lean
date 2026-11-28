import OMAStatements.S_mo_370038

namespace OMA.S_mo_370038
open MeasureTheory

private lemma hull_simplex {d n : ℕ} (p : Fin n → Point d) :
    convexHull ℝ (Set.range p) =
      (fun w : Fin n → ℝ => ∑ i, w i • p i) '' stdSimplex ℝ (Fin n) := by
  classical
  let L : (Fin n → ℝ) →ₗ[ℝ] Point d := ∑ i, (LinearMap.proj (R := ℝ) i).smulRight (p i)
  have hL (w : Fin n → ℝ) : L w = ∑ i, w i • p i := by simp [L]
  rw [show (fun w : Fin n → ℝ => ∑ i, w i • p i) = ⇑L by funext w; exact (hL w).symm]
  rw [← convexHull_rangle_single_eq_stdSimplex, LinearMap.image_convexHull, ← Set.range_comp]
  congr 2
  funext i
  simp [hL,Pi.single_apply]

lemma inside_measurable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (X : ℕ → Ω → Point d)
    (hm : ∀i, Measurable (X i)) (n : ℕ) : MeasurableSet (inside X n) := by
  let C := {p : (Point d × (Fin n → Point d)) × stdSimplex ℝ (Fin n) |
    p.1.1 = ∑ i, p.2.val i • p.1.2 i}
  have hC : IsClosed C := by
    apply isClosed_eq (continuous_fst.comp continuous_fst)
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).smul
      ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
  have hclosed : IsClosed (Prod.fst '' C) := isClosedMap_fst_of_compactSpace C hC
  let F (ω : Ω) := (X 0 ω, fun i : Fin n => X (i.val+1) ω)
  have hmF : Measurable F := (hm 0).prodMk (measurable_pi_lambda _ fun i => hm (i.val+1))
  convert! hmF hclosed.measurableSet using 1
  ext ω
  change X 0 ω ∈ convexHull ℝ _ ↔ F ω ∈ Prod.fst '' C
  rw [hull_simplex]
  constructor
  · rintro ⟨w,hw,he⟩
    exact ⟨(F ω,⟨w,hw⟩),he.symm,rfl⟩
  · rintro ⟨⟨p, w⟩, hp, hp'⟩
    change p = F ω at hp'
    subst p
    exact ⟨w.val,w.property,hp.symm⟩
end OMA.S_mo_370038

namespace OMA.S_mo_370038
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped Topology ENNReal

lemma ae_support_subset (d : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → Point d)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hl : ∀ i, μ.map (X i)=μ.map (X 0)) :
    ∀ᵐ ω ∂μ, (μ.map (X 0)).support ⊆ closure (Set.range fun j : ℕ => X (j+1) ω) := by
  classical
  let B := countableBasis (Point d)
  have hB : IsTopologicalBasis B := isBasis_countableBasis _
  have : Countable B := (countable_countableBasis _).to_subtype
  have one (U : B) : ∀ᵐ ω ∂μ, 0 < (μ.map (X 0)) U.val → ∃ k, X (k+1) ω ∈ U.val := by
    by_cases hU : 0 < (μ.map (X 0)) U.val
    · have hmeas := (hB.isOpen U.property).measurableSet
      let s (k : ℕ) := X k ⁻¹' U.val
      have hs (k : ℕ) : MeasurableSet (s k) := hm k hmeas
      have hi' : iIndepSet s μ := (iIndepSet_iff_meas_biInter hs).mpr
        (fun S => hi.measure_inter_preimage_eq_mul S (sets:=fun _ => U.val) (fun _ _ => hmeas))
      have hval (k : ℕ) : μ (s k)=(μ.map (X 0)) U.val := by
        rw [← hl k,Measure.map_apply (hm k) hmeas]
      have hdiverge : (∑' k, μ (s k))=∞ := by
        simp_rw [hval];exact ENNReal.tsum_const_eq_top_of_ne_zero hU.ne'
      have hlim := (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hs)).mpr (measure_limsup_eq_one hs hi' hdiverge)
      filter_upwards [hlim] with ω hω
      intro _
      obtain ⟨k,hk,hmem⟩ := (frequently_atTop.mp (mem_limsup_iff_frequently_mem.mp hω)) 1
      change X k ω ∈ U.val at hmem
      exact ⟨k-1,by simpa only [Nat.sub_add_cancel hk] using hmem⟩
    · exact Eventually.of_forall (fun _ h => (hU h).elim)
  filter_upwards [ae_all_iff.mpr one] with ω hω
  intro x hx
  apply hB.mem_closure_iff.mpr
  intro U hU hxU
  have hpos := (Measure.mem_support_iff_forall _).mp hx U ((hB.isOpen hU).mem_nhds hxU)
  obtain ⟨k,hk⟩ := hω ⟨U,hU⟩ hpos
  exact ⟨X (k+1) ω,hk,⟨k,rfl⟩⟩
end OMA.S_mo_370038

namespace OMA.S_mo_370038
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

private lemma interior_hull {d : ℕ} (s : Set (Point d)) :
    interior (closure (convexHull ℝ s)) ⊆ convexHull ℝ s := by
  let H := convexHull ℝ s
  have hconv : Convex ℝ H := convex_convexHull _ _
  by_cases hi : (interior H).Nonempty
  · exact (hconv.interior_closure_eq_interior_of_nonempty_interior hi) ▸ interior_subset
  · have hempty : interior H=∅ := Set.not_nonempty_iff_eq_empty.mp hi
    have hnull : volume (closure H)=0 := by simpa [frontier,hempty] using hconv.addHaar_frontier volume
    intro x hx
    have hpos : 0 < volume (interior (closure H)) := isOpen_interior.measure_pos volume ⟨x,hx⟩
    exact ((not_lt_of_ge (measure_mono interior_subset)) (hnull ▸ hpos)).elim

private lemma ae_interior {d : ℕ} (ν : Measure (Point d)) (h : ν ≪ volume) :
    ∀ᵐ x ∂ν, x ∈ interior (convexHull ℝ ν.support) := by
  let K := convexHull ℝ ν.support
  have hnull : ν (frontier K)=0 := h ((convex_convexHull ℝ ν.support).addHaar_frontier volume)
  have hout : ∀ᵐ x ∂ν, x ∉ frontier K := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hnull
  filter_upwards [Measure.support_mem_ae (μ := ν),hout] with x hx hf
  have hc : x ∈ closure K := subset_closure (subset_convexHull ℝ _ hx)
  by_contra hn
  exact hf ⟨hc,hn⟩

private def sampleHull {d : ℕ} (Y : ℕ → Point d) (n : ℕ) :=
  convexHull ℝ (Set.range fun i : Fin n => Y i.val)

private lemma prefix_mono {d : ℕ} (Y : ℕ → Point d) : Monotone (sampleHull Y) := by
  intro n m h
  apply convexHull_mono
  rintro _ ⟨i,rfl⟩
  exact ⟨i.castLE h,rfl⟩

private lemma hull_prefix {d : ℕ} (Y : ℕ → Point d) :
    convexHull ℝ (Set.range Y) ⊆ ⋃ n, sampleHull Y n := by
  apply convexHull_min
  · rintro _ ⟨i,rfl⟩
    exact mem_iUnion.mpr ⟨i+1,subset_convexHull ℝ _ ⟨⟨i,by omega⟩,rfl⟩⟩
  · exact (prefix_mono Y).directed_le.convex_iUnion (fun n => convex_convexHull _ _)

private lemma approx_support {d : ℕ} (S : Set (Point d)) (Y : ℕ → Point d) (x : Point d)
    (hS : S ⊆ closure (Set.range Y)) (hx : x ∈ interior (convexHull ℝ S)) :
    ∃ n, x ∈ sampleHull Y n := by
  have h : convexHull ℝ S ⊆ closure (convexHull ℝ (Set.range Y)) :=
    convexHull_min (hS.trans (closure_mono (subset_convexHull ℝ _))) (convex_convexHull _ _).closure
  exact mem_iUnion.mp (hull_prefix Y (interior_hull _ (interior_mono h hx)))

end OMA.S_mo_370038

open OMA.S_mo_370038 MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem OMA.solution : type_of% @OMA.S_mo_370038.main := by
  intro d Ω _ μ _ X hm hi hl hac
  have hmono : Monotone (inside X) := by
    intro n m h ω hω
    exact prefix_mono (fun j => X (j+1) ω) h hω
  have htest := ae_of_ae_map (hm 0).aemeasurable (ae_interior (μ.map (X 0)) hac)
  have hfull : ∀ᵐ ω ∂μ, ω ∈ ⋃ n, inside X n := by
    filter_upwards [htest,ae_support_subset d μ X hm hi hl] with ω hω hd
    obtain ⟨n,hn⟩ := approx_support (μ.map (X 0)).support (fun j => X (j+1) ω) (X 0 ω) hd hω
    exact mem_iUnion.mpr ⟨n,hn⟩
  have heq : μ (⋃ n, inside X n)=1 :=
    (prob_compl_eq_zero_iff (MeasurableSet.iUnion (inside_measurable X hm))).mp (ae_iff.mp hfull)
  simpa only [heq,Function.comp_def] using tendsto_measure_iUnion_atTop (μ := μ) hmono
