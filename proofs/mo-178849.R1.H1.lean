import OMAReductions.R_mo_178849_R1
/- Adapted from OpenAI openai/math 3344da59991ed94f9ba711217b29c1d760badfa6 and the private threshold overlay. -/
section
open Set MeasureTheory
open scoped Classical Pointwise
namespace FT
def Raw {H X Y : Type} [Group H] [MulAction H X] [MulAction H Y] [TopologicalSpace X]
    (K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)) (n : ℕ)
    (ok : Set (Y →₀ ℝ) → Prop) (count : (X → Set (Y →₀ ℝ)) → Prop) : Prop :=
 let V := Y →₀ ℝ
 let S := Geometry.SimplicialComplex ℝ V
 let c := fun s : Finset V => convexHull ℝ (s : Set V)
 let tr := fun (A : Set (Finset V)) (p : Set V) => {s ∈ A | (s : Set V) ⊆ p}
 let sub := fun (L B : S) => L.space=B.space ∧ (∀ s∈L.faces,∃ t∈B.faces,c s⊆c t) ∧
  ∀ t∈B.faces,(∀ s∈L.faces,c s∩c t=convexHull ℝ ((s:Set V)∩c t)) ∧ (tr L.faces (c t)).Finite
 let a := fun h : H => Finsupp.domLCongr (R:=ℝ) (MulAction.toPerm h : Y≃Y)
 ∃ (T : ℕ → X → S) (P : ℕ → X → Set V), count (P 0) ∧
 (∀ i x,sub (T i x) K) ∧ (∀ i x v,v∈P i x → ∃ s∈(T i x).faces,v∈c s ∧ c s⊆P i x) ∧
 (∀ i t,t∈K.faces → IsLocallyConstant (fun x=>tr (T i x).faces (c t)) ∧
  IsLocallyConstant (fun x=>tr {s∈(T i x).faces | c s⊆P i x} (c t))) ∧
 (∀ i h x s,s∈(T i x).faces → s.map (a h).toEmbedding∈(T i (h•x)).faces) ∧
 (∀ i h x v,v∈P i x → a h v∈P i (h•x)) ∧ (∀ x,T n x=K ∧ P n x=K.space) ∧
 ∀ i,i<n → ∀ x,sub (T i x) (T (i+1) x) ∧ P i x⊆P (i+1) x ∧
 (∀ t∈(T (i+1) x).faces,c t⊆P (i+1) x → ∀ s∈(T i x).faces,c s⊆c t∩P i x → s.card<t.card) ∧
 ok (P (i+1) x \ P i x)
end FT
end
section
theorem ite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort*} {t e : α} : (ite c t e) = t := if_pos hc
theorem ite_eq_right {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort*} {t e : α} : (ite c t e) = e := if_neg hc
theorem dite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort*} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := dif_pos hc
theorem dite_eq_right {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort*} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := dif_neg hc
theorem Finsupp.mapDomain_apply_of_injective {α β M : Type*} [AddCommMonoid M] {f : α → β} (hf : f.Injective) (x : α →₀ M) (a : α) : Finsupp.mapDomain f x (f a) = x a := Finsupp.mapDomain_apply hf x a
theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*} [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a} (hf : ∀ a, Measurable fun c => f c a) : Measurable f := measurable_pi_lambda f hf
def Set.equivOfEq {α : Type*} {s t : Set α} (h : s = t) : s ≃ t := Equiv.setCongr h
theorem AffineBasis.setFinite {ι k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P] [FiniteDimensional k V] {s : Set ι} (b : AffineBasis s k P) : s.Finite := b.finite_set
theorem Isometry.lipschitzWith {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β] {f : α → β} (h : Isometry f) : LipschitzWith 1 f := h.lipschitz
@[simp] theorem SimpleGraph.ncard_neighborSet {V : Type*} (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] : (G.neighborSet v).ncard = G.degree v := by
  simp [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse
section
open Set Finset
open scoped Topology
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma exists_weights_of_mem_affineSpan {s : Finset E} {v : E}
    (hv : v ∈ affineSpan ℝ (s : Set E)) :
    ∃ w : E → ℝ, ∑ x ∈ s, w x = 1 ∧ v = ∑ x ∈ s, w x • x := by
  classical
  have hv' : v ∈ affineSpan ℝ (Set.range (fun x : s => (x : E))) := by simpa using hv
  obtain ⟨w, hw, hvw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hv'
  let w' : E → ℝ := fun x => if h : x ∈ s then w ⟨x, h⟩ else 0
  have hsum : ∑ x ∈ s, w' x = ∑ x : s, w x := by
    rw [← Finset.sum_attach]
    simp [w']
  refine ⟨w', hsum.trans hw, ?_⟩
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw] at hvw
  rw [← Finset.sum_attach]
  simpa [w'] using hvw
lemma exists_small_positive_weights {I : Type*} (s : Finset I) (w : I → ℝ)
    {c : ℝ} (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ i ∈ s, 0 < δ * w i + (1-δ) * c := by
  have he : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i ∈ s, 0 < δ * w i + (1-δ) * c := by
    apply (s.eventually_all).mpr
    intro i _
    have hcont : Continuous (fun δ : ℝ => δ * w i + (1-δ) * c) := by fun_prop
    exact hcont.continuousAt.eventually (eventually_gt_nhds (by simpa using hc))
  have he' := he.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hlt := (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  exact (hpos.and (hlt.and he')).exists
lemma sum_weights_mem_convexHull (s : Finset E) {w : E → ℝ}
    (hw : ∀ x ∈ s, 0 ≤ w x) (hsum : ∑ x ∈ s, w x = 1) :
    ∑ x ∈ s, w x • x ∈ convexHull ℝ (s : Set E) :=
  (convex_convexHull ℝ (s : Set E)).sum_mem hw hsum
    (fun _ hx => subset_convexHull ℝ (s : Set E) hx)
end
section
open Set Finset
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma same_side_cone_overlap [DecidableEq E] {F : Finset E} (hF : F.Nonempty) {u v : E}
    (huF : u ∉ F) (hvspan : v ∈ affineSpan ℝ ((insert u F : Finset E) : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    (hu : b < f u) (hv : b < f v) :
    ∃ p, p ∈ convexHull ℝ ((insert u F : Finset E) : Set E) ∧
      p ∈ convexHull ℝ ((insert v F : Finset E) : Set E) ∧ b < f p := by
  classical
  obtain ⟨w, hw, hvw⟩ := exists_weights_of_mem_affineSpan hvspan
  have hsum : w u + ∑ x ∈ F, w x = 1 := by simpa [Finset.sum_insert huF] using hw
  have hfv : f v = w u * f u + (∑ x ∈ F, w x) * b := by
    rw [hvw, map_sum, Finset.sum_insert huF]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun x hx => congrArg (w x * ·) (hFb x hx))]
    rw [Finset.sum_mul]
  have hwu : 0 < w u := by
    have he : f v - b = w u * (f u - b) := by linear_combination hfv + b * hsum
    have hm : 0 < w u * (f u - b) := he ▸ sub_pos.mpr hv
    exact (mul_pos_iff_of_pos_right (sub_pos.mpr hu)).mp hm
  let c : ℝ := (F.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr hF.card_pos)
  have hcsum : ∑ _x ∈ F, c = 1 := by
    simp [c, ne_of_gt (Nat.cast_pos.mpr hF.card_pos : (0 : ℝ) < F.card)]
  let q : E := ∑ x ∈ F, c • x
  have hq : q ∈ convexHull ℝ (F : Set E) :=
    sum_weights_mem_convexHull F (fun _ _ => hc.le) hcsum
  have hfq : f q = b := by
    change f (∑ x ∈ F, c • x) = b
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun x hx => congrArg (c * ·) (hFb x hx)),
      ← Finset.sum_mul, hcsum, one_mul]
  obtain ⟨δ, hδ, hδ1, hδw⟩ := exists_small_positive_weights F w hc
  let r : E → ℝ := fun x => if x = u then 0 else c
  have hrF (x : E) (hx : x ∈ F) : r x = c := by
    simp [r, ne_of_mem_of_not_mem hx huF]
  have hru : r u = 0 := by simp [r]
  have hrsum : ∑ x ∈ insert u F, r x = 1 := by
    rw [Finset.sum_insert huF, hru, zero_add]
    rw [Finset.sum_congr rfl hrF]
    exact hcsum
  have hrq : ∑ x ∈ insert u F, r x • x = q := by
    rw [Finset.sum_insert huF, hru, zero_smul, zero_add]
    exact Finset.sum_congr rfl (fun x hx => by rw [hrF x hx])
  let z : E → ℝ := fun x => δ * w x + (1-δ) * r x
  have hz : ∀ x ∈ insert u F, 0 ≤ z x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp only [z, hru, mul_zero, add_zero]
      exact (mul_pos hδ hwu).le
    · simpa only [z, hrF x hx] using (hδw x hx).le
  have hzsum : ∑ x ∈ insert u F, z x = 1 := by
    simp only [z, Finset.sum_add_distrib, ← Finset.mul_sum, hw, hrsum]
    ring
  have hzp : ∑ x ∈ insert u F, z x • x = δ • v + (1-δ) • q := by
    simp only [z, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
    rw [← hvw, hrq]
  refine ⟨δ • v + (1-δ) • q, ?_, ?_, ?_⟩
  · rw [← hzp]
    exact sum_weights_mem_convexHull _ hz hzsum
  · apply (convex_convexHull ℝ ((insert v F : Finset E) : Set E))
      (subset_convexHull ℝ _ (Finset.mem_insert_self v F))
      ((convexHull_mono (show (F : Set E) ⊆ ((insert v F : Finset E) : Set E) from
        Finset.subset_insert _ _)) hq) hδ.le (sub_nonneg.mpr hδ1.le)
    ring
  · simp only [map_add, map_smul, smul_eq_mul, hfq]
    nlinarith [mul_pos hδ (sub_pos.mpr hv)]
end
section
open Set Finset
open scoped Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma apex_notMem_affineSpan {F : Finset E} {u : E} (hu : u ∉ F)
    (h : AffineIndependent ℝ ((↑) : ↥(insert u F) → E)) :
    u ∉ affineSpan ℝ (F : Set E) := by
  let i : ↥(insert u F) := ⟨u, Finset.mem_insert_self _ _⟩
  have hnot := h.notMem_affineSpan_sdiff i Set.univ
  have he : ((↑) : ↥(insert u F) → E) '' (Set.univ \ {i}) = (F : Set E) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      rcases Finset.mem_insert.mp j.property with hj' | hj'
      · exact False.elim (hj.2 (Set.mem_singleton_iff.mpr (Subtype.ext hj')))
      · exact hj'
    · intro hx
      refine ⟨⟨x, Finset.mem_insert_of_mem hx⟩, ⟨Set.mem_univ _, ?_⟩, rfl⟩
      intro hi
      have hxu : x = u := congrArg Subtype.val (Set.mem_singleton_iff.mp hi)
      exact hu (hxu ▸ hx)
  simpa only [he] using hnot
lemma exists_facet_form {F : Finset E} (hF : F.Nonempty) {u : E}
    (hu : u ∉ affineSpan ℝ (F : Set E)) :
    ∃ (f : E →ₗ[ℝ] ℝ) (b : ℝ), (∀ x ∈ F, f x = b) ∧ f u ≠ b := by
  obtain ⟨a, ha⟩ := hF
  have has : a ∈ affineSpan ℝ (F : Set E) := subset_affineSpan ℝ _ ha
  have hua : u - a ∉ (affineSpan ℝ (F : Set E)).direction := by
    simpa only [← AffineSubspace.vsub_right_mem_direction_iff_mem has u,
      vsub_eq_sub] using hu
  obtain ⟨f, hfu, hfker⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hua inferInstance
  refine ⟨f, f a, ?_, ?_⟩
  · intro x hx
    have hxa : x - a ∈ (affineSpan ℝ (F : Set E)).direction :=
      (AffineSubspace.vsub_right_mem_direction_iff_mem has x).mpr
        (subset_affineSpan ℝ _ hx)
    have hz : f (x-a) = 0 := by
      have hm : f (x-a) ∈ (affineSpan ℝ (F : Set E)).direction.map f :=
        Submodule.mem_map.mpr ⟨x-a, hxa, rfl⟩
      rw [hfker, Submodule.mem_bot] at hm
      exact hm
    simpa only [map_sub, sub_eq_zero] using hz
  · simpa only [map_sub, sub_ne_zero] using hfu
lemma affineForm_eq_on_convexHull {F : Finset E} (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (h : ∀ x ∈ F, f x = b) {p : E} (hp : p ∈ convexHull ℝ (F : Set E)) : f p = b := by
  have he : (F : Set E).EqOn f.toAffineMap (AffineMap.const ℝ E b) := h
  exact AffineMap.eqOn_affineSpan he (convexHull_subset_affineSpan _ hp)
lemma eq_of_facet_same_side (K : Geometry.SimplicialComplex ℝ E)
    {F : Finset E} (hF : F.Nonempty) {u v : E} (huF : u ∉ F) (hvF : v ∉ F)
    (huK : insert u F ∈ K.faces) (hvK : insert v F ∈ K.faces)
    (hspan : v ∈ affineSpan ℝ ((insert u F : Finset E) : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    (hu : b < f u) (hv : b < f v) : u = v := by
  by_contra huv
  obtain ⟨p, hpu, hpv, hp⟩ := same_side_cone_overlap hF huF hspan f b hFb hu hv
  have hinter : ((insert u F : Finset E) : Set E) ∩
      ((insert v F : Finset E) : Set E) = (F : Set E) := by
    ext x
    simp only [Finset.coe_insert, Set.mem_inter_iff, Set.mem_insert_iff]
    aesop
  have hpf := K.inter_subset_convexHull huK hvK ⟨hpu, hpv⟩
  rw [hinter] at hpf
  exact (ne_of_gt hp) (affineForm_eq_on_convexHull f b hFb hpf)
lemma facet_apex_card_le_two (K : Geometry.SimplicialComplex ℝ E)
    {F A : Finset E} (hF : F.Nonempty)
    (hAK : ∀ u ∈ A, insert u F ∈ K.faces) (hAF : ∀ u ∈ A, u ∉ F)
    (hcarrier : ∀ u ∈ A, ∀ v ∈ A,
      affineSpan ℝ ((insert u F : Finset E) : Set E) =
        affineSpan ℝ ((insert v F : Finset E) : Set E)) : A.card ≤ 2 := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  obtain ⟨f, b, hFb, hab⟩ := exists_facet_form hF
    (apex_notMem_affineSpan (hAF a ha) (K.indep (hAK a ha)))
  have hne (u : E) (hu : u ∈ A) : f u ≠ b := by
    intro hub
    have hon : ((insert u F : Finset E) : Set E).EqOn
        f.toAffineMap (AffineMap.const ℝ E b) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hub
      · exact hFb x hx
    have he := AffineMap.eqOn_affineSpan hon
    apply hab
    apply he
    rw [hcarrier u hu a ha]
    exact subset_affineSpan ℝ _ (Finset.mem_insert_self _ _)
  let side : A → Bool := fun u => decide (b < f u)
  have hinj : Function.Injective side := by
    intro u v huv
    apply Subtype.ext
    have hs : (b < f u) ↔ (b < f v) := by
      exact decide_eq_decide.mp huv
    have hspan : (v : E) ∈ affineSpan ℝ ((insert (u : E) F : Finset E) : Set E) := by
      rw [hcarrier u u.property v v.property]
      exact subset_affineSpan ℝ _ (Finset.mem_insert_self _ _)
    by_cases hu : b < f u
    · exact eq_of_facet_same_side K hF (hAF u u.property) (hAF v v.property)
        (hAK u u.property) (hAK v v.property) hspan f b hFb hu (hs.mp hu)
    · have hv : ¬ b < f v := fun hv => hu (hs.mpr hv)
      have hul : f u < b := lt_of_le_of_ne (le_of_not_gt hu) (hne u u.property)
      have hvl : f v < b := lt_of_le_of_ne (le_of_not_gt hv) (hne v v.property)
      exact eq_of_facet_same_side K hF (hAF u u.property) (hAF v v.property)
        (hAK u u.property) (hAK v v.property) hspan (-f) (-b)
        (fun x hx => congrArg Neg.neg (hFb x hx))
        (neg_lt_neg hul) (neg_lt_neg hvl)
  simpa using Fintype.card_le_of_injective side hinj
lemma affineSpan_eq_of_card_eq {s t : Finset E}
    (ht : AffineIndependent ℝ ((↑) : t → E))
    (hst : (t : Set E) ⊆ convexHull ℝ (s : Set E)) (hc : t.card = s.card) :
    affineSpan ℝ (t : Set E) = affineSpan ℝ (s : Set E) := by
  have hle : affineSpan ℝ (t : Set E) ≤ affineSpan ℝ (s : Set E) :=
    affineSpan_le.mpr (hst.trans (convexHull_subset_affineSpan _))
  by_contra hne
  have hlt := ht.card_lt_card_of_affineSpan_lt_affineSpan (lt_of_le_of_ne hle hne)
  omega
lemma facet_coface_card_le_two (K : Geometry.SimplicialComplex ℝ E)
    {F S : Finset E} {B : Finset (Finset E)} (hF : F.Nonempty)
    (hS : S.card = F.card + 1) (hB : ∀ t ∈ B, t ∈ K.faces)
    (hFB : ∀ t ∈ B, F ⊆ t ∧ t.card = F.card + 1)
    (hBS : ∀ t ∈ B, (t : Set E) ⊆ convexHull ℝ (S : Set E)) : B.card ≤ 2 := by
  have hex (t : B) : ∃ u ∉ F, insert u F = (t : Finset E) :=
    Finset.exists_eq_insert_iff.mpr ⟨(hFB t t.property).1, (hFB t t.property).2.symm⟩
  let apex : B → E := fun t => (hex t).choose
  have ha (t : B) : apex t ∉ F ∧ insert (apex t) F = (t : Finset E) :=
    (hex t).choose_spec
  let A : Finset E := Finset.univ.image apex
  have hAK : ∀ u ∈ A, insert u F ∈ K.faces := by
    intro u hu
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    rw [(ha t).2]
    exact hB t t.property
  have hAF : ∀ u ∈ A, u ∉ F := by
    intro u hu
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    exact (ha t).1
  have hsp (u : E) (hu : u ∈ A) :
      affineSpan ℝ ((insert u F : Finset E) : Set E) = affineSpan ℝ (S : Set E) := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    rw [(ha t).2]
    exact affineSpan_eq_of_card_eq (K.indep (hB t t.property)) (hBS t t.property)
      ((hFB t t.property).2.trans hS.symm)
  have hA := facet_apex_card_le_two K hF hAK hAF
    (fun u hu v hv => (hsp u hu).trans (hsp v hv).symm)
  have hinj : Function.Injective apex := by
    intro t t' he
    apply Subtype.ext
    calc (t : Finset E) = insert (apex t) F := (ha t).2.symm
         _ = insert (apex t') F := by rw [he]
         _ = (t' : Finset E) := (ha t').2
  have hc : A.card = B.card := by simp [A, Finset.card_image_of_injective _ hinj]
  rwa [hc] at hA
end
section
open Set Finset
open scoped Topology Classical
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma positiveCombination_carrier {F T : Finset E}
    (hF : AffineIndependent ℝ ((↑) : F → E)) (hTF : T ⊆ F)
    (w : E → ℝ) (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1)
    (hq : (∑ x ∈ F, w x • x) ∈ convexHull ℝ (T : Set E)) : F ⊆ T := by
  classical
  obtain ⟨a,_,has,hap⟩ := Finset.mem_convexHull'.mp hq
  let a' : E → ℝ := fun x => if x ∈ T then a x else 0
  have hs : ∑ x ∈ F, a' x = 1 := by
    calc
      _ = ∑ x ∈ T, a' x := (Finset.sum_subset hTF (fun x _ hx => by simp [a',hx])).symm
      _ = ∑ x ∈ T, a x := Finset.sum_congr rfl (fun x hx => by simp [a',hx])
      _ = 1 := has
  have hp : ∑ x ∈ F, a' x • x = ∑ x ∈ F, w x • x := by
    calc
      _ = ∑ x ∈ T, a' x • x :=
        (Finset.sum_subset hTF (fun x _ hx => by simp [a',hx])).symm
      _ = ∑ x ∈ T, a x • x := Finset.sum_congr rfl (fun x hx => by simp [a',hx])
      _ = _ := hap
  have he := hF.eq_of_sum_eq_sum_subtype (hs.trans hws.symm) hp
  intro x hx
  by_contra hxt
  have hzero : w x = 0 := by simpa [a',hxt] using (he x hx).symm
  exact (ne_of_gt (hw x hx)) hzero
lemma simplex_contains_positivePoint (K : Geometry.SimplicialComplex ℝ E)
    {F T : Finset E} (hF : F ∈ K.faces) (hT : T ∈ K.faces)
    (w : E → ℝ) (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1)
    (hq : (∑ x ∈ F, w x • x) ∈ convexHull ℝ (T : Set E)) : F ⊆ T := by
  classical
  have hqF := sum_weights_mem_convexHull F (fun x hx => (hw x hx).le) hws
  have hqI := K.inter_subset_convexHull hF hT ⟨hqF,hq⟩
  have hs := positiveCombination_carrier (K.indep hF) Finset.inter_subset_left w hw hws
    (by simpa only [Finset.coe_inter] using hqI)
  exact hs.trans Finset.inter_subset_right
lemma eventually_coface_at_positivePoint (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {F : Finset E} (hF : F ∈ K.faces)
    (w : E → ℝ) (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1) :
    ∀ᶠ q in 𝓝 (∑ x ∈ F, w x • x),
      ∀ T ∈ K.faces, q ∈ convexHull ℝ (T : Set E) → F ⊆ T := by
  classical
  apply (hK.eventually_all).mpr
  intro T hT
  by_cases hFT : F ⊆ T
  · exact Filter.Eventually.of_forall (fun _ _ => hFT)
  · have hnot : (∑ x ∈ F, w x • x) ∉ convexHull ℝ (T : Set E) := by
      intro hq
      exact hFT (simplex_contains_positivePoint K hF hT w hw hws hq)
    have hc : IsClosed (convexHull ℝ (T : Set E)) := (T.finite_toSet.isCompact_convexHull ℝ).isClosed
    have he : ∀ᶠ q in 𝓝 (∑ x ∈ F, w x • x), q ∉ convexHull ℝ (T : Set E) :=
      hc.isOpen_compl.mem_nhds hnot
    exact he.mono (fun _ hq hh => False.elim (hq hh))
end
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem exists_facet_coface_on_side (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hconv : Convex ℝ K.space)
    {F : Finset E} (hF : F ∈ K.faces)
    (hdim : ∀ T ∈ K.faces, T.card ≤ F.card+1)
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    {v : E} (hv : v ∈ K.space) (hfv : b < f v) :
    ∃ u ∉ F, insert u F ∈ K.faces ∧ b < f u := by
  classical
  have hFn := K.nonempty_of_mem_faces hF
  let c : ℝ := (F.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr hFn.card_pos)
  have hcs : ∑ _x ∈ F, c = 1 := by
    simp [c,ne_of_gt (Nat.cast_pos.mpr hFn.card_pos : (0:ℝ) < F.card)]
  let q : E := ∑ x ∈ F, c • x
  have hqF : q ∈ convexHull ℝ (F : Set E) :=
    sum_weights_mem_convexHull F (fun _ _ => hc.le) hcs
  have hfq : f q = b := affineForm_eq_on_convexHull f b hFb hqF
  have hev := eventually_coface_at_positivePoint K hK hF (fun _ => c) (fun _ _ => hc) hcs
  have hcont : Continuous (fun δ : ℝ => δ • v + (1-δ) • q) := by fun_prop
  have hlim : Filter.Tendsto (fun δ : ℝ => δ • v + (1-δ) • q) (𝓝 0) (𝓝 q) := by
    simpa using hcont.continuousAt.tendsto (x := 0)
  have he := (hlim.eventually hev).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have hlt := (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ,hδ,hδ1,hδK⟩ := (hpos.and (hlt.and he)).exists
  have hδq : δ • v + (1-δ) • q ∈ K.space :=
    hconv hv (K.convexHull_subset_space hF hqF) hδ.le (sub_nonneg.mpr hδ1.le) (by ring)
  have hfδ : b < f (δ • v + (1-δ) • q) := by
    simp only [map_add,map_smul,smul_eq_mul,hfq]
    nlinarith [mul_pos hδ (sub_pos.mpr hfv)]
  obtain ⟨T,hT,hδT⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hδq
  have hFT := hδK T hT hδT
  have hne : F ≠ T := by
    intro heq
    subst T
    have heq := affineForm_eq_on_convexHull f b hFb hδT
    exact (ne_of_gt hfδ) heq
  have hcT : F.card+1 = T.card := by
    have hltc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hFT,hne⟩)
    have hh := hdim T hT
    omega
  obtain ⟨u,hu,rfl⟩ := Finset.exists_eq_insert_iff.mpr ⟨hFT,hcT⟩
  refine ⟨u,hu,hT,?_⟩
  by_contra hfu
  have hleft : convexHull ℝ ((insert u F : Finset E) : Set E) ⊆ {x | f x ≤ b} := by
    apply convexHull_min _ (convex_halfSpace_le f.isLinear b)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_of_not_gt hfu
    · exact (hFb x hx).le
  exact (not_le_of_gt hfδ) (hleft hδT)
end
section
open Set Finset
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma convexHull_inter_supporting (S : Set E) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hS : ∀ x ∈ S, f x ≤ b) :
    convexHull ℝ S ∩ {x | f x = b} = convexHull ℝ (S ∩ {x | f x = b}) := by
  let T := convexHull ℝ (S ∩ {x | f x = b})
  let C := {x : E | f x ≤ b ∧ (f x = b → x ∈ T)}
  have hSC : S ⊆ C := by
    intro x hx
    exact ⟨hS x hx, fun he => subset_convexHull ℝ _ ⟨hx, he⟩⟩
  have hC : Convex ℝ C := by
    intro x hx y hy u v hu hv huv
    change f (u • x + v • y) ≤ b ∧ (f (u • x + v • y) = b → _)
    simp only [map_add, map_smul, smul_eq_mul]
    have hew : u*b + v*b = b := by rw [← add_mul, huv, one_mul]
    have hux : 0 ≤ u*(b-f x) := mul_nonneg hu (sub_nonneg.mpr hx.1)
    have hvy : 0 ≤ v*(b-f y) := mul_nonneg hv (sub_nonneg.mpr hy.1)
    refine ⟨?_, ?_⟩
    · nlinarith only [hew, hux, hvy]
    · intro he
      by_cases hu0 : u = 0
      · have hv1 : v = 1 := by linarith
        have hyb : f y = b := by simpa [hu0, hv1] using he
        simpa [hu0, hv1] using hy.2 hyb
      by_cases hv0 : v = 0
      · have hu1 : u = 1 := by linarith
        have hxb : f x = b := by simpa [hv0, hu1] using he
        simpa [hv0, hu1] using hx.2 hxb
      have hux0 : u*(b-f x) = 0 := by nlinarith only [he, hew, hux, hvy]
      have hvy0 : v*(b-f y) = 0 := by nlinarith only [he, hew, hux, hvy]
      have hxb : f x = b := (sub_eq_zero.mp ((mul_eq_zero.mp hux0).resolve_left hu0)).symm
      have hyb : f y = b := (sub_eq_zero.mp ((mul_eq_zero.mp hvy0).resolve_left hv0)).symm
      exact (convex_convexHull ℝ _) (hx.2 hxb) (hy.2 hyb) hu hv huv
  apply subset_antisymm
  · intro x hx
    exact (convexHull_min hSC hC hx.1).2 hx.2
  · intro x hx
    refine ⟨convexHull_mono Set.inter_subset_left hx, ?_⟩
    have he : (S ∩ {x | f x = b}).EqOn f.toAffineMap (AffineMap.const ℝ E b) := fun _ hy => hy.2
    exact AffineMap.eqOn_affineSpan he (convexHull_subset_affineSpan _ hx)
end
open Set Finset
open scoped Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma full_face_affineSpan (K : Geometry.SimplicialComplex ℝ E) {S T : Finset E}
    (hspace : K.space ⊆ convexHull ℝ (S : Set E)) (hT : T ∈ K.faces)
    (hc : T.card = S.card) : affineSpan ℝ (T : Set E) = affineSpan ℝ (S : Set E) :=
  affineSpan_eq_of_card_eq (K.indep hT) ((subset_convexHull ℝ _).trans
    ((K.convexHull_subset_space hT).trans hspace)) hc
def facetApexes (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Finset E) : Finset E :=
  (hK.toFinset.biUnion id).filter (fun u => u ∉ F ∧ insert u F ∈ K.faces)
@[simp] lemma mem_facetApexes (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Finset E) (u : E) : u ∈ facetApexes K hK F ↔ u ∉ F ∧ insert u F ∈ K.faces := by
  simp only [facetApexes,Finset.mem_filter,Finset.mem_biUnion,Set.Finite.mem_toFinset,id_eq]
  exact ⟨fun h => h.2,fun h => ⟨⟨insert u F,h.2,Finset.mem_insert_self _ _⟩,h⟩⟩
lemma parent_card_bound (K : Geometry.SimplicialComplex ℝ E) {S : Finset E}
    (hspace : K.space ⊆ convexHull ℝ (S : Set E)) :
    ∀ T ∈ K.faces, T.card ≤ S.card := by
  intro T hT
  exact (K.indep hT).card_le_card_of_subset_affineSpan ((subset_convexHull ℝ _).trans
    ((K.convexHull_subset_space hT).trans (hspace.trans (convexHull_subset_affineSpan _))))
lemma facet_positive_apex_card (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {S F : Finset E}
    (hspace : K.space = convexHull ℝ (S : Set E)) (hF : F ∈ K.faces)
    (hc : F.card+1 = S.card) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hFb : ∀ x ∈ F, f x = b) :
    ((facetApexes K hK F).filter (fun u => b < f u)).card =
      if ∃ v ∈ S, b < f v then 1 else 0 := by
  let A := (facetApexes K hK F).filter (fun u => b < f u)
  have hAc : A.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨huA,hu⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvA,hv⟩ := Finset.mem_filter.mp hv
    obtain ⟨huF,huK⟩ := (mem_facetApexes K hK F u).mp huA
    obtain ⟨hvF,hvK⟩ := (mem_facetApexes K hK F v).mp hvA
    apply eq_of_facet_same_side K (K.nonempty_of_mem_faces hF) huF hvF huK hvK _ f b hFb hu hv
    rw [full_face_affineSpan K hspace.subset huK (by simp [Finset.card_insert_of_notMem huF,hc])]
    exact convexHull_subset_affineSpan _ (hspace ▸ K.convexHull_subset_space hvK
      (subset_convexHull ℝ _ (Finset.mem_insert_self _ _)))
  have hAn : A.Nonempty ↔ ∃ v ∈ S, b < f v := by
    constructor
    · rintro ⟨u,hu⟩
      obtain ⟨huA,hu⟩ := Finset.mem_filter.mp hu
      have huK := ((mem_facetApexes K hK F u).mp huA).2
      by_contra hn
      push Not at hn
      have hh : convexHull ℝ (S : Set E) ⊆ {x | f x ≤ b} :=
        convexHull_min hn (convex_halfSpace_le f.isLinear b)
      exact (not_le_of_gt hu) (hh (hspace ▸ K.convexHull_subset_space huK
        (subset_convexHull ℝ _ (Finset.mem_insert_self _ _))))
    · rintro ⟨v,hv,hfv⟩
      obtain ⟨u,hu,huK,hfu⟩ := exists_facet_coface_on_side K hK
        (hspace.symm ▸ convex_convexHull ℝ (S : Set E)) hF
        (fun T hT => hc ▸ parent_card_bound K hspace.subset T hT) f b hFb
        (hspace.symm ▸ subset_convexHull ℝ (S : Set E) hv) hfv
      exact ⟨u,Finset.mem_filter.mpr ⟨(mem_facetApexes K hK F u).mpr ⟨hu,huK⟩,hfu⟩⟩
  change A.card = _
  split_ifs with h
  · have := (hAn.mpr h).card_pos
    omega
  · have := not_congr hAn |>.mpr h
    simp only [Finset.not_nonempty_iff_eq_empty.mp this,Finset.card_empty]
end BassTrace.Sparse
end
end OAI
end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
open Set Finset
open scoped Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
noncomputable def vertexMean (s : Finset E) : E :=
  (s.card : ℝ)⁻¹ • ∑ x ∈ s, x
lemma vertexMean_mem_convexHull {s : Finset E} (hs : s.Nonempty) :
    vertexMean s ∈ convexHull ℝ (s : Set E) := by
  have h := s.centerMass_id_mem_convexHull (R := ℝ) (w := fun _ => 1)
    (fun _ _ => zero_le_one) (by simpa using (Nat.cast_pos.mpr hs.card_pos : (0 : ℝ) < s.card))
  simpa [Finset.centerMass, vertexMean] using h
lemma linear_vertexMean (f : E →ₗ[ℝ] ℝ) (s : Finset E) :
    f (vertexMean s) = (s.card : ℝ)⁻¹ * ∑ x ∈ s, f x := by
  simp [vertexMean]
lemma linear_vertexMean_eq_iff (f : E →ₗ[ℝ] ℝ) {s : Finset E} (hs : s.Nonempty)
    {b : ℝ} (hb : ∀ x ∈ s, f x ≤ b) :
    f (vertexMean s) = b ↔ ∀ x ∈ s, f x = b := by
  have hn : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  rw [linear_vertexMean]
  constructor
  · intro h
    have he : ∑ x ∈ s, f x = ∑ _x ∈ s, b := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      calc
        _ = (s.card : ℝ) * ((s.card : ℝ)⁻¹ * ∑ x ∈ s, f x) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn), one_mul]
        _ = _ := by rw [h]
    exact (Finset.sum_eq_sum_iff_of_le hb).mp he
  · intro h
    rw [Finset.sum_congr rfl h]
    simp [ne_of_gt hn]
lemma vertexMean_eq_centroid {s : Finset E} (hs : s.Nonempty) :
    vertexMean s = s.centroid ℝ id := by
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp only [Finset.centroidWeights_apply, id_eq]
  exact Finset.smul_sum
lemma vertexMean_map {F : Type*} [AddCommGroup F] [Module ℝ F]
    (f : E ≃ᵃ[ℝ] F) {s : Finset E} (hs : s.Nonempty) :
    vertexMean (s.map f.toEquiv.toEmbedding) = f (vertexMean s) := by
  rw [vertexMean_eq_centroid hs, vertexMean_eq_centroid hs.map, Finset.centroid_map]
  simp only [Finset.centroid_def]
  convert (s.map_affineCombination id (s.centroidWeights ℝ)
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs) f.toAffineMap).symm using 1 <;> rfl
def cell {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Set E :=
  {x | ∀ i, a i x ≤ b i}
lemma exists_ray_boundary {I : Type*} [Fintype I]
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) {c x : E}
    (hc : c ∈ cell a b) (hx : x ∈ cell a b)
    (hp : ∃ i, 0 < a i (x - c)) :
    ∃ (i : I) (t : ℝ), 1 ≤ t ∧
      c + t • (x - c) ∈ cell a b ∧
      a i (c + t • (x - c)) = b i ∧ a i c < b i ∧
      x ∈ segment ℝ c (c + t • (x - c)) := by
  classical
  let S : Finset I := Finset.univ.filter (fun i => 0 < a i (x - c))
  have hs : S.Nonempty := by
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image (fun i => (b i - a i c) / a i (x - c)) hs
  have hip : 0 < a i (x - c) := (Finset.mem_filter.mp hi).2
  let t := (b i - a i c) / a i (x - c)
  have ht : 1 ≤ t := by
    rw [le_div_iff₀ hip]
    simp only [one_mul, map_sub]
    linarith [hx i]
  have hteq : t * a i (x - c) = b i - a i c := by
    exact div_mul_cancel₀ _ (ne_of_gt hip)
  have hmem : c + t • (x - c) ∈ cell a b := by
    intro j
    simp only [map_add, map_smul, smul_eq_mul]
    by_cases hj : 0 < a j (x - c)
    · have hbound : t ≤ (b j - a j c) / a j (x - c) :=
        hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      have hmul := (le_div_iff₀ hj).mp hbound
      linarith
    · have hmul : t * a j (x - c) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_not_gt hj)
      linarith [hc j]
  refine ⟨i, t, ht, hmem, ?_, ?_, ?_⟩
  · simp only [map_add, map_smul, smul_eq_mul]
    linarith
  · have : 0 < a i x - a i c := by simpa using hip
    linarith [hx i]
  · have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    refine ⟨1 - t⁻¹, t⁻¹, ?_, inv_nonneg.mpr ht0.le, by ring, ?_⟩
    · have := inv_le_one_of_one_le₀ ht
      linarith
    · simp only [smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt ht0), one_smul,
        sub_smul, one_smul, smul_sub]
      module
section BoundedRay
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma bounded_cell_positive_direction {I : Type*}
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (hbounded : Bornology.IsBounded (cell a b))
    {c v : V} (hc : c ∈ cell a b) (hv : v ≠ 0) : ∃ i, 0 < a i v := by
  by_contra! h
  obtain ⟨R, hR⟩ := hbounded.exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg c).trans (hR c hc)
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let t : ℝ := (R + ‖c‖ + 1) / ‖v‖
  have ht : 0 < t := div_pos (by positivity) hv0
  have hmem : c + t • v ∈ cell a b := by
    intro i
    simp only [map_add, map_smul, smul_eq_mul]
    have := mul_nonpos_of_nonneg_of_nonpos ht.le (h i)
    linarith [hc i]
  have hn : ‖t • v‖ ≤ R + ‖c‖ := by
    calc
      ‖t • v‖ = ‖(c + t • v) - c‖ := by congr 1; abel
      _ ≤ ‖c + t • v‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ R + ‖c‖ := add_le_add (hR _ hmem) le_rfl
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hn
  have hteq : t * ‖v‖ = R + ‖c‖ + 1 := div_mul_cancel₀ _ (ne_of_gt hv0)
  linarith
lemma bounded_exists_ray_boundary {I : Type*} [Fintype I]
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (hbounded : Bornology.IsBounded (cell a b))
    {c x : V} (hc : c ∈ cell a b) (hx : x ∈ cell a b) (hxc : x ≠ c) :
    ∃ (i : I) (t : ℝ), 1 ≤ t ∧
      c + t • (x - c) ∈ cell a b ∧
      a i (c + t • (x - c)) = b i ∧ a i c < b i ∧
      x ∈ segment ℝ c (c + t • (x - c)) :=
  exists_ray_boundary a b hc hx
    (bounded_cell_positive_direction a b hbounded hc (sub_ne_zero.mpr hxc))
end BoundedRay
lemma boundary_ray_unique {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) {c y z : E}
    (hy : y ∈ cell a b) (hz : z ∈ cell a b)
    (hyi : ∃ i, a i y = b i ∧ a i c < b i)
    (hzi : ∃ i, a i z = b i ∧ a i c < b i)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (he : t • (y - c) = u • (z - c)) : t = u ∧ y = z := by
  obtain ⟨i, hiy, hic⟩ := hyi
  obtain ⟨j, hjz, hjc⟩ := hzi
  have he1 := congrArg (a i) he
  have he2 := congrArg (a j) he
  simp only [map_smul, map_sub, smul_eq_mul, hiy] at he1
  simp only [map_smul, map_sub, smul_eq_mul, hjz] at he2
  have htu : t ≤ u := by
    have hi := hz i
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hi (a i c)) hu.le
    nlinarith
  have hut : u ≤ t := by
    have hj := hy j
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hj (a j c)) ht.le
    nlinarith
  have h : t = u := le_antisymm htu hut
  refine ⟨h, ?_⟩
  rw [← h] at he
  have hdiff : y - c = z - c := by
    have hh := congrArg ((t⁻¹ : ℝ) • ·) he
    simpa [smul_smul, ne_of_gt ht] using hh
  exact sub_left_injective hdiff
lemma linear_eq_on_affineSpan (f : E →ₗ[ℝ] ℝ) {S : Set E} {b : ℝ}
    (hS : ∀ x ∈ S, f x = b) {x : E} (hx : x ∈ affineSpan ℝ S) : f x = b := by
  refine affineSpan_induction hx hS ?_
  intro t u v w hu hv hw
  simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, hu, hv, hw,
    sub_self, smul_zero, zero_add]
lemma convexHull_inter_supporting (S : Set E) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hS : ∀ x ∈ S, f x ≤ b) :
    convexHull ℝ S ∩ {x | f x = b} = convexHull ℝ (S ∩ {x | f x = b}) := by
  let T := convexHull ℝ (S ∩ {x | f x = b})
  let C := {x : E | f x ≤ b ∧ (f x = b → x ∈ T)}
  have hSC : S ⊆ C := by
    intro x hx
    exact ⟨hS x hx, fun he => subset_convexHull ℝ _ ⟨hx, he⟩⟩
  have hC : Convex ℝ C := by
    intro x hx y hy u v hu hv huv
    change f (u • x + v • y) ≤ b ∧ (f (u • x + v • y) = b → _)
    simp only [map_add, map_smul, smul_eq_mul]
    have hew : u*b + v*b = b := by rw [← add_mul, huv, one_mul]
    have hux : 0 ≤ u*(b-f x) := mul_nonneg hu (sub_nonneg.mpr hx.1)
    have hvy : 0 ≤ v*(b-f y) := mul_nonneg hv (sub_nonneg.mpr hy.1)
    refine ⟨?_, ?_⟩
    · nlinarith only [hew, hux, hvy]
    · intro he
      by_cases hu0 : u = 0
      · have hv1 : v = 1 := by linarith
        have hyb : f y = b := by simpa [hu0, hv1] using he
        simpa [hu0, hv1] using hy.2 hyb
      by_cases hv0 : v = 0
      · have hu1 : u = 1 := by linarith
        have hxb : f x = b := by simpa [hv0, hu1] using he
        simpa [hv0, hu1] using hx.2 hxb
      have hux0 : u*(b-f x) = 0 := by nlinarith only [he, hew, hux, hvy]
      have hvy0 : v*(b-f y) = 0 := by nlinarith only [he, hew, hux, hvy]
      have hxb : f x = b := (sub_eq_zero.mp ((mul_eq_zero.mp hux0).resolve_left hu0)).symm
      have hyb : f y = b := (sub_eq_zero.mp ((mul_eq_zero.mp hvy0).resolve_left hv0)).symm
      exact (convex_convexHull ℝ _) (hx.2 hxb) (hy.2 hyb) hu hv huv
  apply subset_antisymm
  · intro x hx
    exact (convexHull_min hSC hC hx.1).2 hx.2
  · intro x hx
    refine ⟨convexHull_mono Set.inter_subset_left hx, ?_⟩
    exact linear_eq_on_affineSpan f (fun _ hy => hy.2)
      (convexHull_subset_affineSpan _ hx)
lemma exists_positive_ray_of_mem_convexHull_insert {S : Set E} {c x : E}
    (hx : x ∈ convexHull ℝ (insert c S)) (hxc : x ≠ c) :
    ∃ y ∈ convexHull ℝ S, ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      x = c + t • (y-c) ∧ x ∈ segment ℝ c y := by
  have hS : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h] at hx
    have : x = c := by simpa using hx
    exact hxc this
  rw [convexHull_insert hS, convexJoin_singleton_left] at hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
  have hseg := hxy
  obtain ⟨u, t, hu, ht, hut, he⟩ := hxy
  have ht0 : t ≠ 0 := by
    intro ht0
    have hu1 : u = 1 := by linarith
    apply hxc
    simpa [ht0, hu1] using he.symm
  refine ⟨y, hy, t, lt_of_le_of_ne ht (Ne.symm ht0), by linarith, ?_, hseg⟩
  rw [← he, show u = 1-t by linarith, sub_smul, one_smul, smul_sub]
  abel
def radialBoundary {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (c : E) : Set E :=
  {y | y ∈ cell a b ∧ ∃ i, a i y = b i ∧ a i c < b i}
lemma center_notMem_radialBoundary {I : Type*} (a : I → E →ₗ[ℝ] ℝ)
    (b : I → ℝ) (c : E) : c ∉ radialBoundary a b c := by
  rintro ⟨_, i, he, hi⟩
  exact (ne_of_lt hi) he
lemma cone_hull_inter {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    {c : E} {S T : Set E}
    (hS : convexHull ℝ S ⊆ radialBoundary a b c)
    (hT : convexHull ℝ T ⊆ radialBoundary a b c)
    (hST : convexHull ℝ S ∩ convexHull ℝ T ⊆ convexHull ℝ (S ∩ T)) :
    convexHull ℝ (insert c S) ∩ convexHull ℝ (insert c T) =
      convexHull ℝ (insert c (S ∩ T)) := by
  apply subset_antisymm
  · intro x hx
    by_cases hxc : x = c
    · subst x
      exact subset_convexHull ℝ _ (Set.mem_insert c _)
    obtain ⟨y, hy, t, ht, _, hxy, hseg⟩ :=
      exists_positive_ray_of_mem_convexHull_insert hx.1 hxc
    obtain ⟨z, hz, u, hu, _, hxz, _⟩ :=
      exists_positive_ray_of_mem_convexHull_insert hx.2 hxc
    have hray : t • (y-c) = u • (z-c) := by
      exact add_left_cancel (hxy.symm.trans hxz)
    have hyz := (boundary_ray_unique a b (hS hy).1 (hT hz).1
      (hS hy).2 (hT hz).2 ht hu hray).2
    have hyST : y ∈ convexHull ℝ (S ∩ T) := hST ⟨hy, hyz ▸ hz⟩
    exact (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (Set.mem_insert c _))
      (convexHull_mono (Set.subset_insert c _) hyST) hseg
  · exact Set.subset_inter
      (convexHull_mono (Set.insert_subset_insert Set.inter_subset_left))
      (convexHull_mono (Set.insert_subset_insert Set.inter_subset_right))
lemma cone_hull_inter_boundary {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    {c : E} {S T : Set E}
    (hS : convexHull ℝ S ⊆ radialBoundary a b c)
    (hT : convexHull ℝ T ⊆ radialBoundary a b c)
    (hST : convexHull ℝ S ∩ convexHull ℝ T ⊆ convexHull ℝ (S ∩ T)) :
    convexHull ℝ (insert c S) ∩ convexHull ℝ T = convexHull ℝ (S ∩ T) := by
  apply subset_antisymm
  · intro x hx
    have hxc : x ≠ c := by
      intro hh
      exact center_notMem_radialBoundary a b c (hh ▸ hT hx.2)
    obtain ⟨y, hy, t, ht, _, hxy, _⟩ :=
      exists_positive_ray_of_mem_convexHull_insert hx.1 hxc
    have hray : t • (y-c) = (1 : ℝ) • (x-c) := by
      rw [one_smul, hxy]
      abel
    have hyx := (boundary_ray_unique a b (hS hy).1 (hT hx.2).1
      (hS hy).2 (hT hx.2).2 ht zero_lt_one hray).2
    exact hST ⟨hyx ▸ hy, hx.2⟩
  · exact Set.subset_inter
      (convexHull_mono (Set.inter_subset_left.trans (Set.subset_insert c S)))
      (convexHull_mono Set.inter_subset_right)
lemma affineIndependent_insert {S : Set E} {c : E}
    (hS : AffineIndependent ℝ ((↑) : S → E)) (hc : c ∉ affineSpan ℝ S) :
    AffineIndependent ℝ (fun x : (insert c S : Set E) => (x : E)) := by
  let i : (insert c S : Set E) := ⟨c, Set.mem_insert c S⟩
  let f : {j : (insert c S : Set E) // j ≠ i} → S := fun j =>
    ⟨j.val.val, by
      rcases j.val.property with he | hm
      · exact False.elim (j.property (Subtype.ext he))
      · exact hm⟩
  have hf : Function.Injective f := by
    intro j k hjk
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S => (z : E)) hjk
  have hi : AffineIndependent ℝ (fun j : {j : (insert c S : Set E) // j ≠ i} =>
      (j.val : E)) := hS.comp_embedding ⟨f, hf⟩
  apply hi.affineIndependent_of_notMem_span
  intro hmem
  apply hc
  apply affineSpan_mono ℝ (s₁ := (fun x : (insert c S : Set E) => (x : E)) '' {j | j ≠ i})
    (s₂ := S) ?_ hmem
  rintro x ⟨j, hj, rfl⟩
  exact (f ⟨j, hj⟩).property
variable [DecidableEq E]
def coneFaces (B : Geometry.SimplicialComplex ℝ E) (c : E) : Set (Finset E) :=
  {{c}} ∪ B.faces ∪ (fun s => insert c s) '' B.faces
lemma mem_coneFaces_iff (B : Geometry.SimplicialComplex ℝ E) (c : E) (s : Finset E) :
    s ∈ coneFaces B c ↔ s = {c} ∨ s ∈ B.faces ∨ ∃ t ∈ B.faces, s = insert c t := by
  simp only [coneFaces, Set.mem_union, Set.mem_singleton_iff, Set.mem_image]
  aesop
lemma coneFaces_down_closed (B : Geometry.SimplicialComplex ℝ E) (c : E) :
    IsRelLowerSet (coneFaces B c) Finset.Nonempty := by
  intro s hs
  rw [mem_coneFaces_iff] at hs
  have hpos : s.Nonempty := by
    rcases hs with rfl | hs | ⟨t, _, rfl⟩
    · exact Finset.singleton_nonempty _
    · exact B.nonempty_of_mem_faces hs
    · exact Finset.insert_nonempty _ _
  refine ⟨hpos, ?_⟩
  intro t hts ht
  rw [mem_coneFaces_iff]
  rcases hs with rfl | hs | ⟨u, hu, rfl⟩
  · left
    exact Finset.Subset.antisymm hts (Finset.singleton_subset_iff.mpr
      (by obtain ⟨x, hx⟩ := ht; simpa only [Finset.mem_singleton.mp (hts hx)] using hx))
  · exact Or.inr (Or.inl (B.down_closed hs hts ht))
  · by_cases hct : c ∈ t
    · by_cases he : t.erase c = ∅
      · exact Or.inl ((Finset.erase_eq_empty_iff t c).mp he |>.resolve_left ht.ne_empty)
      · right; right
        refine ⟨t.erase c, B.down_closed hu ?_ (Finset.nonempty_iff_ne_empty.mpr he),
          (Finset.insert_erase hct).symm⟩
        intro x hx
        exact (Finset.mem_insert.mp (hts (Finset.mem_of_mem_erase hx))).resolve_left
          (Finset.ne_of_mem_erase hx)
    · right; left
      apply B.down_closed hu _ ht
      intro x hx
      rcases Finset.mem_insert.mp (hts hx) with rfl | hu'
      · exact False.elim (hct hx)
      · exact hu'
lemma center_mem_hull_coneFace_iff {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c) {s : Finset E} (hs : s ∈ coneFaces B c) :
    c ∈ convexHull ℝ (s : Set E) ↔ c ∈ s := by
  constructor
  · intro hc
    rcases (mem_coneFaces_iff B c s).mp hs with rfl | hs | ⟨t, _, rfl⟩
    · exact Finset.mem_singleton_self _
    · exact False.elim (center_notMem_radialBoundary a b c
        (hB (B.convexHull_subset_space hs hc)))
    · exact Finset.mem_insert_self _ _
  · intro hc
    exact subset_convexHull ℝ (s : Set E) hc
lemma coneFaces_inter_subset {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    {s t : Finset E} (hs : s ∈ coneFaces B c) (ht : t ∈ coneFaces B c) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
  intro x hx
  by_cases hxc : x = c
  · subst x
    exact subset_convexHull ℝ _
      ⟨(center_mem_hull_coneFace_iff a b B c hB hs).mp hx.1,
       (center_mem_hull_coneFace_iff a b B c hB ht).mp hx.2⟩
  have hnotS : s ≠ {c} := by
    intro hh
    apply hxc
    simpa [hh] using hx.1
  have hnotT : t ≠ {c} := by
    intro hh
    apply hxc
    simpa [hh] using hx.2
  have hs' := ((mem_coneFaces_iff B c s).mp hs).resolve_left hnotS
  have ht' := ((mem_coneFaces_iff B c t).mp ht).resolve_left hnotT
  have hcone (u v : Finset E) (hu : u ∈ B.faces) (hv : v ∈ B.faces) :=
    cone_hull_inter a b (B.convexHull_subset_space hu |>.trans hB)
      (B.convexHull_subset_space hv |>.trans hB) (B.inter_subset_convexHull hu hv)
  have hmixed (u v : Finset E) (hu : u ∈ B.faces) (hv : v ∈ B.faces) :=
    cone_hull_inter_boundary a b (B.convexHull_subset_space hu |>.trans hB)
      (B.convexHull_subset_space hv |>.trans hB) (B.inter_subset_convexHull hu hv)
  rcases hs' with hs | ⟨u, hu, rfl⟩ <;> rcases ht' with ht | ⟨v, hv, rfl⟩
  · exact B.inter_subset_convexHull hs ht hx
  · have hh : x ∈ convexHull ℝ ((v : Set E) ∩ s) := by
      rw [← hmixed v s hv hs]
      exact ⟨by simpa only [Finset.coe_insert] using hx.2, hx.1⟩
    exact convexHull_mono (by intro y hy; exact ⟨hy.2, Finset.mem_insert_of_mem hy.1⟩) hh
  · have hh : x ∈ convexHull ℝ ((u : Set E) ∩ t) := by
      rw [← hmixed u t hu ht]
      exact ⟨by simpa only [Finset.coe_insert] using hx.1, hx.2⟩
    exact convexHull_mono (by intro y hy; exact ⟨Finset.mem_insert_of_mem hy.1, hy.2⟩) hh
  · have hh : x ∈ convexHull ℝ (insert c ((u : Set E) ∩ v)) := by
      rw [← hcone u v hu hv]
      simpa only [Finset.coe_insert] using hx
    apply convexHull_mono _ hh
    intro y hy
    rcases hy with rfl | hy
    · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
    · exact ⟨Finset.mem_insert_of_mem hy.1, Finset.mem_insert_of_mem hy.2⟩
def coneComplex {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    (hspan : ∀ s ∈ B.faces, c ∉ affineSpan ℝ (s : Set E)) :
    Geometry.SimplicialComplex ℝ E where
  faces := coneFaces B c
  isRelLowerSet_faces := coneFaces_down_closed B c
  indep := by
    intro s hs
    rcases (mem_coneFaces_iff B c s).mp hs with rfl | hs | ⟨t, ht, rfl⟩
    · exact affineIndependent_of_subsingleton ℝ _
    · exact B.indep hs
    · have hh := affineIndependent_insert (B.indep ht) (hspan t ht)
      rw [← Finset.coe_insert] at hh
      exact hh
  inter_subset_convexHull := coneFaces_inter_subset a b B c hB
lemma coneComplex_finite {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    (hspan : ∀ s ∈ B.faces, c ∉ affineSpan ℝ (s : Set E))
    (hfinite : B.faces.Finite) : (coneComplex a b B c hB hspan).faces.Finite := by
  exact ((Set.finite_singleton _).union hfinite).union (hfinite.image _)
omit [DecidableEq E] in
lemma center_notMem_affineSpan_boundaryFace {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    {s : Finset E} (hs : s ∈ B.faces) : c ∉ affineSpan ℝ (s : Set E) := by
  have hn := B.nonempty_of_mem_faces hs
  obtain ⟨_, i, hi, hic⟩ := hB (B.convexHull_subset_space hs
    (vertexMean_mem_convexHull hn))
  have hle : ∀ x ∈ s, a i x ≤ b i := fun x hx =>
    (hB (B.subset_space hs hx)).1 i
  have he := (linear_vertexMean_eq_iff (a i) hn hle).mp hi
  intro hc
  exact (ne_of_lt hic) (linear_eq_on_affineSpan (a i) he hc)
lemma mem_coneComplex_space_iff {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    (hspan : ∀ s ∈ B.faces, c ∉ affineSpan ℝ (s : Set E)) (x : E) :
    x ∈ (coneComplex a b B c hB hspan).space ↔
      x = c ∨ ∃ y ∈ B.space, x ∈ segment ℝ c y := by
  classical
  constructor
  · intro hx
    by_cases hxc : x = c
    · exact Or.inl hxc
    right
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    rcases (mem_coneFaces_iff B c s).mp hs with rfl | hs | ⟨t, ht, rfl⟩
    · exact (hxc (by simpa using hx)).elim
    · exact ⟨x, B.convexHull_subset_space hs hx, right_mem_segment _ _ _⟩
    · obtain ⟨y, hy, _, _, _, _, hxy⟩ :=
        exists_positive_ray_of_mem_convexHull_insert (by simpa using hx) hxc
      exact ⟨y, B.convexHull_subset_space ht hy, hxy⟩
  · intro hh
    rcases hh with hxc | ⟨y, hy, hx⟩
    · subst x
      apply Geometry.SimplicialComplex.mem_space_iff.mpr
      exact ⟨{c}, (mem_coneFaces_iff B c {c}).mpr (Or.inl rfl), by simp⟩
    · obtain ⟨s, hs, hy⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hy
      apply Geometry.SimplicialComplex.mem_space_iff.mpr
      refine ⟨insert c s, (mem_coneFaces_iff B c _).mpr (Or.inr (Or.inr ⟨s, hs, rfl⟩)), ?_⟩
      apply (convex_convexHull ℝ (insert c s : Finset E)).segment_subset _ _ hx
      · exact subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
      · exact convexHull_mono (by intro z hz; exact Finset.mem_insert_of_mem hz) hy
omit [DecidableEq E] in
lemma convex_cell {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    Convex ℝ (cell a b) := by
  intro x hx y hy r s hr hs hrs i
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    r * a i x + s * a i y ≤ r * b i + s * b i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) hr)
        (mul_le_mul_of_nonneg_left (hy i) hs)
    _ = b i := by rw [← add_mul, hrs, one_mul]
lemma coneComplex_space_eq_cell {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [DecidableEq V]
    {I : Type*} [Fintype I] (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hbounded : Bornology.IsBounded (cell a b))
    (B : Geometry.SimplicialComplex ℝ V) (c : V) (hc : c ∈ cell a b)
    (hB : B.space = radialBoundary a b c) :
    (coneComplex a b B c hB.subset
      (fun _ hs => center_notMem_affineSpan_boundaryFace a b B c hB.subset hs)).space
      = cell a b := by
  ext x
  rw [mem_coneComplex_space_iff]
  constructor
  · rintro (rfl | ⟨y, hy, hx⟩)
    · exact hc
    · exact (convex_cell a b).segment_subset hc (hB.subset hy).1 hx
  · intro hx
    by_cases hxc : x = c
    · exact Or.inl hxc
    obtain ⟨i, t, _, hy, hi, hic, hxy⟩ :=
      bounded_exists_ray_boundary a b hbounded hc hx hxc
    exact Or.inr ⟨c + t • (x-c), hB.symm.subset ⟨hy, i, hi, hic⟩, hxy⟩
end BassTrace.Sparse.Cuts
end OAI
end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
open Set Finset
open scoped Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
section Restriction
def restrictComplex (B : Geometry.SimplicialComplex ℝ E) (P : Set E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | s ∈ B.faces ∧ (s : Set E) ⊆ P}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨B.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨B.down_closed hs.1 hts ht, fun _ hx => hs.2 (hts hx)⟩
  indep hs := B.indep hs.1
  inter_subset_convexHull hs ht := B.inter_subset_convexHull hs.1 ht.1
lemma restrictComplex_finite (B : Geometry.SimplicialComplex ℝ E) (P : Set E)
    (hB : B.faces.Finite) : (restrictComplex B P).faces.Finite :=
  hB.subset (fun _ hs => hs.1)
def glueComplex (B C : Geometry.SimplicialComplex ℝ E)
    (hcross : ∀ s ∈ B.faces, ∀ t ∈ C.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) :
    Geometry.SimplicialComplex ℝ E where
  faces := B.faces ∪ C.faces
  isRelLowerSet_faces := by
    intro s hs
    rcases hs with hs | hs
    · exact ⟨B.nonempty_of_mem_faces hs, fun _ ht hn => Or.inl (B.down_closed hs ht hn)⟩
    · exact ⟨C.nonempty_of_mem_faces hs, fun _ ht hn => Or.inr (C.down_closed hs ht hn)⟩
  indep := by
    intro s hs
    exact hs.elim B.indep C.indep
  inter_subset_convexHull := by
    intro s t hs ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact B.inter_subset_convexHull hs ht
    · exact hcross s hs t ht
    · simpa only [Set.inter_comm] using hcross t ht s hs
    · exact C.inter_subset_convexHull hs ht
lemma glueComplex_finite (B C : Geometry.SimplicialComplex ℝ E)
    (hcross : ∀ s ∈ B.faces, ∀ t ∈ C.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)))
    (hB : B.faces.Finite) (hC : C.faces.Finite) :
    (glueComplex B C hcross).faces.Finite := hB.union hC
lemma glueComplex_space (B C : Geometry.SimplicialComplex ℝ E)
    (hcross : ∀ s ∈ B.faces, ∀ t ∈ C.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E))) :
    (glueComplex B C hcross).space = B.space ∪ C.space := by
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff, Set.mem_union,
    show (glueComplex B C hcross).faces = B.faces ∪ C.faces from rfl]
  aesop
end Restriction
section Trace
def RespectsSet (B : Geometry.SimplicialComplex ℝ E) (P : Set E) : Prop :=
  ∀ s ∈ B.faces, convexHull ℝ (s : Set E) ∩ P = convexHull ℝ ((s : Set E) ∩ P)
lemma restrictComplex_space_of_respects (B : Geometry.SimplicialComplex ℝ E)
    (P : Set E) (h : RespectsSet B P) :
    (restrictComplex B P).space = B.space ∩ P := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    refine ⟨B.convexHull_subset_space hs.1 hx, ?_⟩
    have he : (s : Set E) ∩ P = s := Set.inter_eq_left.mpr hs.2
    have hx' : x ∈ convexHull ℝ (s : Set E) ∩ P := by
      rw [h s hs.1, he]
      exact hx
    exact hx'.2
  · rintro ⟨hx, hxP⟩
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    let t := s.filter (· ∈ P)
    have ht : (t : Set E) = (s : Set E) ∩ P := by ext; simp [t]
    have hxt : x ∈ convexHull ℝ (t : Set E) := by
      rw [ht, ← h s hs]
      exact ⟨hx, hxP⟩
    have hne : t.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxt⟩)
    refine Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨t, ⟨B.down_closed hs (Finset.filter_subset _ _) hne, ?_⟩, hxt⟩
    intro y hy
    exact (Finset.mem_filter.mp hy).2
lemma hull_inter_of_supporting_eq (s : Finset E) (P Q : Set E)
    (hsP : convexHull ℝ (s : Set E) ⊆ P) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hf : ∀ x ∈ P, f x ≤ b) (hface : P ∩ Q = P ∩ {x | f x = b}) :
    convexHull ℝ (s : Set E) ∩ Q = convexHull ℝ ((s : Set E) ∩ Q) := by
  have hiff (x : E) (hx : x ∈ P) : x ∈ Q ↔ f x = b := by
    constructor
    · intro hq
      exact (hface.subset ⟨hx, hq⟩).2
    · intro he
      exact (hface.symm.subset ⟨hx, he⟩).2
  calc
    _ = convexHull ℝ (s : Set E) ∩ {x | f x = b} := by
      ext x
      exact and_congr_right (fun hx => hiff x (hsP hx))
    _ = convexHull ℝ ((s : Set E) ∩ {x | f x = b}) :=
      convexHull_inter_supporting _ f b (fun x hx => hf x (hsP (subset_convexHull _ _ hx)))
    _ = _ := by
      congr 1
      ext x
      exact and_congr_right (fun hx => (hiff x (hsP (subset_convexHull _ _ hx))).symm)
lemma respectsSet_of_supporting_eq (B : Geometry.SimplicialComplex ℝ E)
    (P Q : Set E) (hBP : B.space ⊆ P) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hf : ∀ x ∈ P, f x ≤ b) (hface : P ∩ Q = P ∩ {x | f x = b}) :
    RespectsSet B Q := by
  intro s hs
  exact hull_inter_of_supporting_eq s P Q ((B.convexHull_subset_space hs).trans hBP)
    f b hf hface
lemma cross_inter_of_respects (B C : Geometry.SimplicialComplex ℝ E)
    (P : Set E) (hB : RespectsSet B P) (hC : C.space ⊆ P)
    (hcommon : restrictComplex B P ≤ C)
    {s t : Finset E} (hs : s ∈ B.faces) (ht : t ∈ C.faces) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
  classical
  intro x hx
  let u := s.filter (· ∈ P)
  have hu : (u : Set E) = (s : Set E) ∩ P := by ext; simp [u]
  have hxu : x ∈ convexHull ℝ (u : Set E) := by
    rw [hu, ← hB s hs]
    exact ⟨hx.1, hC (C.convexHull_subset_space ht hx.2)⟩
  have hne : u.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxu⟩)
  have huB : u ∈ (restrictComplex B P).faces :=
    ⟨B.down_closed hs (Finset.filter_subset _ _) hne,
      fun _ hy => (Finset.mem_filter.mp hy).2⟩
  have hi := C.inter_subset_convexHull (hcommon huB) ht ⟨hxu, hx.2⟩
  apply convexHull_mono _ hi
  intro y hy
  exact ⟨(Finset.mem_filter.mp hy.1).1, hy.2⟩
end Trace
section GeneralBoundary
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma mem_radialBoundary_of_supporting {I : Type*} [Fintype I]
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (hbounded : Bornology.IsBounded (cell a b))
    {c x : V} (hc : c ∈ cell a b) (hx : x ∈ cell a b)
    (f : V →ₗ[ℝ] ℝ) (d : ℝ) (hf : ∀ y ∈ cell a b, f y ≤ d)
    (hfc : f c < d) (hfx : f x = d) : x ∈ radialBoundary a b c := by
  have hxc : x ≠ c := by intro he; subst x; exact (ne_of_lt hfc) hfx
  obtain ⟨i, t, ht, hy, hi, hic, _⟩ := bounded_exists_ray_boundary a b hbounded hc hx hxc
  have hfy := hf _ hy
  simp only [map_add, map_smul, map_sub, smul_eq_mul, hfx] at hfy
  have ht1 : t = 1 := by nlinarith
  subst t
  simp only [one_smul, add_sub_cancel] at hi
  exact ⟨hx, i, hi, hic⟩
end GeneralBoundary
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
def SupportingFace (Q P : Set V) : Prop :=
  ∃ (f : V →ₗ[ℝ] ℝ) (b : ℝ), (∀ x ∈ P, f x ≤ b) ∧
    Q = P ∩ {x | f x = b}
lemma SupportingFace.subset {Q P : Set V} (h : SupportingFace Q P) : Q ⊆ P := by
  obtain ⟨f, b, _, rfl⟩ := h
  exact Set.inter_subset_left
lemma supportingFace_self (P : Set V) : SupportingFace P P := by
  refine ⟨0, 0, by simp, ?_⟩
  simp
lemma linear_le_on_convexHull (s : Set V) (f : V →ₗ[ℝ] ℝ) (b : ℝ)
    (hf : ∀ x ∈ s, f x ≤ b) : ∀ x ∈ convexHull ℝ s, f x ≤ b := by
  intro x hx
  apply convexHull_min (s := s) (t := {y | f y ≤ b}) hf _ hx
  intro y hy z hz u v hu hv huv
  simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at *
  calc
    u * f y + v * f z ≤ u * b + v * b :=
      add_le_add (mul_le_mul_of_nonneg_left hy hu) (mul_le_mul_of_nonneg_left hz hv)
    _ = b := by rw [← add_mul, huv, one_mul]
lemma SupportingFace.trans_finite_hull {s : Finset V} {Q R : Set V}
    (hQ : SupportingFace Q (convexHull ℝ (s : Set V)))
    (hR : SupportingFace R Q) : SupportingFace R (convexHull ℝ (s : Set V)) := by
  classical
  obtain ⟨f, b, hf, hQ⟩ := hQ
  obtain ⟨g, d, hg, hR⟩ := hR
  have hfv (x : V) (hx : x ∈ s) : f x ≤ b := hf x (subset_convexHull ℝ _ hx)
  have hgv (x : V) (hx : x ∈ s) (he : f x = b) : g x ≤ d := by
    apply hg
    rw [hQ]
    exact ⟨subset_convexHull ℝ _ hx, he⟩
  let M : ℝ := 1 + ∑ x ∈ s, |g x - d| / (b - f x)
  let k : V →ₗ[ℝ] ℝ := M • f + g
  have hk (x : V) : k x = M * f x + g x := by simp [k]
  have hstrict (x : V) (hx : x ∈ s) (he : f x ≠ b) : k x < M*b+d := by
    have hb : 0 < b - f x := sub_pos.mpr (lt_of_le_of_ne (hfv x hx) he)
    have hterm : |g x-d| / (b-f x) ≤ ∑ y ∈ s, |g y-d| / (b-f y) :=
      Finset.single_le_sum (fun y hy => div_nonneg (abs_nonneg (g y-d)) (sub_nonneg.mpr (hfv y hy))) hx
    have hratio : |g x-d| / (b-f x) < M := by dsimp [M]; linarith
    have hm := (div_lt_iff₀ hb).mp hratio
    rw [hk]
    have hab := le_abs_self (g x-d)
    nlinarith only [hm, hab]
  have hkv (x : V) (hx : x ∈ s) : k x ≤ M*b+d := by
    by_cases he : f x = b
    · rw [hk, he]
      linarith [hgv x hx he]
    · exact (hstrict x hx he).le
  have hkeq (x : V) (hx : x ∈ s) :
      k x = M*b+d ↔ f x = b ∧ g x = d := by
    by_cases he : f x = b
    · rw [hk, he]
      constructor
      · intro hh; exact ⟨rfl, by linarith⟩
      · rintro ⟨_, rfl⟩; rfl
    · exact iff_of_false (ne_of_lt (hstrict x hx he)) (fun hh => he hh.1)
  refine ⟨k, M*b+d, linear_le_on_convexHull _ k _ hkv, ?_⟩
  have hvQ : Q = convexHull ℝ ((s : Set V) ∩ {x | f x = b}) := by
    rw [hQ, convexHull_inter_supporting _ f b hfv]
  calc
    R = convexHull ℝ ((s : Set V) ∩ {x | f x = b}) ∩ {x | g x = d} := by rw [hR, hvQ]
    _ = convexHull ℝ (((s : Set V) ∩ {x | f x = b}) ∩ {x | g x = d}) :=
      convexHull_inter_supporting _ g d (fun x hx => hgv x hx.1 hx.2)
    _ = convexHull ℝ ((s : Set V) ∩ {x | k x = M*b+d}) := by
      congr 1
      ext x
      constructor
      · rintro ⟨⟨hx, hfx⟩, hgx⟩
        exact ⟨hx, (hkeq x hx).mpr ⟨hfx, hgx⟩⟩
      · rintro ⟨hx, hkx⟩
        exact ⟨⟨hx, ((hkeq x hx).mp hkx).1⟩, ((hkeq x hx).mp hkx).2⟩
    _ = convexHull ℝ (s : Set V) ∩ {x | k x = M*b+d} :=
      (convexHull_inter_supporting _ k _ hkv).symm
lemma SupportingFace.restrict {Q P S : Set V} (h : SupportingFace Q P)
    (hSP : S ⊆ P) : SupportingFace (S ∩ Q) S := by
  obtain ⟨f, b, hf, hQ⟩ := h
  refine ⟨f, b, fun x hx => hf x (hSP hx), ?_⟩
  ext x
  rw [hQ]
  exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hSP hx.1, hx.2⟩⟩
lemma SupportingFace.supporting_inter {Q S P : Set V}
    (hQ : SupportingFace Q P) (hS : SupportingFace S P) :
    SupportingFace (Q ∩ S) P := by
  obtain ⟨f, b, hf, hQ⟩ := hQ
  obtain ⟨g, d, hg, hS⟩ := hS
  refine ⟨f+g, b+d, fun x hx => add_le_add (hf x hx) (hg x hx), ?_⟩
  ext x
  simp only [hQ, hS, Set.mem_inter_iff, Set.mem_ofPred_eq, LinearMap.add_apply]
  constructor
  · rintro ⟨⟨hxP, hfx⟩, _, hgx⟩
    exact ⟨hxP, by rw [hfx, hgx]⟩
  · rintro ⟨hxP, hfgx⟩
    exact ⟨⟨hxP, by linarith [hf x hxP, hg x hxP]⟩,
      hxP, by linarith [hf x hxP, hg x hxP]⟩
lemma SupportingFace.eq_convexHull_subset {s : Finset V} {Q : Set V}
    (hQ : SupportingFace Q (convexHull ℝ (s : Set V))) :
    ∃ t : Finset V, t ⊆ s ∧ Q = convexHull ℝ (t : Set V) := by
  classical
  obtain ⟨f, b, hf, he⟩ := hQ
  refine ⟨s.filter (fun x => f x = b), Finset.filter_subset _ _, ?_⟩
  rw [he, convexHull_inter_supporting _ f b (fun x hx => hf x (subset_convexHull ℝ _ hx))]
  congr 1
  ext x
  simp
lemma finite_supportingFaces (s : Finset V) :
    {Q : Set V | Q.Nonempty ∧ SupportingFace Q (convexHull ℝ (s : Set V))}.Finite := by
  classical
  apply ((s.powerset.image (fun t : Finset V => convexHull ℝ (t : Set V))).finite_toSet).subset
  intro Q hQ
  obtain ⟨t, ht, rfl⟩ := hQ.2.eq_convexHull_subset
  exact Finset.mem_image_of_mem (fun t : Finset V => convexHull ℝ (t : Set V))
    (Finset.mem_powerset.mpr ht)
lemma SupportingFace.inter_of_parent_inter {s : Finset V} {P Q R S : Set V}
    (hQ : SupportingFace Q P) (hR : SupportingFace R S)
    (hPS : SupportingFace (P ∩ S) P)
    (hs : Q = convexHull ℝ (s : Set V)) : SupportingFace (Q ∩ R) Q := by
  have hQS : SupportingFace (Q ∩ S) Q := by
    have h := hPS.restrict hQ.subset
    have he : Q ∩ (P ∩ S) = Q ∩ S := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hx.2.2⟩,
        fun hx => ⟨hx.1, hQ.subset hx.1, hx.2⟩⟩
    rwa [he] at h
  have hQR : SupportingFace ((Q ∩ S) ∩ R) (Q ∩ S) := hR.restrict Set.inter_subset_right
  have he : (Q ∩ S) ∩ R = Q ∩ R := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩,
      fun hx => ⟨⟨hx.1, hR.subset hx.2⟩, hx.2⟩⟩
  rw [he] at hQR
  rw [hs] at hQS ⊢
  exact hQS.trans_finite_hull (by simpa only [hs] using hQR)
structure CellData (P : Set V) where
  n : ℕ
  a : Fin n → V →ₗ[ℝ] ℝ
  b : Fin n → ℝ
  eq_cell : P = cell a b
  bounded : Bornology.IsBounded P
  center : V
  center_mem : center ∈ P
  center_support : ∀ (f : V →ₗ[ℝ] ℝ) (d : ℝ), (∀ x ∈ P, f x ≤ d) →
    f center = d → ∀ x ∈ P, f x = d
lemma cell_reindex {I J : Type*} (e : I ≃ J) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) :
    cell (fun j => a (e.symm j)) (fun j => b (e.symm j)) = cell a b := by
  ext x
  constructor
  · intro hx i
    simpa only [Equiv.symm_apply_apply] using hx (e i)
  · intro hx j
    exact hx (e.symm j)
noncomputable def CellData.ofPresentation {I : Type*} [Fintype I]
    (P : Set V) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (he : P = cell a b)
    (hb : Bornology.IsBounded P) (c : V) (hc : c ∈ P)
    (hcs : ∀ (f : V →ₗ[ℝ] ℝ) (d : ℝ), (∀ x ∈ P, f x ≤ d) →
      f c = d → ∀ x ∈ P, f x = d) : CellData P where
  n := Fintype.card I
  a := fun i => a ((Fintype.equivFin I).symm i)
  b := fun i => b ((Fintype.equivFin I).symm i)
  eq_cell := he.trans (cell_reindex (Fintype.equivFin I) a b).symm
  bounded := hb
  center := c
  center_mem := hc
  center_support := hcs
lemma vertexMean_supports {s : Finset V} (hs : s.Nonempty)
    (f : V →ₗ[ℝ] ℝ) (d : ℝ)
    (hf : ∀ x ∈ convexHull ℝ (s : Set V), f x ≤ d)
    (hc : f (vertexMean s) = d) :
    ∀ x ∈ convexHull ℝ (s : Set V), f x = d := by
  have hv := (linear_vertexMean_eq_iff f hs (fun x hx =>
    hf x (subset_convexHull ℝ _ hx))).mp hc
  intro x hx
  exact linear_eq_on_affineSpan f hv (convexHull_subset_affineSpan (s : Set V) hx)
noncomputable def CellData.supportingFace {P Q : Set V} (p : CellData P)
    (s : Finset V) (hs : P = convexHull ℝ (s : Set V))
    (hQ : SupportingFace Q P) (hne : Q.Nonempty) : CellData Q := by
  classical
  refine Classical.choice ?_
  obtain ⟨f, d, hf, he⟩ := hQ
  let a' : Fin p.n ⊕ Bool → V →ₗ[ℝ] ℝ := Sum.elim p.a (fun j => if j then -f else f)
  let b' : Fin p.n ⊕ Bool → ℝ := Sum.elim p.b (fun j => if j then -d else d)
  have hcell : Q = cell a' b' := by
    ext x
    rw [he]
    constructor
    · rintro ⟨hx, hfx⟩ i
      change f x = d at hfx
      rcases i with i | i
      · exact (p.eq_cell ▸ hx) i
      · cases i <;> simp [a', b', hfx]
    · intro hx
      refine ⟨?_, le_antisymm (hx (Sum.inr false)) ?_⟩
      · rw [p.eq_cell]
        exact fun i => hx (Sum.inl i)
      · have hh := hx (Sum.inr true)
        simpa [a', b'] using hh
  have hQ' : SupportingFace Q (convexHull ℝ (s : Set V)) := hs ▸ ⟨f, d, hf, he⟩
  obtain ⟨t, _, ht⟩ := hQ'.eq_convexHull_subset
  have htn : t.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp (ht ▸ hne))
  refine ⟨CellData.ofPresentation Q a' b' hcell (p.bounded.subset ?_) (vertexMean t) ?_ ?_⟩
  · exact fun x hx => (he.subset hx).1
  · rw [ht]
    exact vertexMean_mem_convexHull htn
  · intro g c hg heq x hx
    rw [ht] at hg hx
    exact vertexMean_supports htn g c hg heq x hx
lemma CellData.face_subset_boundary {P Q : Set V} (p : CellData P)
    (hQ : SupportingFace Q P) (hproper : Q ≠ P) :
    Q ⊆ radialBoundary p.a p.b p.center := by
  obtain ⟨f, d, hf, hQ⟩ := hQ
  have hc : f p.center < d := lt_of_le_of_ne (hf _ p.center_mem) (by
    intro he
    apply hproper
    rw [hQ]
    exact Set.inter_eq_left.mpr (fun x hx => p.center_support f d hf he x hx))
  intro x hx
  have hPx : x ∈ P := (hQ.subset hx).1
  apply mem_radialBoundary_of_supporting p.a p.b
    (p.eq_cell ▸ p.bounded) (p.eq_cell ▸ p.center_mem) (p.eq_cell ▸ hPx) f d
    (by simpa only [← p.eq_cell] using hf) hc
  exact (hQ.subset hx).2
lemma CellData.boundary_mem_face {P : Set V} (p : CellData P)
    {x : V} (hx : x ∈ radialBoundary p.a p.b p.center) :
    ∃ Q, SupportingFace Q P ∧ Q ≠ P ∧ x ∈ Q := by
  obtain ⟨hxp, i, hi, hic⟩ := hx
  refine ⟨P ∩ {y | p.a i y = p.b i}, ?_, ?_, ?_⟩
  · exact ⟨p.a i, p.b i, fun y hy => (p.eq_cell ▸ hy) i, rfl⟩
  · intro he
    have hc := he.symm.subset p.center_mem
    exact (ne_of_lt hic) hc.2
  · exact ⟨p.eq_cell.symm ▸ hxp, hi⟩
structure FiniteCellFamily (F : Finset (Set V)) : Prop where
  data : ∀ P ∈ F, Nonempty (CellData P)
  faces : ∀ P ∈ F, ∀ Q, SupportingFace Q P → Q.Nonempty → Q ∈ F
  inter : ∀ P ∈ F, ∀ Q ∈ F, SupportingFace (P ∩ Q) P
lemma FiniteCellFamily.erase_maximal {F : Finset (Set V)}
    (hF : FiniteCellFamily F) {P : Set V} (hm : Maximal (· ∈ F) P) :
    FiniteCellFamily (F.erase P) := by
  classical
  refine ⟨fun Q hQ => hF.data Q (Finset.mem_of_mem_erase hQ), ?_, ?_⟩
  · intro Q hQ R hR hne
    apply Finset.mem_erase.mpr
    refine ⟨?_, hF.faces Q (Finset.mem_of_mem_erase hQ) R hR hne⟩
    intro he
    subst R
    have hQP : Q ⊆ P := hm.2 (Finset.mem_of_mem_erase hQ) hR.subset
    exact (Finset.mem_erase.mp hQ).1 (Set.Subset.antisymm hQP hR.subset)
  · intro Q hQ R hR
    exact hF.inter Q (Finset.mem_of_mem_erase hQ) R (Finset.mem_of_mem_erase hR)
def familySpace (F : Finset (Set V)) : Set V := {x | ∃ P ∈ F, x ∈ P}
structure CellTriangulation (F : Finset (Set V)) where
  complex : Geometry.SimplicialComplex ℝ V
  finite : complex.faces.Finite
  space : complex.space = familySpace F
  trace : ∀ P ∈ F, RespectsSet complex P
  carrier : ∀ s ∈ complex.faces, ∃ P ∈ F, convexHull ℝ (s : Set V) ⊆ P
lemma CellTriangulation.respects_of_carrier {F : Finset (Set V)}
    (B : CellTriangulation F) (P : Set V)
    (hP : ∀ Q ∈ F, SupportingFace (Q ∩ P) Q) : RespectsSet B.complex P := by
  intro s hs
  obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
  obtain ⟨f, b, hf, he⟩ := hP Q hQ
  exact hull_inter_of_supporting_eq s Q P hsQ f b hf he
noncomputable def CellTriangulation.extend {F : Finset (Set V)}
    (hF : FiniteCellFamily F) {P : Set V} (hm : Maximal (· ∈ F) P)
    (B : CellTriangulation (F.erase P)) (p : CellData P) : CellTriangulation F := by
  classical
  have hBP : RespectsSet B.complex P := B.respects_of_carrier P (fun Q hQ =>
    hF.inter Q (Finset.mem_of_mem_erase hQ) P hm.1)
  let T := restrictComplex B.complex P
  have hT : T.space = radialBoundary p.a p.b p.center := by
    rw [show T.space = B.complex.space ∩ P from
      restrictComplex_space_of_respects B.complex P hBP, B.space]
    ext x
    constructor
    · rintro ⟨⟨Q, hQ, hxQ⟩, hxP⟩
      have hproper : P ∩ Q ≠ P := by
        intro he
        have hPQ : P ⊆ Q := fun y hy => (he.symm.subset hy).2
        have hQP := hm.2 (Finset.mem_of_mem_erase hQ) hPQ
        exact (Finset.mem_erase.mp hQ).1 (Set.Subset.antisymm hQP hPQ)
      exact p.face_subset_boundary
        (hF.inter P hm.1 Q (Finset.mem_of_mem_erase hQ)) hproper ⟨hxP, hxQ⟩
    · intro hx
      obtain ⟨Q, hQ, hproper, hxQ⟩ := p.boundary_mem_face hx
      exact ⟨⟨Q, Finset.mem_erase.mpr ⟨hproper, hF.faces P hm.1 Q hQ ⟨x, hxQ⟩⟩,
        hxQ⟩, hQ.subset hxQ⟩
  have hspan : ∀ s ∈ T.faces, p.center ∉ affineSpan ℝ (s : Set V) :=
    fun s hs => center_notMem_affineSpan_boundaryFace p.a p.b T p.center hT.subset hs
  let C := coneComplex p.a p.b T p.center hT.subset hspan
  have hC : C.space = P := by
    rw [p.eq_cell]
    exact coneComplex_space_eq_cell p.a p.b (p.eq_cell ▸ p.bounded)
      T p.center (p.eq_cell ▸ p.center_mem) hT
  have hTC : T ≤ C := by
    intro s hs
    exact (mem_coneFaces_iff T p.center s).mpr (Or.inr (Or.inl hs))
  have hcross : ∀ s ∈ B.complex.faces, ∀ t ∈ C.faces,
      convexHull ℝ (s : Set V) ∩ convexHull ℝ (t : Set V) ⊆
        convexHull ℝ ((s : Set V) ∩ (t : Set V)) :=
    fun _ hs _ ht => cross_inter_of_respects B.complex C P hBP hC.subset hTC hs ht
  refine ⟨glueComplex B.complex C hcross, ?_, ?_, ?_, ?_⟩
  · exact glueComplex_finite B.complex C hcross B.finite
      (coneComplex_finite p.a p.b T p.center hT.subset hspan
        (restrictComplex_finite B.complex P B.finite))
  · rw [glueComplex_space, B.space, hC]
    ext x
    constructor
    · rintro (⟨Q, hQ, hxQ⟩ | hxP)
      · exact ⟨Q, Finset.mem_of_mem_erase hQ, hxQ⟩
      · exact ⟨P, hm.1, hxP⟩
    · rintro ⟨Q, hQ, hxQ⟩
      by_cases he : Q = P
      · exact Or.inr (he ▸ hxQ)
      · exact Or.inl ⟨Q, Finset.mem_erase.mpr ⟨he, hQ⟩, hxQ⟩
  · intro Q hQ s hs
    rcases hs with hs | hs
    · by_cases he : Q = P
      · exact he ▸ hBP s hs
      · exact B.trace Q (Finset.mem_erase.mpr ⟨he, hQ⟩) s hs
    · obtain ⟨f, b, hf, he⟩ := hF.inter P hm.1 Q hQ
      exact respectsSet_of_supporting_eq C P Q hC.subset f b hf he s hs
  · intro s hs
    rcases hs with hs | hs
    · obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
      exact ⟨Q, Finset.mem_of_mem_erase hQ, hsQ⟩
    · exact ⟨P, hm.1, (C.convexHull_subset_space hs).trans hC.subset⟩
open scoped Classical
lemma CellTriangulation.mem_extend_faces {F : Finset (Set V)}
    (hF : FiniteCellFamily F) {P : Set V} (hm : Maximal (· ∈ F) P)
    (B : CellTriangulation (F.erase P)) (p : CellData P) (s : Finset V) :
    s ∈ (B.extend hF hm p).complex.faces ↔
      s ∈ B.complex.faces ∨ s = {p.center} ∨
        ∃ t ∈ B.complex.faces, (t : Set V) ⊆ P ∧ s = insert p.center t := by
  classical
  change s ∈ B.complex.faces ∨ s ∈ coneFaces (restrictComplex B.complex P) p.center ↔ _
  rw [mem_coneFaces_iff]
  constructor
  · rintro (hs | hs | hs | ⟨t, ht, rfl⟩)
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inl hs.1
    · exact Or.inr (Or.inr ⟨t, ht.1, ht.2, rfl⟩)
  · rintro (hs | hs | ⟨t, ht, htP, rfl⟩)
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr (Or.inr ⟨t, ⟨ht, htP⟩, rfl⟩))
lemma CellData.center_mem_iff_subset {P Q : Set V} (p : CellData Q)
    (h : SupportingFace (Q ∩ P) Q) : p.center ∈ P ↔ Q ⊆ P := by
  constructor
  · intro hp
    obtain ⟨f, d, hf, he⟩ := h
    have hc := he.subset ⟨p.center_mem, hp⟩
    intro x hx
    exact (he.symm.subset ⟨hx, p.center_support f d hf hc.2 x hx⟩).2
  · intro h
    exact h p.center_mem
noncomputable def chainFaces (F : Finset (Set V)) (c : Set V → V) : Set (Finset V) :=
  {s | ∃ t : Finset (Set V), t.Nonempty ∧ t ⊆ F ∧
      (t : Set (Set V)).Pairwise (fun P Q => P ⊆ Q ∨ Q ⊆ P) ∧ s = t.image c}
omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma mem_chainFaces_erase_subset {F : Finset (Set V)} {P : Set V}
    {c : Set V → V} {s : Finset V} (hs : s ∈ chainFaces (F.erase P) c) :
    s ∈ chainFaces F c := by
  classical
  obtain ⟨t, hne, hsub, hchain, he⟩ := hs
  exact ⟨t, hne, hsub.trans (Finset.erase_subset _ _), hchain, he⟩
omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma chainFaces_maximal {F : Finset (Set V)} {P : Set V}
    (hm : Maximal (· ∈ F) P) (c : Set V → V)
    (hc : ∀ Q ∈ F, c Q ∈ P ↔ Q ⊆ P) (s : Finset V) :
    s ∈ chainFaces F c ↔ s ∈ chainFaces (F.erase P) c ∨
      s = {c P} ∨ ∃ t ∈ chainFaces (F.erase P) c,
        (t : Set V) ⊆ P ∧ s = insert (c P) t := by
  classical
  constructor
  · rintro ⟨t, hne, hsub, hchain, rfl⟩
    by_cases hP : P ∈ t
    · have hQP (Q : Set V) (hQ : Q ∈ t) : Q ⊆ P := by
        by_cases he : Q = P
        · exact he ▸ Set.Subset.refl _
        · rcases hchain hQ hP he with h | h
          · exact h
          · exact hm.2 (hsub hQ) h
      by_cases hempty : t.erase P = ∅
      · right; left
        have ht : t = {P} := by
          ext Q
          simp only [Finset.mem_singleton]
          constructor
          · intro hQ
            by_contra hn
            have hh : Q ∈ t.erase P := Finset.mem_erase.mpr ⟨hn, hQ⟩
            rw [hempty] at hh
            exact Finset.notMem_empty Q hh
          · rintro rfl; exact hP
        simp [ht]
      · right; right
        refine ⟨(t.erase P).image c, ?_, ?_, ?_⟩
        · exact ⟨t.erase P, Finset.nonempty_iff_ne_empty.mpr hempty,
            fun Q hQ => Finset.mem_erase.mpr
              ⟨(Finset.mem_erase.mp hQ).1, hsub (Finset.mem_of_mem_erase hQ)⟩,
            hchain.mono (Finset.erase_subset _ _), rfl⟩
        · intro x hx
          obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hx
          exact (hc Q (hsub (Finset.mem_of_mem_erase hQ))).mpr
            (hQP Q (Finset.mem_of_mem_erase hQ))
        · rw [← Finset.image_insert, Finset.insert_erase hP]
    · left
      exact ⟨t, hne, fun Q hQ => Finset.mem_erase.mpr
        ⟨fun he => hP (he ▸ hQ), hsub hQ⟩, hchain, rfl⟩
  · rintro (hs | rfl | ⟨s, ⟨t, hne, hsub, hchain, rfl⟩, hcorn, rfl⟩)
    · exact mem_chainFaces_erase_subset hs
    · exact ⟨{P}, Finset.singleton_nonempty _, by simpa using hm.1,
        by simp, by simp⟩
    · refine ⟨insert P t, Finset.insert_nonempty _ _, ?_, ?_, by simp⟩
      · intro Q hQ
        rcases Finset.mem_insert.mp hQ with rfl | hQ
        · exact hm.1
        · exact Finset.mem_of_mem_erase (hsub hQ)
      · rw [Finset.coe_insert, Set.pairwise_insert]
        refine ⟨hchain, ?_⟩
        intro Q hQ _
        have hQF := Finset.mem_of_mem_erase (hsub hQ)
        have hQP := (hc Q hQF).mp (hcorn (Finset.mem_image_of_mem c hQ))
        exact ⟨Or.inr hQP, Or.inl hQP⟩
theorem exists_cellTriangulation_chains (F : Finset (Set V))
    (hF : FiniteCellFamily F) (c : Set V → V)
    (hcenters : ∀ P ∈ F, ∃ p : CellData P, p.center = c P) :
    ∃ B : CellTriangulation F, B.complex.faces = chainFaces F c := by
  classical
  revert hF hcenters
  refine F.strongInductionOn ?_
  intro F ih hF hcenters
  by_cases hne : F.Nonempty
  · obtain ⟨P, hm⟩ := Finset.exists_maximal hne
    obtain ⟨B, hB⟩ := ih (F.erase P) (Finset.erase_ssubset hm.1)
      (hF.erase_maximal hm) (fun Q hQ => hcenters Q (Finset.mem_of_mem_erase hQ))
    obtain ⟨p, hp⟩ := hcenters P hm.1
    refine ⟨B.extend hF hm p, ?_⟩
    ext s
    rw [CellTriangulation.mem_extend_faces, hB, hp]
    exact (chainFaces_maximal hm c (fun Q hQ => by
      obtain ⟨q, hq⟩ := hcenters Q hQ
      rw [← hq]
      exact q.center_mem_iff_subset (hF.inter Q hQ P hm.1)) s).symm
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst F
    let B : CellTriangulation (∅ : Finset (Set V)) := {
      complex := ⊥
      finite := by simp [Geometry.SimplicialComplex.faces_bot]
      space := by ext x; simp [familySpace, Geometry.SimplicialComplex.space_bot]
      trace := by simp
      carrier := by simp [Geometry.SimplicialComplex.faces_bot] }
    refine ⟨B, ?_⟩
    ext s
    simp only [B, Geometry.SimplicialComplex.faces_bot, Set.mem_empty_iff_false,
      false_iff]
    rintro ⟨t, ht, htF, _⟩
    have ht0 : t = ∅ := Finset.subset_empty.mp htF
    exact ht.ne_empty ht0
end BassTrace.Sparse.Cuts
end OAI
end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
open Set Finset
open scoped Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
section CellVertices
open Filter
open scoped Topology
variable {I : Type*} [Fintype I]
noncomputable def activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) : Finset I :=
  Finset.univ.filter fun i => a i x = b i
lemma mem_activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) (i : I) :
    i ∈ activeConstraints a b x ↔ a i x = b i := by
  classical
  simp [activeConstraints]
lemma exists_extrapolate_mem
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) {x y : E}
    (hx : x ∈ cell a b)
    (hactive : activeConstraints a b x = activeConstraints a b y) :
    ∃ t : ℝ, 0 < t ∧ x + t • (x - y) ∈ cell a b := by
  have hi (i : I) : ∀ᶠ t : ℝ in 𝓝 0, a i (x + t • (x - y)) ≤ b i := by
    by_cases h : a i x = b i
    · have hyi : a i y = b i := by
        rw [← mem_activeConstraints, ← hactive, mem_activeConstraints]
        exact h
      filter_upwards [] with t
      simp only [map_add, map_smul, map_sub, smul_eq_mul, h, hyi, sub_self,
        mul_zero, add_zero, le_refl]
    · have hlt : a i x < b i := lt_of_le_of_ne (hx i) h
      have hc : Continuous (fun t : ℝ => a i x + t * (a i x - a i y)) := by fun_prop
      have he : ∀ᶠ t : ℝ in 𝓝 0, a i x + t * (a i x - a i y) < b i :=
        hc.continuousAt.eventually (gt_mem_nhds (by simpa using hlt))
      filter_upwards [he] with t ht
      simpa only [map_add, map_smul, map_sub, smul_eq_mul] using ht.le
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, a i (x + t • (x - y)) ≤ b i :=
    Filter.eventually_all.mpr hi
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨δ / 2, by positivity, hball ?_⟩
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [abs_of_pos (by positivity : 0 < δ / 2)]
  linarith
lemma activeConstraints_injOn_extremePoints
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    Set.InjOn (activeConstraints a b) ((cell a b).extremePoints ℝ) := by
  intro x hx y hy hactive
  obtain ⟨t, ht, hz⟩ := exists_extrapolate_mem a b hx.1 hactive
  have hsum : t + 1 ≠ 0 := by positivity
  have hseg : x ∈ openSegment ℝ y (x + t • (x - y)) := by
    apply mem_openSegment_iff_div.mpr
    refine ⟨t, 1, ht, by norm_num, ?_⟩
    simp only [smul_add, smul_sub, smul_smul]
    rw [show 1 / (t + 1) * t = t / (t + 1) by ring]
    calc
      _ = (1 / (t + 1) + t / (t + 1)) • x := by module
      _ = x := by rw [← add_div, add_comm 1 t, div_self hsum, one_smul]
  exact (hx.2 hy.1 hz hseg).symm
lemma finite_extremePoints_cell
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    ((cell a b).extremePoints ℝ).Finite := by
  classical
  exact Set.Finite.of_injOn (t := Set.univ) (Set.mapsTo_univ _ _)
    (activeConstraints_injOn_extremePoints a b) Set.finite_univ
noncomputable def polyhedronVertices (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Finset E :=
  (finite_extremePoints_cell a b).toFinset
@[simp] lemma mem_polyhedronVertices
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) :
    x ∈ polyhedronVertices a b ↔ x ∈ (cell a b).extremePoints ℝ :=
  Set.Finite.mem_toFinset _
variable [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
lemma exists_extreme_maximizer {s : Set E} (hs : IsCompact s) (hne : s.Nonempty)
    (f : E →L[ℝ] ℝ) :
    ∃ x ∈ s.extremePoints ℝ, ∀ y ∈ s, f y ≤ f x := by
  obtain ⟨x, hx, hxmax⟩ := hs.exists_isMaxOn hne f.continuous.continuousOn
  have hex : IsExposed ℝ s {x ∈ s | ∀ y ∈ s, f y ≤ f x} := fun _ => ⟨f, rfl⟩
  obtain ⟨z, hz⟩ := (hex.isCompact hs).extremePoints_nonempty ⟨x, hx, hxmax⟩
  exact ⟨z, hex.isExtreme.extremePoints_subset_extremePoints hz, hz.1.2⟩
lemma cell_eq_convexHull_vertices
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hc : IsCompact (cell a b)) :
    cell a b = convexHull ℝ (polyhedronVertices a b : Set E) := by
  have hv : Convex ℝ (cell a b) := by
    intro x hx y hy r s hr hs hrs i
    simp only [map_add, map_smul, smul_eq_mul]
    calc
      r * a i x + s * a i y ≤ r * b i + s * b i :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) hr)
          (mul_le_mul_of_nonneg_left (hy i) hs)
      _ = b i := by rw [← add_mul, hrs, one_mul]
  have he : (polyhedronVertices a b : Set E) =
      (cell a b).extremePoints ℝ := by
    ext x
    exact mem_polyhedronVertices a b x
  have h := closure_convexHull_extremePoints hc hv
  rw [← he, ((polyhedronVertices a b).finite_toSet.isClosed_convexHull (𝕜 := ℝ)).closure_eq] at h
  exact h.symm
end CellVertices
section Arrangements
variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I] [Fintype J]
omit [Fintype I] in
lemma isClosed_cell (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) : IsClosed (cell a b) := by
  have he : cell a b = ⋂ i, {x | a i x ≤ b i} := by ext x; simp [cell]
  rw [he]
  exact isClosed_iInter fun i => isClosed_le (a i).continuous_of_finiteDimensional continuous_const
lemma cell_eq_convexHull_of_bounded (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hb : Bornology.IsBounded (cell a b)) :
    cell a b = convexHull ℝ (polyhedronVertices a b : Set V) :=
  cell_eq_convexHull_vertices a b (Metric.isCompact_of_isClosed_isBounded (isClosed_cell a b) hb)
noncomputable def CellData.ofBounded (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hb : Bornology.IsBounded (cell a b)) (hne : (cell a b).Nonempty) :
    CellData (cell a b) := by
  have he := cell_eq_convexHull_of_bounded a b hb
  have hvn : (polyhedronVertices a b).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp (he ▸ hne))
  exact CellData.ofPresentation _ a b rfl hb (vertexMean (polyhedronVertices a b))
    (he ▸ vertexMean_mem_convexHull hvn) (fun f d hf hc x hx =>
      vertexMean_supports hvn f d (he ▸ hf) hc x (he ▸ hx))
def signedForm (a : J → V →ₗ[ℝ] ℝ) (s : J → Bool) (j : J) : V →ₗ[ℝ] ℝ :=
  if s j then a j else -a j
def signedBound (b : J → ℝ) (s : J → Bool) (j : J) : ℝ :=
  if s j then b j else -b j
def cutCell (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (s : J → Bool) : Set V := P ∩ cell (signedForm a s) (signedBound b s)
lemma cutCell_nonempty_data {P : Set V} (p : CellData P)
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) (s : J → Bool)
    (hne : (cutCell P a b s).Nonempty) :
    Nonempty (CellData (cutCell P a b s)) ∧
    ∃ v : Finset V, cutCell P a b s = convexHull ℝ (v : Set V) := by
  let a' : Fin p.n ⊕ J → V →ₗ[ℝ] ℝ := Sum.elim p.a (signedForm a s)
  let b' : Fin p.n ⊕ J → ℝ := Sum.elim p.b (signedBound b s)
  have he : cutCell P a b s = cell a' b' := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩ i
      cases i with
      | inl i => exact (p.eq_cell ▸ hx) i
      | inr j => exact hy j
    · intro hx
      exact ⟨p.eq_cell.symm ▸ (show x ∈ cell p.a p.b from fun i => hx (Sum.inl i)),
        fun j => hx (Sum.inr j)⟩
  have hb : Bornology.IsBounded (cell a' b') :=
    he ▸ p.bounded.subset Set.inter_subset_left
  exact ⟨⟨he ▸ CellData.ofBounded a' b' hb (he ▸ hne)⟩,
    polyhedronVertices a' b', he.trans (cell_eq_convexHull_of_bounded a' b' hb)⟩
omit [FiniteDimensional ℝ V] in
lemma cutCell_inter_supporting (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (s t : J → Bool) : SupportingFace (cutCell P a b s ∩ cutCell P a b t)
      (cutCell P a b s) := by
  classical
  let T : Finset J := Finset.univ.filter fun j => s j ≠ t j
  let f : V →ₗ[ℝ] ℝ := ∑ j ∈ T, signedForm a s j
  let d : ℝ := ∑ j ∈ T, signedBound b s j
  have hle {x : V} (hx : x ∈ cutCell P a b s) : f x ≤ d := by
    simp only [f, LinearMap.sum_apply]
    exact Finset.sum_le_sum fun j _ => hx.2 j
  have heq {x : V} (hx : x ∈ cutCell P a b s) :
      f x = d ↔ ∀ j ∈ T, signedForm a s j x = signedBound b s j := by
    simp only [f, d, LinearMap.sum_apply]
    exact Finset.sum_eq_sum_iff_of_le (fun j _ => hx.2 j)
  refine ⟨f, d, fun _ hx => hle hx, ?_⟩
  ext x
  constructor
  · rintro ⟨hxs, hxt⟩
    refine ⟨hxs, (heq hxs).mpr ?_⟩
    intro j hj
    have hst : s j ≠ t j := (Finset.mem_filter.mp hj).2
    have hs := hxs.2 j
    have ht := hxt.2 j
    cases hs' : s j <;> cases ht' : t j <;>
      simp only [hs', ht', signedForm, signedBound, Bool.false_eq_true, ↓reduceIte,
        LinearMap.neg_apply, ne_eq, not_true_eq_false] at hst hs ht ⊢ <;> linarith
  · rintro ⟨hxs, hfx⟩
    refine ⟨hxs, hxs.1, ?_⟩
    intro j
    by_cases hst : s j = t j
    · simpa only [signedForm, signedBound, ← hst] using hxs.2 j
    · have hjeq := (heq hxs).mp hfx j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hst⟩)
      cases hs' : s j <;> cases ht' : t j <;>
        simp only [hs', ht', signedForm, signedBound, Bool.false_eq_true, ↓reduceIte,
          LinearMap.neg_apply, not_true_eq_false] at hst hjeq ⊢ <;> linarith
omit [Fintype J] [FiniteDimensional ℝ V] in
lemma cutCell_cover (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) :
    P = ⋃ s : J → Bool, cutCell P a b s := by
  classical
  ext x
  constructor
  · intro hx
    apply Set.mem_iUnion.mpr
    refine ⟨fun j => decide (a j x ≤ b j), hx, ?_⟩
    intro j
    by_cases h : a j x ≤ b j
    · simp [signedForm, signedBound, h]
    · simp only [signedForm, signedBound, h, decide_false, Bool.false_eq_true,
        ↓reduceIte, LinearMap.neg_apply]
      linarith
  · intro hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    exact hs.1
end Arrangements
section ArrangementTriangulation
variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype J]
omit [FiniteDimensional ℝ V] in
lemma SupportingFace.inter_restrict {P Q S : Set V}
    (h : SupportingFace (P ∩ Q) P) (hSP : S ⊆ P) : SupportingFace (S ∩ Q) S := by
  have hh := h.restrict hSP
  convert hh using 1
  ext x
  exact ⟨fun hx => ⟨hx.1, hSP hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
omit [FiniteDimensional ℝ V] in
lemma cutCell_inter_parents_supporting {P Q : Set V}
    (hPQ : SupportingFace (P ∩ Q) P) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (s t : J → Bool) : SupportingFace
      (cutCell P a b s ∩ cutCell Q a b t) (cutCell P a b s) := by
  have hQ := hPQ.inter_restrict (show cutCell P a b s ⊆ P from Set.inter_subset_left)
  have hT := cutCell_inter_supporting P a b s t
  have hh := hQ.supporting_inter hT
  convert hh using 1
  ext x
  simp only [cutCell, Set.mem_inter_iff]
  tauto
noncomputable def cutParents (A : Finset (Set V))
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) : Finset (Set V) := by
  classical
  exact ((A ×ˢ Finset.univ).image (fun ps : Set V × (J → Bool) => cutCell ps.1 a b ps.2)).filter
    Set.Nonempty
omit [FiniteDimensional ℝ V] in
lemma mem_cutParents (A : Finset (Set V)) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (Q : Set V) : Q ∈ cutParents A a b ↔
      ∃ P ∈ A, ∃ s : J → Bool, Q = cutCell P a b s ∧ Q.Nonempty := by
  classical
  simp only [cutParents, Finset.mem_filter, Finset.mem_image, Finset.mem_product,
    Finset.mem_univ, and_true, Prod.exists]
  constructor
  · rintro ⟨⟨P, s, hP, he⟩, hne⟩
    exact ⟨P, hP, s, he.symm, hne⟩
  · rintro ⟨P, hP, s, he, hne⟩
    exact ⟨⟨P, s, hP, he.symm⟩, hne⟩
end ArrangementTriangulation
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
omit [FiniteDimensional ℝ V] in
lemma affine_decomp_apply (f : V →ᵃ[ℝ] ℝ) (x : V) : f x = f.linear x + f 0 := by
  exact congrFun f.decomp x
theorem simplex_has_cellData (s : Finset V) (hs : s.Nonempty)
    (hi : AffineIndependent ℝ ((↑) : s → V)) :
    Nonempty (CellData (convexHull ℝ (s : Set V))) := by
  classical
  obtain ⟨t, hst, htind, httop⟩ :=
    exists_subset_affineIndependent_affineSpan_eq_top hi
  let B : AffineBasis t ℝ V := ⟨Subtype.val, htind, by simpa using httop⟩
  let : Finite t := B.finite
  let : Fintype t := Fintype.ofFinite t
  let v : Finset V := (B.setFinite).toFinset
  have hv : (v : Set V) = t := Set.Finite.coe_toFinset _
  have hBrange : Set.range B = t := Subtype.range_coe
  let a : t → V →ₗ[ℝ] ℝ := fun i => -(B.coord i).linear
  let b : t → ℝ := fun i => B.coord i 0
  have hfull : convexHull ℝ (v : Set V) = cell a b := by
    have he : convexHull ℝ (v : Set V) = convexHull ℝ (Set.range B) :=
      congrArg (convexHull ℝ) (hv.trans hBrange.symm)
    rw [he, B.convexHull_eq_nonneg_coord]
    ext x
    constructor
    · intro hx i
      have hd := affine_decomp_apply (B.coord i) x
      have hc := hx i
      change -(B.coord i).linear x ≤ B.coord i 0
      linarith
    · intro hx i
      have hd := affine_decomp_apply (B.coord i) x
      have hc : -(B.coord i).linear x ≤ B.coord i 0 := hx i
      linarith
  have hfull_ne : (cell a b).Nonempty := by
    apply hfull ▸ ((convexHull_nonempty_iff).mpr ?_)
    obtain ⟨x, hx⟩ := hs
    exact ⟨x, by rw [hv]; exact hst hx⟩
  have hbounded : Bornology.IsBounded (cell a b) := by
    rw [← hfull]
    exact (v.finite_toSet.isCompact_convexHull ℝ).isBounded
  let p : CellData (convexHull ℝ (v : Set V)) :=
    hfull ▸ CellData.ofBounded a b hbounded hfull_ne
  let S : Finset t := Finset.univ.filter fun i => (i : V) ∈ s
  let f : V →ᵃ[ℝ] ℝ := ∑ i ∈ S, B.coord i
  have hf_basis (i : t) : f (B i) = if (i : V) ∈ s then 1 else 0 := by
    have hsum (T : Finset t) : (∑ j ∈ T, B.coord j) (B i) =
        ∑ j ∈ T, B.coord j (B i) := by
      induction T using Finset.induction_on with
      | empty => simp
      | @insert j T hj ih => simp [Finset.sum_insert hj, ih]
    rw [hsum]
    simp only [B.coord_apply]
    simp [S]
  have hle : ∀ x ∈ (v : Set V), f.linear x ≤ 1-f 0 := by
    intro x hx
    have hxt : x ∈ t := hv ▸ hx
    have hh := hf_basis ⟨x, hxt⟩
    have hd := affine_decomp_apply f x
    change f x = if x ∈ s then 1 else 0 at hh
    split_ifs at hh <;> linarith
  have he : (v : Set V) ∩ {x | f.linear x = 1-f 0} = (s : Set V) := by
    ext x
    constructor
    · rintro ⟨hx, he⟩
      have hxt : x ∈ t := hv ▸ hx
      have hh := hf_basis ⟨x, hxt⟩
      have hd := affine_decomp_apply f x
      change f x = if x ∈ s then 1 else 0 at hh
      by_contra hxs
      change x ∉ s at hxs
      rw [ite_eq_right hxs] at hh
      change f.linear x = 1-f 0 at he
      linarith
    · intro hx
      have hxt := hst hx
      refine ⟨by rw [hv]; exact hxt, ?_⟩
      have hh := hf_basis ⟨x, hxt⟩
      have hd := affine_decomp_apply f x
      change f x = if x ∈ s then 1 else 0 at hh
      change x ∈ s at hx
      rw [ite_eq_left hx] at hh
      change f.linear x = 1-f 0
      linarith
  have hface : SupportingFace (convexHull ℝ (s : Set V))
      (convexHull ℝ (v : Set V)) := by
    refine ⟨f.linear, 1-f 0, linear_le_on_convexHull _ _ _ hle, ?_⟩
    rw [convexHull_inter_supporting _ f.linear (1-f 0) hle, he]
  exact ⟨p.supportingFace v rfl hface (convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs))⟩
omit [FiniteDimensional ℝ V] in
lemma simplex_affine_indicator (s t : Finset V)
    (hi : AffineIndependent ℝ ((↑) : s → V)) :
    ∃ f : V →ᵃ[ℝ] ℝ, ∀ x ∈ s, f x = if x ∈ t then 1 else 0 := by
  classical
  obtain ⟨u, hsu, huind, hutop⟩ := exists_subset_affineIndependent_affineSpan_eq_top hi
  let B : AffineBasis u ℝ V := ⟨Subtype.val, huind, by simpa using hutop⟩
  let T : Finset u := t.preimage Subtype.val Subtype.val_injective.injOn
  refine ⟨∑ i ∈ T, B.coord i, ?_⟩
  intro x hx
  let i : u := ⟨x, hsu hx⟩
  have hsum (R : Finset u) : (∑ j ∈ R, B.coord j) (B i) =
      ∑ j ∈ R, B.coord j (B i) := by
    induction R using Finset.induction_on with
    | empty => simp
    | @insert j R hj ih => simp [Finset.sum_insert hj, ih]
  change (∑ j ∈ T, B.coord j) (B i) = _
  rw [hsum]
  simp [T, B.coord_apply, i]
omit [FiniteDimensional ℝ V] in
lemma simplex_face_supporting (s t : Finset V)
    (hi : AffineIndependent ℝ ((↑) : s → V)) (ht : t ⊆ s) :
    SupportingFace (convexHull ℝ (t : Set V)) (convexHull ℝ (s : Set V)) := by
  classical
  obtain ⟨f, hf⟩ := simplex_affine_indicator s t hi
  have hle : ∀ x ∈ (s : Set V), f.linear x ≤ 1-f 0 := by
    intro x hx
    have hh := hf x hx
    have hd := affine_decomp_apply f x
    split_ifs at hh <;> linarith
  refine ⟨f.linear, 1-f 0, linear_le_on_convexHull _ _ _ hle, ?_⟩
  rw [convexHull_inter_supporting _ f.linear (1-f 0) hle]
  congr 1
  ext x
  constructor
  · intro hx
    refine ⟨ht hx, ?_⟩
    have hh := hf x (ht hx)
    have hd := affine_decomp_apply f x
    change x ∈ t at hx
    rw [ite_eq_left hx] at hh
    change f.linear x = 1-f 0
    linarith
  · rintro ⟨hx, he⟩
    have hh := hf x hx
    have hd := affine_decomp_apply f x
    change f.linear x = 1-f 0 at he
    by_contra hxt
    change x ∉ t at hxt
    rw [ite_eq_right hxt] at hh
    linarith
end BassTrace.Sparse.Cuts
end OAI
end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
open Set Finset
open scoped Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
section CanonicalCenters
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
noncomputable def canonicalVertices (P : Set V) : Finset V :=
  if h : (P.extremePoints ℝ).Finite then h.toFinset else ∅
noncomputable def canonicalCenter (P : Set V) : V := vertexMean (canonicalVertices P)
lemma coe_canonicalVertices {P : Set V} (hP : (P.extremePoints ℝ).Finite) :
    (canonicalVertices P : Set V) = P.extremePoints ℝ := by
  simp [canonicalVertices, hP]
lemma finite_extremePoints_finiteHull (s : Finset V) :
    ((convexHull ℝ (s : Set V)).extremePoints ℝ).Finite :=
  s.finite_toSet.subset extremePoints_convexHull_subset
lemma finiteHull_eq_canonicalVertices (s : Finset V) :
    convexHull ℝ (s : Set V) =
      convexHull ℝ (canonicalVertices (convexHull ℝ (s : Set V)) : Set V) := by
  have hfin := finite_extremePoints_finiteHull s
  rw [coe_canonicalVertices hfin]
  have hk := closure_convexHull_extremePoints (s.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ (s : Set V))
  rw [(hfin.isClosed_convexHull ℝ).closure_eq] at hk
  exact hk.symm
lemma canonicalCenter_mem_finiteHull {s : Finset V} (hs : s.Nonempty) :
    canonicalCenter (convexHull ℝ (s : Set V)) ∈ convexHull ℝ (s : Set V) := by
  have hne : (canonicalVertices (convexHull ℝ (s : Set V))).Nonempty := by
    apply Finset.coe_nonempty.mp
    have hh : (convexHull ℝ (s : Set V)).Nonempty :=
      convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)
    exact convexHull_nonempty_iff.mp ((finiteHull_eq_canonicalVertices s) ▸ hh)
  exact (finiteHull_eq_canonicalVertices s).symm.subset (vertexMean_mem_convexHull hne)
lemma canonicalCenter_supports_finiteHull {s : Finset V} (hs : s.Nonempty)
    (f : V →ₗ[ℝ] ℝ) (d : ℝ)
    (hf : ∀ x ∈ convexHull ℝ (s : Set V), f x ≤ d)
    (he : f (canonicalCenter (convexHull ℝ (s : Set V))) = d) :
    ∀ x ∈ convexHull ℝ (s : Set V), f x = d := by
  have hne : (canonicalVertices (convexHull ℝ (s : Set V))).Nonempty := by
    apply Finset.coe_nonempty.mp
    have hh : (convexHull ℝ (s : Set V)).Nonempty :=
      convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)
    exact convexHull_nonempty_iff.mp ((finiteHull_eq_canonicalVertices s) ▸ hh)
  intro x hx
  exact vertexMean_supports hne f d ((finiteHull_eq_canonicalVertices s) ▸ hf)
    he x ((finiteHull_eq_canonicalVertices s) ▸ hx)
lemma affine_image_extremePoints (e : V ≃ᵃ[ℝ] W) (P : Set V) :
    e '' P.extremePoints ℝ = (e '' P).extremePoints ℝ := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  have hseg (a b : V) : e '' openSegment ℝ a b = openSegment ℝ (e a) (e b) :=
    image_openSegment _ e.toAffineMap a b
  simp only [mem_extremePoints, e.surjective.forall, e.injective.mem_set_image,
    e.injective.eq_iff, ← hseg]
lemma canonicalVertices_map (e : V ≃ᵃ[ℝ] W) (P : Set V)
    (hP : (P.extremePoints ℝ).Finite) :
    canonicalVertices (e '' P) = (canonicalVertices P).map e.toEquiv.toEmbedding := by
  have himg : ((e '' P).extremePoints ℝ).Finite :=
    (affine_image_extremePoints e P) ▸ hP.image e
  apply Finset.coe_injective
  rw [coe_canonicalVertices himg, Finset.coe_map, coe_canonicalVertices hP]
  exact (affine_image_extremePoints e P).symm
lemma canonicalCenter_map (e : V ≃ᵃ[ℝ] W) (P : Set V)
    (hP : (P.extremePoints ℝ).Finite) (hne : (P.extremePoints ℝ).Nonempty) :
    canonicalCenter (e '' P) = e (canonicalCenter P) := by
  unfold canonicalCenter
  rw [canonicalVertices_map e P hP]
  apply vertexMean_map e
  apply Finset.coe_nonempty.mp
  rwa [coe_canonicalVertices hP]
variable [FiniteDimensional ℝ V]
noncomputable def CellData.canonical {P : Set V} (p : CellData P) : CellData P := by
  let v := polyhedronVertices p.a p.b
  have he : P = convexHull ℝ (v : Set V) := p.eq_cell.trans
    (cell_eq_convexHull_of_bounded p.a p.b (p.eq_cell ▸ p.bounded))
  have hv : v.Nonempty := Finset.coe_nonempty.mp
    (convexHull_nonempty_iff.mp (he ▸ (show P.Nonempty from ⟨p.center, p.center_mem⟩)))
  exact { p with
    center := canonicalCenter P
    center_mem := by rw [he]; exact canonicalCenter_mem_finiteHull hv
    center_support := by
      rw [he]
      exact fun f d hf he => canonicalCenter_supports_finiteHull hv f d hf he }
theorem exists_canonical_cellTriangulation (F : Finset (Set V))
    (hF : FiniteCellFamily F) :
    ∃ B : CellTriangulation F, B.complex.faces = chainFaces F canonicalCenter := by
  apply exists_cellTriangulation_chains F hF canonicalCenter
  intro P hP
  obtain ⟨p⟩ := hF.data P hP
  exact ⟨p.canonical, rfl⟩
omit [FiniteDimensional ℝ V] in
lemma chainFaces_affine_map (F : Finset (Set V)) (c : Set V → V)
    (d : Set W → W) (e : V ≃ᵃ[ℝ] W)
    (hcd : ∀ P ∈ F, d (e '' P) = e (c P))
    {s : Finset V} (hs : s ∈ chainFaces F c) :
    s.map e.toEquiv.toEmbedding ∈ chainFaces (F.image fun P => e '' P) d := by
  classical
  obtain ⟨t, hne, ht, hchain, rfl⟩ := hs
  refine ⟨t.image (fun P => e '' P), hne.image _, ?_, ?_, ?_⟩
  · exact Finset.image_subset_image ht
  · intro P hP Q hQ hne
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
    have he : P' ≠ Q' := fun h => hne (h ▸ rfl)
    rcases hchain hP' hQ' he with h | h
    · exact Or.inl (Set.image_mono h)
    · exact Or.inr (Set.image_mono h)
  · rw [Finset.map_eq_image, Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro P hP
    exact (hcd P (ht hP)).symm
omit [FiniteDimensional ℝ V] [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma chainFaces_restrict (F : Finset (Set V)) (c : Set V → V) (P : Set V)
    (hc : ∀ Q ∈ F, c Q ∈ P ↔ Q ⊆ P) (s : Finset V) :
    s ∈ chainFaces F c ∧ (s : Set V) ⊆ P ↔
      s ∈ chainFaces (F.filter fun Q => Q ⊆ P) c := by
  classical
  constructor
  · rintro ⟨⟨t, hne, hsub, hchain, rfl⟩, hP⟩
    refine ⟨t, hne, ?_, hchain, rfl⟩
    intro Q hQ
    exact Finset.mem_filter.mpr ⟨hsub hQ,
      (hc Q (hsub hQ)).mp (hP (Finset.mem_image_of_mem c hQ))⟩
  · rintro ⟨t, hne, hsub, hchain, rfl⟩
    refine ⟨⟨t, hne, hsub.trans (Finset.filter_subset _ _), hchain, rfl⟩, ?_⟩
    intro x hx
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hx
    have hh := Finset.mem_filter.mp (hsub hQ)
    exact (hc Q hh.1).mpr hh.2
omit [FiniteDimensional ℝ V] in
lemma canonical_chainFaces_affine_map (F : Finset (Set V)) (e : V ≃ᵃ[ℝ] W)
    (hvertices : ∀ P ∈ F, ∃ t : Finset V, t.Nonempty ∧ P = convexHull ℝ (t : Set V))
    {s : Finset V} (hs : s ∈ chainFaces F canonicalCenter) :
    s.map e.toEquiv.toEmbedding ∈
      chainFaces (F.image fun P => e '' P) canonicalCenter := by
  apply chainFaces_affine_map F canonicalCenter canonicalCenter e ?_ hs
  intro P hP
  obtain ⟨t, ht, rfl⟩ := hvertices P hP
  apply canonicalCenter_map e _ (finite_extremePoints_finiteHull t)
  exact (t.finite_toSet.isCompact_convexHull ℝ).extremePoints_nonempty
    (convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr ht))
end CanonicalCenters
section CanonicalFaceFamilies
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
noncomputable def cellFaces (P : Set V) : Finset (Set V) :=
  if h : {Q : Set V | Q.Nonempty ∧ SupportingFace Q P}.Finite then h.toFinset else ∅
noncomputable def faceClosure (A : Finset (Set V)) : Finset (Set V) :=
  A.biUnion cellFaces
lemma mem_cellFaces {P Q : Set V} (hP : ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    Q ∈ cellFaces P ↔ Q.Nonempty ∧ SupportingFace Q P := by
  obtain ⟨s, rfl⟩ := hP
  simp [cellFaces, finite_supportingFaces s]
lemma mem_faceClosure (A : Finset (Set V))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V)) (Q : Set V) :
    Q ∈ faceClosure A ↔ ∃ P ∈ A, Q.Nonempty ∧ SupportingFace Q P := by
  simp only [faceClosure, Finset.mem_biUnion]
  constructor
  · rintro ⟨P, hP, hQ⟩
    exact ⟨P, hP, (mem_cellFaces (hvertices P hP)).mp hQ⟩
  · rintro ⟨P, hP, hQ⟩
    exact ⟨P, hP, (mem_cellFaces (hvertices P hP)).mpr hQ⟩
lemma SupportingFace.affine_image {P Q : Set V} (h : SupportingFace Q P)
    (e : V ≃ᵃ[ℝ] W) : SupportingFace (e '' Q) (e '' P) := by
  obtain ⟨f, d, hf, he⟩ := h
  let f' : W →ᵃ[ℝ] ℝ := f.toAffineMap.comp e.symm.toAffineMap
  have hh (x : V) : f'.linear (e x) = f x - f' 0 := by
    have := affine_decomp_apply f' (e x)
    have heval : f' (e x) = f x := by simp [f']
    rw [heval] at this
    linarith
  refine ⟨f'.linear, d - f' 0, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    rw [hh]
    exact sub_le_sub_right (hf x hx) _
  · ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    simp only [e.injective.mem_set_image, Set.mem_inter_iff, Set.mem_ofPred_eq, hh]
    rw [he]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, sub_left_inj]
theorem faceClosure_isCellFamily (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P) :
    FiniteCellFamily (faceClosure A) := by
  have hmem := mem_faceClosure A hvertices
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨P, hP, hne, hQP⟩ := (hmem Q).mp hQ
    obtain ⟨p⟩ := hdata P hP
    obtain ⟨s, hs⟩ := hvertices P hP
    exact ⟨p.supportingFace s hs hQP hne⟩
  · intro Q hQ R hRQ hne
    obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
    obtain ⟨s, hs⟩ := hvertices P hP
    apply (hmem R).mpr
    refine ⟨P, hP, hne, ?_⟩
    rw [hs] at hQP ⊢
    exact hQP.trans_finite_hull hRQ
  · intro Q hQ R hR
    obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
    obtain ⟨S, hS, _, hRS⟩ := (hmem R).mp hR
    obtain ⟨s, hs⟩ := hvertices P hP
    obtain ⟨t, _, ht⟩ := (hs ▸ hQP).eq_convexHull_subset
    exact hQP.inter_of_parent_inter hRS (hinter P hP S hS) ht
variable [FiniteDimensional ℝ V]
theorem exists_canonical_parentTriangulation (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P) :
    ∃ B : CellTriangulation A,
      B.complex.faces = chainFaces (faceClosure A) canonicalCenter := by
  have hmem := mem_faceClosure A hvertices
  have hsubset : A ⊆ faceClosure A := by
    intro P hP
    apply (hmem P).mpr
    obtain ⟨p⟩ := hdata P hP
    exact ⟨P, hP, ⟨p.center, p.center_mem⟩, supportingFace_self P⟩
  obtain ⟨B, hB⟩ := exists_canonical_cellTriangulation (faceClosure A)
    (faceClosure_isCellFamily A hdata hvertices hinter)
  let C : CellTriangulation A := {
    complex := B.complex
    finite := B.finite
    space := by
      rw [B.space]
      ext x
      constructor
      · rintro ⟨Q, hQ, hxQ⟩
        obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
        exact ⟨P, hP, hQP.subset hxQ⟩
      · rintro ⟨P, hP, hxP⟩
        exact ⟨P, hsubset hP, hxP⟩
    trace := fun P hP => B.trace P (hsubset hP)
    carrier := by
      intro s hs
      obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
      obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
      exact ⟨P, hP, hsQ.trans hQP.subset⟩ }
  exact ⟨C, hB⟩
end CanonicalFaceFamilies
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
lemma affineIndependent_map_finset (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E)) :
    AffineIndependent ℝ ((↑) : s.map ⟨f, hf⟩ → F) := by
  have h := hs.map' f hf
  have he : f ∘ ((↑) : s → E) =
      ((↑) : s.map ⟨f, hf⟩ → F) ∘ (s.equivMap ⟨f, hf⟩) := rfl
  rw [he, affineIndependent_equiv] at h
  exact h
noncomputable def affineImageComplex (K : Geometry.SimplicialComplex ℝ E)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) : Geometry.SimplicialComplex ℝ F where
  faces := (fun s : Finset E => s.map ⟨f, hf⟩) '' K.faces
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    refine ⟨(K.nonempty_of_mem_faces ht).map, ?_⟩
    intro u hut hu
    let t' := t.filter (fun x => f x ∈ u)
    have he : t'.map ⟨f, hf⟩ = u := by
      ext y
      simp only [Finset.mem_map, Finset.mem_filter, t']
      constructor
      · rintro ⟨x, ⟨_, hu⟩, rfl⟩; exact hu
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp (hut hy)
        exact ⟨x, ⟨hx, hy⟩, rfl⟩
    refine ⟨t', K.down_closed ht (Finset.filter_subset _ _) ?_, he⟩
    exact Finset.map_nonempty.mp (he.symm ▸ hu)
  indep := by
    rintro s ⟨t, ht, rfl⟩
    exact affineIndependent_map_finset f hf (K.indep ht)
  inter_subset_convexHull := by
    rintro s t ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ x hx
    have hconv (a : Finset E) :
        convexHull ℝ (a.map ⟨f, hf⟩ : Set F) = f '' convexHull ℝ (a : Set E) := by
      rw [Finset.coe_map]
      exact (f.image_convexHull (a : Set E)).symm
    rw [hconv, hconv, ← Set.image_inter hf] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hh := K.inter_subset_convexHull hu hv hy
    have hab : ((u.map ⟨f, hf⟩ ∩ v.map ⟨f, hf⟩ : Finset F) : Set F) =
        ((u ∩ v).map ⟨f, hf⟩ : Set F) := by rw [Finset.map_inter]
    rw [← Finset.coe_inter, hab, hconv]
    exact ⟨y, by simpa only [Finset.coe_inter] using hh, rfl⟩
lemma affineImageComplex_finite (K : Geometry.SimplicialComplex ℝ E)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (hK : K.faces.Finite) :
    (affineImageComplex K f hf).faces.Finite := hK.image _
lemma affineImageComplex_space (K : Geometry.SimplicialComplex ℝ E)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) :
    (affineImageComplex K f hf).space = f '' K.space := by
  ext y
  simp only [Geometry.SimplicialComplex.mem_space_iff, affineImageComplex, Set.mem_image]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, hy⟩
    rw [Finset.coe_map] at hy
    change y ∈ convexHull ℝ (f '' (t : Set E)) at hy
    rw [← f.image_convexHull] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, ⟨t, ht, hx⟩, rfl⟩
  · rintro ⟨x, ⟨t, ht, hx⟩, rfl⟩
    refine ⟨t.map ⟨f, hf⟩, ⟨t, ht, rfl⟩, ?_⟩
    rw [Finset.coe_map]
    change f x ∈ convexHull ℝ (f '' (t : Set E))
    rw [← f.image_convexHull]
    exact ⟨x, hx, rfl⟩
lemma affine_image_extremePoints_injective (f : E →ᵃ[ℝ] F)
    (hf : Function.Injective f) (P : Set E) :
    f '' P.extremePoints ℝ = (f '' P).extremePoints ℝ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxP, hxe⟩ := mem_extremePoints_iff_left.mp hx
    apply mem_extremePoints_iff_left.mpr
    refine ⟨⟨x, hxP, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [← image_openSegment ℝ f a b, hf.mem_set_image] at hab
    exact congrArg f (hxe a ha b hb hab)
  · intro hy
    obtain ⟨hyP, hye⟩ := mem_extremePoints_iff_left.mp hy
    obtain ⟨x, hx, rfl⟩ := hyP
    refine ⟨x, mem_extremePoints_iff_left.mpr ⟨hx, ?_⟩, rfl⟩
    intro a ha b hb hab
    apply hf
    apply hye _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← image_openSegment ℝ f a b]
    exact ⟨x, hab, rfl⟩
noncomputable def affinePreimageComplex (K : Geometry.SimplicialComplex ℝ F)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) : Geometry.SimplicialComplex ℝ E where
  faces := (fun s : Finset E => s.map ⟨f, hf⟩) ⁻¹' K.faces
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨Finset.map_nonempty.mp (K.nonempty_of_mem_faces hs), ?_⟩
    intro t hts ht
    exact K.down_closed hs (Finset.map_subset_map.mpr hts) ht.map
  indep := by
    intro s hs
    apply AffineIndependent.of_comp f
    have h := (affineIndependent_equiv (s.equivMap ⟨f,hf⟩)).mpr (K.indep hs)
    exact h
  inter_subset_convexHull := by
    intro s t hs ht x hx
    have hconv (a : Finset E) :
        convexHull ℝ (a.map ⟨f, hf⟩ : Set F) = f '' convexHull ℝ (a : Set E) := by
      rw [Finset.coe_map]
      exact (f.image_convexHull (a : Set E)).symm
    have hx' : f x ∈ convexHull ℝ (s.map ⟨f,hf⟩ : Set F) ∩
        convexHull ℝ (t.map ⟨f,hf⟩ : Set F) := by
      rw [hconv, hconv]
      exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
    have hh := K.inter_subset_convexHull hs ht hx'
    rw [← Finset.coe_inter, ← Finset.map_inter, hconv, hf.mem_set_image] at hh
    simpa only [Finset.coe_inter] using hh
lemma affinePreimageComplex_finite (K : Geometry.SimplicialComplex ℝ F)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (hK : K.faces.Finite) :
    (affinePreimageComplex K f hf).faces.Finite := by
  exact hK.preimage (Finset.map_injective ⟨f, hf⟩).injOn
lemma affineImage_preimage_complex (K : Geometry.SimplicialComplex ℝ F)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    (hK : ∀ s ∈ K.faces, (s : Set F) ⊆ Set.range f) :
    affineImageComplex (affinePreimageComplex K f hf) f hf = K := by
  apply Geometry.SimplicialComplex.ext
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hs
    let t := s.preimage f hf.injOn
    have ht : t.map ⟨f,hf⟩ = s := by
      ext y
      simp only [Finset.mem_map, t, Finset.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hy
        obtain ⟨x, rfl⟩ := hK s hs hy
        exact ⟨x, hy, rfl⟩
    exact ⟨t, show t.map ⟨f,hf⟩ ∈ K.faces by rwa [ht], ht⟩
end BassTrace.Sparse.Cuts
end OAI
end
section
/- Internal experiment on OpenAI openai/math@3344da5 (mo-178849). -/
namespace OAI.BassTrace.Sparse.Cuts.ActiveFlags
open Set Finset
open scoped Classical
variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]
variable (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)

def face (A : Finset I) : Set V := {x ∈ cell a b | ∀ i ∈ A, a i x = b i}

lemma center_mem [FiniteDimensional ℝ V] (hb : Bornology.IsBounded (cell a b))
    (A : Finset I) (hne : (face a b A).Nonempty) : canonicalCenter (face a b A) ∈ face a b A := by
  let f : I ⊕ A → V →ₗ[ℝ] ℝ := Sum.elim a (fun i => -a i.val)
  let d : I ⊕ A → ℝ := Sum.elim b (fun i => -b i.val)
  have he : face a b A = cell f d := by
    ext x
    constructor
    · rintro ⟨hx, ha⟩ (i | i)
      · exact hx i
      · change -(a i.val x) ≤ -b i.val
        rw [ha i.val i.property]
    · intro hx
      exact ⟨fun i => hx (.inl i), fun i hi => le_antisymm (hx (.inl i))
        (neg_le_neg_iff.mp (hx (.inr ⟨i, hi⟩)))⟩
  have hb' : Bornology.IsBounded (cell f d) := he ▸ hb.subset (show face a b A ⊆ cell a b from fun _ h => h.1)
  rw [he, cell_eq_convexHull_of_bounded f d hb'] at hne ⊢
  exact canonicalCenter_mem_finiteHull (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp hne))

/-- The face centroid hulls indexed by flags cover every active face, including all lower-dimensional cells. -/
theorem cover [FiniteDimensional ℝ V] (hb : Bornology.IsBounded (cell a b))
    (A : Finset I) {x : V} (hx : x ∈ face a b A) :
    ∃ T : Finset (Finset I), A ∈ T ∧ (∀ B ∈ T, A ⊆ B ∧ (face a b B).Nonempty) ∧
      IsChain (· ⊆ ·) (T : Set (Finset I)) ∧
      AffineIndependent ℝ ((↑) : ((fun B => canonicalCenter (face a b B)) '' (T : Set (Finset I))) → V) ∧
      x ∈ convexHull ℝ ((fun B => canonicalCenter (face a b B)) '' (T : Set (Finset I))) := by
  classical
  let c := canonicalCenter (face a b A)
  have hc : c ∈ face a b A := center_mem a b hb A ⟨x,hx⟩
  by_cases h : x = c
  · refine ⟨{A}, by simp, ?_, ?_, ?_, ?_⟩
    · simpa using And.intro (Finset.Subset.refl A) (show (face a b A).Nonempty from ⟨x,hx⟩)
    · simp
    · have : Subsingleton ((fun B => canonicalCenter (face a b B)) '' (({A} : Finset (Finset I)) : Set (Finset I))) := by
        rw [Finset.coe_singleton, Set.image_singleton]
        infer_instance
      exact affineIndependent_of_subsingleton _ _
    · simpa [c] using h
  obtain ⟨i,t,_,hy,hi,hl,hs⟩ := bounded_exists_ray_boundary a b hb hc.1 hx.1 h
  have hn : i ∉ A := fun hm => hl.ne (hc.2 i hm)
  have hy' : c + t • (x - c) ∈ face a b (insert i A) := by
    refine ⟨hy, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · simp [map_add, map_smul, map_sub, hc.2 j hj, hx.2 j hj]
  obtain ⟨T,_,hT,hch,hind,hull⟩ := cover hb (insert i A) hy'
  have sub (B) (hB : B ∈ T) : A ⊆ B := (Finset.subset_insert _ _).trans (hT B hB).1
  refine ⟨insert A T, Finset.mem_insert_self .., ?_, ?_, ?_, ?_⟩
  · intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact ⟨Finset.Subset.rfl, x,hx⟩
    · exact ⟨sub B hB,(hT B hB).2⟩
  · rw [Finset.coe_insert]
    exact hch.insert fun B hB _ => Or.inl (sub B hB)
  · rw [Finset.coe_insert, Set.image_insert_eq]
    apply affineIndependent_insert hind
    intro hspan
    apply hl.ne
    apply linear_eq_on_affineSpan (a i) _ hspan
    rintro _ ⟨B,hB,rfl⟩
    exact (center_mem a b hb B (hT B hB).2).2 i ((hT B hB).1 (Finset.mem_insert_self ..))
  · apply (convex_convexHull ℝ _).segment_subset _ _ hs
    · exact subset_convexHull _ _ ⟨A, Finset.mem_insert_self .., rfl⟩
    · exact convexHull_mono (Set.image_mono (by exact_mod_cast Finset.subset_insert A T)) hull
termination_by Fintype.card I - A.card
decreasing_by
  rw [Finset.card_insert_of_notMem hn]
  have hh := Finset.card_le_univ (insert i A)
  rw [Finset.card_insert_of_notMem hn] at hh
  omega

/-- On an actual signed clip, use geometric faces as labels: equal active-set presentations
collapse in `U`. Every covering simplex lies entirely in the clip. -/
theorem signed_cover {J : Type*} [Fintype J] [FiniteDimensional ℝ V]
    (hb : Bornology.IsBounded (cell a b)) (g : J → V →ₗ[ℝ] ℝ) (d : J → ℝ) (σ : J → Bool)
    {x : V} (hx : x ∈ cutCell (cell a b) g d σ) :
    let f := Sum.elim a (signedForm g σ)
    let e := Sum.elim b (signedBound d σ)
    ∃ U : Finset (Set V), (∀ P ∈ U, P.Nonempty ∧ ∃ B, P = face f e B) ∧
      IsChain (· ⊆ ·) (U : Set (Set V)) ∧
      AffineIndependent ℝ ((↑) : (canonicalCenter '' (U : Set (Set V))) → V) ∧
      x ∈ convexHull ℝ (canonicalCenter '' (U : Set (Set V))) ∧
      convexHull ℝ (canonicalCenter '' (U : Set (Set V))) ⊆ cutCell (cell a b) g d σ := by
  classical
  dsimp only
  let f := Sum.elim a (signedForm g σ)
  let e := Sum.elim b (signedBound d σ)
  have he : cutCell (cell a b) g d σ = cell f e := by
    ext y
    exact ⟨fun ⟨h,k⟩ => fun i => by cases i with | inl i => exact h i | inr j => exact k j, fun h => ⟨fun i => h (.inl i), fun j => h (.inr j)⟩⟩
  have hb' : Bornology.IsBounded (cell f e) := he ▸ hb.subset Set.inter_subset_left
  have hx' : x ∈ face f e ∅ := ⟨he ▸ hx, by simp⟩
  obtain ⟨T,_,ht,hch,hi,hh⟩ := cover f e hb' ∅ hx'
  refine ⟨T.image (face f e), ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hP
    exact ⟨(ht B hB).2,B,rfl⟩
  · intro P hP Q hQ hpq
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hQ
    have mono {D F : Finset (I ⊕ J)} (h : D ⊆ F) : face f e F ⊆ face f e D :=
      fun _ hy => ⟨hy.1, fun i hD => hy.2 i (h hD)⟩
    exact (hch hB hC (fun h => hpq (congrArg _ h))).elim (fun h => Or.inr (mono h))
      (fun h => Or.inl (mono h))
  · have eqv : canonicalCenter '' ((T.image (face f e) : Finset _) : Set (Set V)) = (fun B => canonicalCenter (face f e B)) '' (T : Set _) := by rw [Finset.coe_image, Set.image_image]
    rw [eqv]
    exact hi
  · simpa only [Finset.coe_image, Set.image_image] using hh
  · rw [he]
    apply convexHull_min _ (convex_cell f e)
    rintro _ ⟨P,hP,rfl⟩
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hP
    exact (center_mem f e hb' B (ht B hB).2).1

end OAI.BassTrace.Sparse.Cuts.ActiveFlags
end
section
/- Intrinsic extension of the signed_flag_inter proof in t_b4031be9/Unique.lean.
   Underlying geometry: OpenAI openai/math@3344da5. -/
namespace OAI.BassTrace.Sparse.Cuts.Intrinsic
open Set
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (F : Finset (Set V)) (hF : FiniteCellFamily F)
include hF in
private lemma finiteHull {P : Set V} (hp : P ∈ F) : ∃ u : Finset V, u.Nonempty ∧ P = convexHull ℝ (u : Set V) := by
  obtain ⟨p⟩ := hF.data P hp
  have h := p.eq_cell.trans (cell_eq_convexHull_of_bounded p.a p.b (p.eq_cell ▸ p.bounded))
  exact ⟨_,Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp (h ▸ (show P.Nonempty from ⟨_,p.center_mem⟩))),h⟩
include hF in
private lemma separate {P Q : Set V} (hp : P ∈ F) (hq : Q ∈ F)
    {y z : V} (hyp : y ∈ P) (hyq : y ∈ Q) (hzp : z ∈ P) (hzq : z ∉ Q) :
    ∃ (f : V →ₗ[ℝ] ℝ) (d : ℝ), (∀ w ∈ P, f w ≤ d) ∧ f y = d ∧ f z < d := by
  obtain ⟨f,d,h,e⟩ := hF.inter P hp Q hq
  exact ⟨f,d,h,(e.subset ⟨hyp,hyq⟩).2,lt_of_le_of_ne (h z hzp) (fun hz => hzq (e.symm.subset ⟨hzp,hz⟩).2)⟩
include hF in
private lemma center_out {P Q : Set V} (hp : P ∈ F) (hq : Q ∈ F) (hn : ¬ P ⊆ Q) : canonicalCenter P ∉ Q := by
  obtain ⟨u,hu,he⟩ := finiteHull F hF hp
  have hc : canonicalCenter P ∈ P := he ▸ canonicalCenter_mem_finiteHull hu
  intro h
  obtain ⟨z,hz,hzq⟩ := Set.not_subset.mp hn
  obtain ⟨f,d,hle,heq,hlt⟩ := separate F hF hp hq hc h hz hzq
  rw [he] at hle heq hz
  exact hlt.ne (canonicalCenter_supports_finiteHull hu f d hle heq z hz)

open scoped Classical
private abbrev C (S : Finset (Set V)) := canonicalCenter '' (S : Set (Set V))
private abbrev H (S : Finset (Set V)) := convexHull ℝ (C S)
private def Good (S : Finset (Set V)) := (∀ P ∈ S, P ∈ F) ∧ IsChain (· ⊆ ·) (S : Set (Set V))
private lemma top {S : Finset (Set V)} (hs : Good F S) (hn : S.Nonempty) : ∃ P ∈ S, ∀ Q ∈ S, Q ⊆ P := by
  obtain ⟨P,h⟩ := S.exists_maximal hn
  refine ⟨P,h.1,fun Q hq => ?_⟩
  by_cases he : Q = P
  · exact he.subset
  · exact (hs.2 hq h.1 he).elim id (h.2 hq)
include hF in
private lemma hull_sub {S : Finset (Set V)} (hs : Good F S) {P : Set V} (hp : P ∈ F)
    (hle : ∀ Q ∈ S, Q ⊆ P) : H S ⊆ P := by
  obtain ⟨u,_,he⟩ := finiteHull F hF hp
  apply convexHull_min _ (he ▸ convex_convexHull ℝ _)
  rintro _ ⟨Q,hq,rfl⟩
  obtain ⟨v,hv,hv'⟩ := finiteHull F hF (hs.1 Q hq)
  exact hle Q hq (hv' ▸ canonicalCenter_mem_finiteHull hv)
private lemma erase_good {S : Finset (Set V)} (hs : Good F S) (P : Set V) : Good F (S.erase P) :=
  ⟨fun Q hq => hs.1 Q (Finset.mem_of_mem_erase hq), fun _ h _ k => hs.2 (Finset.mem_of_mem_erase h) (Finset.mem_of_mem_erase k)⟩
include hF in
private lemma erase_apex {S : Finset (Set V)} (hs : Good F S) {P Q : Set V}
    (hp : P ∈ S) (hm : ∀ R ∈ S, R ⊆ P) (hq : Q ∈ F) (hn : ¬ P ⊆ Q)
    {x : V} (hx : x ∈ H S) (hxq : x ∈ Q) : x ∈ H (S.erase P) := by
  have hP := hs.1 P hp
  have hsub := hull_sub F hF hs hP hm
  obtain ⟨u,hu,he⟩ := finiteHull F hF hP
  obtain ⟨f,d,hle,heq,hlt⟩ := separate F hF hP hq (hsub hx) hxq
    (he ▸ canonicalCenter_mem_finiteHull hu) (center_out F hF hP hq hn)
  have h := convexHull_inter_supporting (C S) f d (fun z hz => hle z (hsub (subset_convexHull ℝ _ hz)))
  apply convexHull_mono _ (h.subset ⟨hx,heq⟩)
  rintro _ ⟨⟨R,hr,rfl⟩,hR⟩
  refine ⟨R,Finset.mem_erase.mpr ⟨?_,hr⟩,rfl⟩
  rintro rfl
  exact hlt.ne hR

private abbrev Support (P : Set V) := {p : (V →ₗ[ℝ] ℝ) × ℝ // ∀ w ∈ P, p.1 w ≤ p.2}
include hF in
private lemma radial_erase {S : Finset (Set V)} (hs : Good F S) {P : Set V}
    (hp : P ∈ S) (hm : ∀ R ∈ S, R ⊆ P) : H (S.erase P) ⊆
    radialBoundary (fun i : Support P => i.val.1) (fun i => i.val.2) (canonicalCenter P) := by
  intro y hy
  have hS := erase_good F hs P
  have hn : (S.erase P).Nonempty := by
    by_contra! he
    simp [H,C,he] at hy
  obtain ⟨Q,hq,hmax⟩ := top F hS hn
  have hsub := hm Q (Finset.mem_of_mem_erase hq)
  have hne : ¬ P ⊆ Q := fun h => (Finset.ne_of_mem_erase hq) (Subset.antisymm hsub h)
  have hyq := hull_sub F hF hS (hS.1 Q hq) hmax hy
  have hP := hs.1 P hp
  obtain ⟨v,hv,he⟩ := finiteHull F hF hP
  obtain ⟨f,d,hle,heq,hlt⟩ := separate F hF hP (hS.1 Q hq) (hsub hyq) hyq
    (he ▸ canonicalCenter_mem_finiteHull hv) (center_out F hF hP (hS.1 Q hq) hne)
  exact ⟨fun i => i.property _ (hsub hyq), ⟨⟨(f,d),hle⟩,heq,hlt⟩⟩

private lemma centers_erase {S : Finset (Set V)} {P : Set V} (hp : P ∈ S) :
    C S = insert (canonicalCenter P) (C (S.erase P)) := by
  unfold C
  rw [← Set.image_insert_eq, ← Finset.coe_insert, Finset.insert_erase hp]

private lemma cerase (S : Finset (Set V)) (P : Set V) : C (S.erase P) ⊆ C S :=
  Set.image_mono (fun _ h => Finset.mem_of_mem_erase h)

include hF in
private theorem inter_sub (S T : Finset (Set V)) (hs : Good F S) (ht : Good F T) :
    H S ∩ H T ⊆ convexHull ℝ (C S ∩ C T) := by
  classical
  by_cases hS : S.Nonempty
  · by_cases hT : T.Nonempty
    · obtain ⟨P,hp,hm⟩ := top F hs hS
      obtain ⟨Q,hq,hk⟩ := top F ht hT
      by_cases hpq : P ⊆ Q
      · by_cases hqp : Q ⊆ P
        · have he := Subset.antisymm hpq hqp
          subst Q
          have ih := inter_sub (S.erase P) (T.erase P) (erase_good F hs P) (erase_good F ht P)
          have k := cone_hull_inter _ _ (radial_erase F hF hs hp hm) (radial_erase F hF ht hq hk) ih
          unfold H
          rw [centers_erase hp,centers_erase hq,← Set.insert_inter_distrib]
          exact k.subset
        · have ih := inter_sub S (T.erase Q) hs (erase_good F ht Q)
          intro x hx
          have he := erase_apex F hF ht hq hk (hs.1 P hp) hqp hx.2 (hull_sub F hF hs (hs.1 P hp) hm hx.1)
          exact convexHull_mono (Set.inter_subset_inter_right _ (cerase T Q)) (ih ⟨hx.1,he⟩)
      · have ih := inter_sub (S.erase P) T (erase_good F hs P) ht
        intro x hx
        have he := erase_apex F hF hs hp hm (ht.1 Q hq) hpq hx.1 (hull_sub F hF ht (ht.1 Q hq) hk hx.2)
        exact convexHull_mono (Set.inter_subset_inter_left _ (cerase S P)) (ih ⟨he,hx.2⟩)
    · simp [H,C,Finset.not_nonempty_iff_eq_empty.mp hT]
  · simp [H,C,Finset.not_nonempty_iff_eq_empty.mp hS]
termination_by S.card + T.card
decreasing_by all_goals (have h₁ := Finset.card_erase_lt_of_mem hp; have h₂ := Finset.card_erase_lt_of_mem hq; omega)

/- Exact common-face intersection; the flags may use different sign charts. -/
include hF in
theorem signed_flag_inter (S T : Finset (Set V))
    (hs : ∀ P ∈ S, P ∈ F) (ht : ∀ P ∈ T, P ∈ F)
    (hS : IsChain (· ⊆ ·) (S : Set (Set V))) (hT : IsChain (· ⊆ ·) (T : Set (Set V))) :
    convexHull ℝ (canonicalCenter '' (S : Set (Set V))) ∩ convexHull ℝ (canonicalCenter '' (T : Set (Set V))) =
      convexHull ℝ ((canonicalCenter '' (S : Set (Set V))) ∩ (canonicalCenter '' (T : Set (Set V)))) :=
  Subset.antisymm (inter_sub F hF S T ⟨hs,hS⟩ ⟨ht,hT⟩)
    (Set.subset_inter (convexHull_mono Set.inter_subset_left) (convexHull_mono Set.inter_subset_right))


include hF in
private lemma independent (S : Finset (Set V)) (hs : Good F S) :
    AffineIndependent ℝ ((↑) : C S → V) := by
  classical
  by_cases hn : S.Nonempty
  · obtain ⟨P,hp,hm⟩ := top F hs hn
    have hS := erase_good F hs P
    have ih := independent (S.erase P) hS
    rw [centers_erase hp]
    apply affineIndependent_insert ih
    intro hx
    by_cases hn' : (S.erase P).Nonempty
    · obtain ⟨Q,hq,hk⟩ := top F hS hn'
      have hqP := hm Q (Finset.mem_of_mem_erase hq)
      have hout := center_out F hF (hs.1 P hp) (hS.1 Q hq) (fun h => (Finset.ne_of_mem_erase hq) (Subset.antisymm hqP h))
      obtain ⟨f,b,h,e⟩ := hF.inter P (hs.1 P hp) Q (hS.1 Q hq)
      have hsub := hull_sub F hF hS (hS.1 Q hq) hk
      have hc := (Classical.choice (hF.data P (hs.1 P hp))).canonical.center_mem
      apply hout
      apply (e.symm.subset ⟨hc,?_⟩).2
      apply linear_eq_on_affineSpan f _ hx
      intro x hxx
      have hq' := hsub (subset_convexHull ℝ _ hxx)
      exact (e.subset ⟨hqP hq',hq'⟩).2
    · simp [C,Finset.not_nonempty_iff_eq_empty.mp hn'] at hx
      exact hx
  · have he : C S = ∅ := by simp [C,Finset.not_nonempty_iff_eq_empty.mp hn]
    rw [he]
    exact affineIndependent_of_subsingleton _ _
termination_by S.card
decreasing_by exact Finset.card_erase_lt_of_mem hp

private theorem face_support {I : Type*} [Fintype I] (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (A : Finset I) :
    SupportingFace (ActiveFlags.face a b A) (cell a b) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa [ActiveFlags.face] using supportingFace_self (cell a b)
  | @insert i A hi ih =>
    have h : SupportingFace (cell a b ∩ {x | a i x = b i}) (cell a b) := ⟨a i,b i,fun _ hx => hx i,rfl⟩
    convert h.supporting_inter ih using 1
    ext x; simp [ActiveFlags.face]


include hF in
noncomputable def complex : Geometry.SimplicialComplex ℝ V where
  faces := chainFaces F canonicalCenter
  indep := by
    rintro s ⟨S,_,hsub,hchain,rfl⟩
    change AffineIndependent ℝ ((↑) : (↑(S.image canonicalCenter) : Set V) → V)
    rw [Finset.coe_image]
    exact independent F hF S ⟨fun _ => @hsub _,hchain⟩
  inter_subset_convexHull := by
    rintro s t ⟨S,_,h1,h2,rfl⟩ ⟨T,_,h3,h4,rfl⟩
    simpa only [Finset.coe_image] using (signed_flag_inter F hF S T (fun _ => @h1 _) (fun _ => @h3 _) h2 h4).subset
  isRelLowerSet_faces := by
    classical
    rintro s ⟨S,hn,hsub,hch,rfl⟩
    refine ⟨hn.image _,?_⟩
    intro t ht hne
    let U := S.filter (fun Q => canonicalCenter Q ∈ t)
    have eq : U.image canonicalCenter = t := by
      ext v; constructor
      · rintro hv
        obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp hQ).2
      · intro hv
        obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp (ht hv)
        exact Finset.mem_image.mpr ⟨Q,Finset.mem_filter.mpr ⟨hQ,hv⟩,rfl⟩
    have hu := Finset.filter_subset (fun Q => canonicalCenter Q ∈ t) S
    exact ⟨U,Finset.image_nonempty.mp (eq.symm ▸ hne),hu.trans hsub, fun _ hx _ hy => hch (hu hx) (hu hy),eq.symm⟩

include hF in
theorem realization : ∃ B : CellTriangulation F, B.complex.faces = chainFaces F canonicalCenter := by
  classical
  let K := complex F hF
  have carrier : ∀ s ∈ K.faces, ∃ P ∈ F, convexHull ℝ (s : Set V) ⊆ P := by
    rintro s ⟨S,hn,hsub,hch,rfl⟩
    have hs : Good F S := ⟨fun _ => @hsub _,hch⟩
    obtain ⟨P,hp,hm⟩ := top F hs hn
    exact ⟨P,hsub hp,by simpa only [Finset.coe_image] using hull_sub F hF hs (hsub hp) hm⟩
  refine ⟨⟨K,?_,?_,?_,carrier⟩,rfl⟩
  · apply ((F.powerset.image (fun S => S.image canonicalCenter)).finite_toSet).subset
    rintro s ⟨S,_,hs,_,rfl⟩
    exact Finset.mem_image.mpr ⟨_,Finset.mem_powerset.mpr hs,rfl⟩
  · ext x; constructor
    · intro hx
      obtain ⟨s,hs,hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
      obtain ⟨P,hP,sub⟩ := carrier s hs
      exact ⟨P,hP,sub hx⟩
    · rintro ⟨P,hP,hx⟩
      obtain ⟨p⟩ := hF.data P hP
      let g : Empty → V →ₗ[ℝ] ℝ := Empty.elim
      let d : Empty → ℝ := Empty.elim
      let e : Empty → Bool := Empty.elim
      have hx' : x ∈ cutCell (cell p.a p.b) g d e := ⟨p.eq_cell ▸ hx,fun j => j.elim⟩
      obtain ⟨S,hS,hch,_,hh,_⟩ := ActiveFlags.signed_cover p.a p.b (p.eq_cell ▸ p.bounded) g d e hx'
      have hn : S.Nonempty := by by_contra! h; simp [h] at hh
      refine Geometry.SimplicialComplex.mem_space_iff.mpr ⟨S.image canonicalCenter,⟨S,hn,?_,hch,rfl⟩,by simpa only [Finset.coe_image] using hh⟩
      intro Q hQ
      obtain ⟨hne,A,eq⟩ := hS Q hQ
      apply hF.faces P hP Q _ hne
      rw [eq]
      have h := face_support (Sum.elim p.a (signedForm g e)) (Sum.elim p.b (signedBound d e)) A
      convert h using 1
      refine p.eq_cell.trans ?_
      ext y; constructor
      · intro hy j; cases j with
        | inl i => exact hy i
        | inr j => exact j.elim
      · intro hy i; exact hy (.inl i)
  · intro Q hQ s hs
    obtain ⟨P,hP,hsub⟩ := carrier s hs
    obtain ⟨f,b,h,e⟩ := hF.inter P hP Q hQ
    exact hull_inter_of_supporting_eq s P Q hsub f b h e

end OAI.BassTrace.Sparse.Cuts.Intrinsic
end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
open Set Finset
open scoped Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
section EmbeddingNaturality
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
lemma vertexMean_affine_map (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {s : Finset V} (hs : s.Nonempty) :
    vertexMean (s.map ⟨f, hf⟩) = f (vertexMean s) := by
  rw [vertexMean_eq_centroid hs, vertexMean_eq_centroid hs.map, Finset.centroid_map]
  simp only [Finset.centroid_def]
  convert (s.map_affineCombination id (s.centroidWeights ℝ)
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs) f).symm using 1
  rfl
lemma canonicalVertices_affine_map (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (P : Set V) (hP : (P.extremePoints ℝ).Finite) :
    canonicalVertices (f '' P) = (canonicalVertices P).map ⟨f, hf⟩ := by
  have himg : ((f '' P).extremePoints ℝ).Finite :=
    (affine_image_extremePoints_injective f hf P) ▸ hP.image f
  apply Finset.coe_injective
  rw [coe_canonicalVertices himg, Finset.coe_map, coe_canonicalVertices hP]
  exact (affine_image_extremePoints_injective f hf P).symm
lemma canonicalCenter_affine_map (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (P : Set V) (hP : (P.extremePoints ℝ).Finite) (hne : (P.extremePoints ℝ).Nonempty) :
    canonicalCenter (f '' P) = f (canonicalCenter P) := by
  unfold canonicalCenter
  rw [canonicalVertices_affine_map f hf P hP]
  apply vertexMean_affine_map f hf
  apply Finset.coe_nonempty.mp
  rwa [coe_canonicalVertices hP]
lemma SupportingFace.affine_image_injective {P Q : Set V} (h : SupportingFace Q P)
    (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    SupportingFace (f '' Q) (f '' P) := by
  obtain ⟨a, d, ha, he⟩ := h
  obtain ⟨g, hg⟩ := f.linear.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (f.linear_injective_iff.mpr hf))
  let a' : W →ₗ[ℝ] ℝ := a.comp g
  have hh (x : V) : a' (f x) = a x + a' (f 0) := by
    have hd := affine_decomp_apply (a'.toAffineMap.comp f) x
    have hgx := LinearMap.congr_fun hg x
    change g (f.linear x) = x at hgx
    simpa [a', hgx] using hd
  refine ⟨a', d + a' (f 0), ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    rw [hh]
    linarith [ha x hx]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [he] at hx
      refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
      change a' (f x) = d + a' (f 0)
      rw [hh x]
      exact congrArg (fun z => z + a' (f 0)) hx.2
    · rintro ⟨⟨x, hx, rfl⟩, hax⟩
      refine ⟨x, ?_, rfl⟩
      rw [he]
      change a' (f x) = d + a' (f 0) at hax
      rw [hh x] at hax
      exact ⟨hx, add_right_cancel hax⟩
lemma SupportingFace.affine_preimage {P Q : Set W} (h : SupportingFace Q P)
    (f : V →ᵃ[ℝ] W) : SupportingFace (f ⁻¹' Q) (f ⁻¹' P) := by
  obtain ⟨a, d, ha, he⟩ := h
  let a' : V →ₗ[ℝ] ℝ := a.comp f.linear
  have hh (x : V) : a (f x) = a' x + a (f 0) :=
    affine_decomp_apply (a.toAffineMap.comp f) x
  refine ⟨a', d - a (f 0), ?_, ?_⟩
  · intro x hx
    have ht := ha (f x) hx
    rw [hh] at ht
    linarith
  · ext x
    simp only [Set.mem_preimage, he, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [hh x]
    exact and_congr_right (fun _ => eq_sub_iff_add_eq.symm)
lemma cellFaces_affine_map_injective (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P : Set V} (hP : ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    cellFaces (f '' P) = (cellFaces P).image (fun Q => f '' Q) := by
  have himg : ∃ s : Finset W, f '' P = convexHull ℝ (s : Set W) := by
    obtain ⟨s, rfl⟩ := hP
    refine ⟨s.map ⟨f, hf⟩, ?_⟩
    rw [Finset.coe_map]
    exact f.image_convexHull (s : Set V)
  ext Q
  rw [mem_cellFaces himg, Finset.mem_image]
  constructor
  · rintro ⟨hne, hface⟩
    have hsub := hface.subset
    have he : f '' (f ⁻¹' Q) = Q := Set.image_preimage_eq_of_subset (hsub.trans (Set.image_subset_range f P))
    refine ⟨f ⁻¹' Q, (mem_cellFaces hP).mpr ⟨?_, ?_⟩, he⟩
    · obtain ⟨y, hy⟩ := hne
      obtain ⟨x, _, rfl⟩ := hsub hy
      exact ⟨x, hy⟩
    · have hh := hface.affine_preimage f
      simpa only [hf.preimage_image] using hh
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨hne, hface⟩ := (mem_cellFaces hP).mp hR
    exact ⟨hne.image _, hface.affine_image_injective f hf⟩
lemma RespectsSet.affine_image {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (h : RespectsSet K P) (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    RespectsSet (affineImageComplex K f hf) (f '' P) := by
  rintro s ⟨t, ht, rfl⟩
  rw [Finset.coe_map]
  change convexHull ℝ (f '' (t : Set V)) ∩ f '' P =
    convexHull ℝ ((f '' (t : Set V)) ∩ f '' P)
  rw [← f.image_convexHull, ← Set.image_inter hf, h t ht,
    f.image_convexHull, Set.image_inter hf]
noncomputable def CellTriangulation.affineImage {A : Finset (Set V)}
    (B : CellTriangulation A) (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    CellTriangulation (A.image fun P => f '' P) where
  complex := affineImageComplex B.complex f hf
  finite := affineImageComplex_finite B.complex f hf B.finite
  space := by
    rw [affineImageComplex_space, B.space]
    ext y
    constructor
    · rintro ⟨x, ⟨P, hP, hx⟩, rfl⟩
      exact ⟨f '' P, Finset.mem_image_of_mem _ hP, x, hx, rfl⟩
    · rintro ⟨Q, hQ, hy⟩
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, ⟨P, hP, hx⟩, rfl⟩
  trace := by
    rintro Q hQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    exact (B.trace P hP).affine_image f hf
  carrier := by
    rintro s ⟨t, ht, rfl⟩
    obtain ⟨P, hP, htP⟩ := B.carrier t ht
    refine ⟨f '' P, Finset.mem_image_of_mem _ hP, ?_⟩
    rw [Finset.coe_map]
    change convexHull ℝ (f '' (t : Set V)) ⊆ f '' P
    rw [← f.image_convexHull]
    exact Set.image_mono htP
lemma faceClosure_affine_map_injective (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (A : Finset (Set V))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    faceClosure (A.image fun P => f '' P) =
      (faceClosure A).image (fun P => f '' P) := by
  unfold faceClosure
  rw [Finset.biUnion_image, Finset.image_biUnion]
  apply Finset.biUnion_congr rfl
  intro P hP
  exact cellFaces_affine_map_injective f hf (hvertices P hP)
end EmbeddingNaturality
section CanonicalCuts
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {J : Type*} [Fintype J]
theorem intrinsic_parentTriangulation (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P) :
    ∃ B : CellTriangulation A,
      B.complex.faces = chainFaces (faceClosure A) canonicalCenter := by
  have hmem := mem_faceClosure A hvertices
  have hsubset : A ⊆ faceClosure A := by
    intro P hP
    apply (hmem P).mpr
    obtain ⟨p⟩ := hdata P hP
    exact ⟨P, hP, ⟨p.center, p.center_mem⟩, supportingFace_self P⟩
  obtain ⟨B, hB⟩ := Intrinsic.realization (faceClosure A)
    (faceClosure_isCellFamily A hdata hvertices hinter)
  let C : CellTriangulation A := {
    complex := B.complex
    finite := B.finite
    space := by
      rw [B.space]
      ext x
      constructor
      · rintro ⟨Q, hQ, hxQ⟩
        obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
        exact ⟨P, hP, hQP.subset hxQ⟩
      · rintro ⟨P, hP, hxP⟩
        exact ⟨P, hsubset hP, hxP⟩
    trace := fun P hP => B.trace P (hsubset hP)
    carrier := by
      intro s hs
      obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
      obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
      exact ⟨P, hP, hsQ.trans hQP.subset⟩ }
  exact ⟨C, hB⟩

theorem exists_canonical_cutTriangulation (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P)
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) :
    ∃ B : CellTriangulation A,
      B.complex.faces = chainFaces (faceClosure (cutParents A a b)) canonicalCenter ∧
      ∀ P ∈ A, ∀ s : J → Bool, RespectsSet B.complex (cutCell P a b s) := by
  classical
  let C := cutParents A a b
  have hCdata : ∀ Q ∈ C, Nonempty (CellData Q) := by
    intro Q hQ
    obtain ⟨P, hP, s, rfl, hne⟩ := (mem_cutParents A a b Q).mp hQ
    obtain ⟨p⟩ := hdata P hP
    exact (cutCell_nonempty_data p a b s hne).1
  have hCvertices : ∀ Q ∈ C, ∃ v : Finset V, Q = convexHull ℝ (v : Set V) := by
    intro Q hQ
    obtain ⟨P, hP, s, rfl, hne⟩ := (mem_cutParents A a b Q).mp hQ
    obtain ⟨p⟩ := hdata P hP
    exact (cutCell_nonempty_data p a b s hne).2
  have hCinter : ∀ Q ∈ C, ∀ R ∈ C, SupportingFace (Q ∩ R) Q := by
    intro Q hQ R hR
    obtain ⟨P, hP, s, rfl, _⟩ := (mem_cutParents A a b Q).mp hQ
    obtain ⟨P', hP', t, rfl, _⟩ := (mem_cutParents A a b R).mp hR
    exact cutCell_inter_parents_supporting (hinter P hP P' hP') a b s t
  obtain ⟨B, hB⟩ := intrinsic_parentTriangulation C hCdata hCvertices hCinter
  have hspace : familySpace C = familySpace A := by
    ext x
    constructor
    · rintro ⟨Q, hQ, hxQ⟩
      obtain ⟨P, hP, s, rfl, _⟩ := (mem_cutParents A a b Q).mp hQ
      exact ⟨P, hP, hxQ.1⟩
    · rintro ⟨P, hP, hxP⟩
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ((cutCell_cover P a b).subset hxP)
      exact ⟨cutCell P a b s, (mem_cutParents A a b _).mpr ⟨P, hP, s, rfl, x, hs⟩, hs⟩
  have htrace : ∀ P ∈ A, RespectsSet B.complex P := by
    intro P hP
    apply B.respects_of_carrier
    intro Q hQ
    obtain ⟨P', hP', s, rfl, _⟩ := (mem_cutParents A a b Q).mp hQ
    exact (hinter P' hP' P hP).inter_restrict Set.inter_subset_left
  have hcarrier : ∀ s ∈ B.complex.faces,
      ∃ P ∈ A, convexHull ℝ (s : Set V) ⊆ P := by
    intro s hs
    obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
    obtain ⟨P, hP, t, rfl, _⟩ := (mem_cutParents A a b Q).mp hQ
    exact ⟨P, hP, hsQ.trans Set.inter_subset_left⟩
  refine ⟨⟨B.complex, B.finite, B.space.trans hspace, htrace, hcarrier⟩, hB, ?_⟩
  intro P hP s
  by_cases hne : (cutCell P a b s).Nonempty
  · exact B.trace _ ((mem_cutParents A a b _).mpr ⟨P, hP, s, rfl, hne⟩)
  · have he : cutCell P a b s = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    intro t ht
    simp [he]
end CanonicalCuts
section GeneralChains
variable {V W : Type*}
lemma chainFaces_map_injective (A : Finset (Set V)) (c : Set V → V)
    (d : Set W → W) (f : V → W) (hf : Function.Injective f)
    (hcd : ∀ P ∈ A, d (f '' P) = f (c P)) :
    chainFaces (A.image fun P => f '' P) d =
      (fun s : Finset V => s.map ⟨f, hf⟩) '' chainFaces A c := by
  have hfi : Function.Injective (fun P : Set V => f '' P) := Set.image_injective.mpr hf
  ext s
  constructor
  · rintro ⟨t, hne, ht, hchain, rfl⟩
    let u := t.preimage (fun P : Set V => f '' P) hfi.injOn
    have hu : u ⊆ A := by
      intro P hP
      have htP := ht (Finset.mem_preimage.mp hP)
      obtain ⟨Q, hQ, he⟩ := Finset.mem_image.mp htP
      exact hfi he ▸ hQ
    have hut : u.image (fun P => f '' P) = t := by
      ext Q
      simp only [Finset.mem_image, u, Finset.mem_preimage]
      constructor
      · rintro ⟨P, hP, rfl⟩; exact hP
      · intro hQ
        obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp (ht hQ)
        exact ⟨P, hQ, rfl⟩
    have hune : u.Nonempty := by
      obtain ⟨Q, hQ⟩ := hne
      rw [← hut] at hQ
      obtain ⟨P, hP, _⟩ := Finset.mem_image.mp hQ
      exact ⟨P, hP⟩
    have huchain : (u : Set (Set V)).Pairwise (fun P Q => P ⊆ Q ∨ Q ⊆ P) := by
      intro P hP Q hQ hpq
      have himgne : f '' P ≠ f '' Q := fun h => hpq (hfi h)
      rcases hchain (Finset.mem_preimage.mp hP) (Finset.mem_preimage.mp hQ) himgne with h | h
      · exact Or.inl ((Set.image_subset_image_iff hf).mp h)
      · exact Or.inr ((Set.image_subset_image_iff hf).mp h)
    refine ⟨u.image c, ⟨u, hune, hu, huchain, rfl⟩, ?_⟩
    change (u.image c).map ⟨f, hf⟩ = t.image d
    rw [← hut, Finset.image_image, Finset.map_eq_image, Finset.image_image]
    apply Finset.image_congr
    intro P hP
    exact (hcd P (hu hP)).symm
  · rintro ⟨s, ⟨t, hne, ht, hchain, rfl⟩, rfl⟩
    refine ⟨t.image (fun P => f '' P), hne.image _, Finset.image_subset_image ht, ?_, ?_⟩
    · intro P hP Q hQ hpq
      obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      have hne' : P' ≠ Q' := fun h => hpq (h ▸ rfl)
      rcases hchain hP' hQ' hne' with h | h
      · exact Or.inl (Set.image_mono h)
      · exact Or.inr (Set.image_mono h)
    · change (t.image c).map ⟨f, hf⟩ = (t.image fun P => f '' P).image d
      rw [Finset.map_eq_image, Finset.image_image, Finset.image_image]
      apply Finset.image_congr
      intro P hP
      exact (hcd P (ht hP)).symm
end GeneralChains
section LinearCutNaturality
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {J : Type*} [Fintype J]
omit [Fintype J] in
lemma cutCell_linear_image (f : V →ₗ[ℝ] W) (P : Set V)
    (a : J → W →ₗ[ℝ] ℝ) (b : J → ℝ) (s : J → Bool) :
    f '' cutCell P (fun j => (a j).comp f) b s = cutCell (f '' P) a b s := by
  have hh (x : V) (j : J) :
      signedForm (fun j => (a j).comp f) s j x = signedForm a s j (f x) := by
    cases h : s j <;> simp [signedForm, h]
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxa⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, fun j => (hh x j) ▸ hxa j⟩
  · rintro ⟨⟨x, hx, rfl⟩, hxa⟩
    exact ⟨x, ⟨hx, fun j => (hh x j).symm ▸ hxa j⟩, rfl⟩
lemma cutParents_linear_image (f : V →ₗ[ℝ] W) (A : Finset (Set V))
    (a : J → W →ₗ[ℝ] ℝ) (b : J → ℝ) :
    cutParents (A.image fun P => f '' P) a b =
      (cutParents A (fun j => (a j).comp f) b).image (fun P => f '' P) := by
  ext Q
  rw [mem_cutParents, Finset.mem_image]
  constructor
  · rintro ⟨P, hP, s, rfl, hne⟩
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hP
    rw [← cutCell_linear_image] at hne ⊢
    exact ⟨_, (mem_cutParents A _ b _).mpr
      ⟨R, hR, s, rfl, Set.image_nonempty.mp hne⟩, rfl⟩
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨P, hP, s, rfl, hne⟩ := (mem_cutParents A _ b R).mp hR
    refine ⟨f '' P, Finset.mem_image_of_mem _ hP, s, ?_, ?_⟩
    · exact cutCell_linear_image f P a b s
    · exact hne.image _
lemma canonical_chainFaces_map_injective (F : Finset (Set V))
    (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (hF : ∀ P ∈ F, ∃ s : Finset V, s.Nonempty ∧ P = convexHull ℝ (s : Set V)) :
    chainFaces (F.image fun P => f '' P) canonicalCenter =
      (fun s : Finset V => s.map ⟨f, hf⟩) '' chainFaces F canonicalCenter := by
  apply chainFaces_map_injective F canonicalCenter canonicalCenter f hf
  intro P hP
  obtain ⟨s, hs, rfl⟩ := hF P hP
  apply canonicalCenter_affine_map f hf _ (finite_extremePoints_finiteHull s)
  have hne : (canonicalVertices (convexHull ℝ (s : Set V))).Nonempty := by
    apply Finset.coe_nonempty.mp
    apply (convexHull_nonempty_iff (𝕜 := ℝ)).mp
    rw [← finiteHull_eq_canonicalVertices]
    exact convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)
  have := Finset.coe_nonempty.mpr hne
  rwa [coe_canonicalVertices (finite_extremePoints_finiteHull s)] at this
end LinearCutNaturality
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
lemma faceClosure_finiteHull (A : Finset (Set V))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    ∀ P ∈ faceClosure A, ∃ s : Finset V, s.Nonempty ∧ P = convexHull ℝ (s : Set V) := by
  intro Q hQ
  obtain ⟨P, hP, hne, hface⟩ := (mem_faceClosure A hvertices Q).mp hQ
  obtain ⟨t, rfl⟩ := hvertices P hP
  obtain ⟨s, _, rfl⟩ := hface.eq_convexHull_subset
  exact ⟨s, Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp hne), rfl⟩
variable [FiniteDimensional ℝ V] {J : Type*} [Fintype J]
theorem exists_embedded_canonical_cutTriangulation (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P)
    (f : V →ₗ[ℝ] W) (hf : Function.Injective f)
    (a : J → W →ₗ[ℝ] ℝ) (b : J → ℝ) :
    ∃ B : CellTriangulation (A.image fun P => f '' P),
      B.complex.faces = chainFaces
        (faceClosure (cutParents (A.image fun P => f '' P) a b)) canonicalCenter ∧
      ∀ P ∈ A, ∀ s : J → Bool,
        RespectsSet B.complex (cutCell (f '' P) a b s) := by
  let a' : J → V →ₗ[ℝ] ℝ := fun j => (a j).comp f
  obtain ⟨B, hB, htr⟩ := exists_canonical_cutTriangulation A hdata hinter a' b
  have hv : ∀ P ∈ cutParents A a' b, ∃ s : Finset V, P = convexHull ℝ (s : Set V) := by
    intro P hP
    obtain ⟨Q, hQ, s, rfl, hne⟩ := (mem_cutParents A a' b P).mp hP
    obtain ⟨q⟩ := hdata Q hQ
    exact (cutCell_nonempty_data q a' b s hne).2
  refine ⟨B.affineImage f.toAffineMap hf, ?_, ?_⟩
  · change (fun s : Finset V => s.map ⟨f, hf⟩) '' B.complex.faces = _
    rw [hB, cutParents_linear_image]
    change (fun s : Finset V => s.map ⟨f.toAffineMap, hf⟩) ''
      chainFaces (faceClosure (cutParents A a' b)) canonicalCenter =
      chainFaces (faceClosure ((cutParents A a' b).image
        fun P => f.toAffineMap '' P)) canonicalCenter
    rw [faceClosure_affine_map_injective f.toAffineMap hf _ hv]
    exact (canonical_chainFaces_map_injective _ f.toAffineMap hf
      (faceClosure_finiteHull _ hv)).symm
  · intro P hP s
    have hh := (htr P hP s).affine_image f.toAffineMap hf
    change RespectsSet (B.affineImage f.toAffineMap hf).complex (f '' cutCell P a' b s) at hh
    rwa [cutCell_linear_image] at hh
end BassTrace.Sparse.Cuts
end OAI
end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
open Set Finset
open scoped Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
section ArbitraryAmbientComplex
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
theorem exists_finite_coordinate_patch (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) :
    ∃ U : Submodule ℝ V, FiniteDimensional ℝ U ∧
      ∀ s ∈ K.faces, (s : Set V) ⊆ Set.range U.subtype := by
  let S : Finset V := hK.toFinset.biUnion id
  let U : Submodule ℝ V := Submodule.span ℝ (S : Set V)
  refine ⟨U, FiniteDimensional.span_of_finite ℝ S.finite_toSet, ?_⟩
  intro s hs x hx
  have hxS : x ∈ S := Finset.mem_biUnion.mpr ⟨s, by simpa using hs, hx⟩
  exact ⟨⟨x, Submodule.subset_span hxS⟩, rfl⟩
end ArbitraryAmbientComplex
section FiniteComplexPatches
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
noncomputable def complexParents (K : Geometry.SimplicialComplex ℝ V) (hK : K.faces.Finite) :
    Finset (Set V) := hK.toFinset.image fun (s : Finset V) => convexHull ℝ (s : Set V)
lemma mem_complexParents (K : Geometry.SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (P : Set V) : P ∈ complexParents K hK ↔
      ∃ s ∈ K.faces, P = convexHull ℝ (s : Set V) := by
  simp only [complexParents, Finset.mem_image, Set.Finite.mem_toFinset, eq_comm]
lemma complexParents_affineImage (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    complexParents (affineImageComplex K f hf) (affineImageComplex_finite K f hf hK) =
      (complexParents K hK).image (fun P => f '' P) := by
  apply Finset.ext
  intro P
  rw [mem_complexParents, Finset.mem_image]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨convexHull ℝ (t : Set V), (mem_complexParents K hK _).mpr ⟨t, ht, rfl⟩, ?_⟩
    rw [Finset.coe_map]
    exact f.image_convexHull (t : Set V)
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (mem_complexParents K hK Q).mp hQ
    refine ⟨t.map ⟨f,hf⟩, ⟨t, ht, rfl⟩, ?_⟩
    rw [Finset.coe_map]
    exact f.image_convexHull (t : Set V)
lemma complexParents_space (K : Geometry.SimplicialComplex ℝ V) (hK : K.faces.Finite) :
    familySpace (complexParents K hK) = K.space := by
  ext x
  constructor
  · rintro ⟨P, hP, hx⟩
    obtain ⟨s, hs, rfl⟩ := (mem_complexParents K hK P).mp hP
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, hs, hx⟩
  · intro hx
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact ⟨_, (mem_complexParents K hK _).mpr ⟨s, hs, rfl⟩, hx⟩
theorem exists_canonical_simplicialCuts (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) {J : Type*} [Fintype J]
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) :
    ∃ B : CellTriangulation (complexParents K hK),
      B.complex.faces = chainFaces
        (faceClosure (cutParents (complexParents K hK) a b)) canonicalCenter ∧
      ∀ s ∈ K.faces, ∀ e : J → Bool,
        RespectsSet B.complex (cutCell (convexHull ℝ (s : Set V)) a b e) := by
  obtain ⟨U, hdim, hU⟩ := exists_finite_coordinate_patch K hK
  let : FiniteDimensional ℝ U := hdim
  let f := U.subtype
  have hf : Function.Injective f := U.subtype_injective
  let L := affinePreimageComplex K f.toAffineMap hf
  have hL : L.faces.Finite := affinePreimageComplex_finite K f.toAffineMap hf hK
  have hLK : affineImageComplex L f.toAffineMap hf = K :=
    affineImage_preimage_complex K f.toAffineMap hf hU
  have hA : (complexParents L hL).image (fun P => f '' P) = complexParents K hK := by
    have hh := complexParents_affineImage L hL f.toAffineMap hf
    change (complexParents L hL).image (fun P => f.toAffineMap '' P) = _
    simpa only [hLK] using hh.symm
  have hdata : ∀ P ∈ complexParents L hL, Nonempty (CellData P) := by
    intro P hP
    obtain ⟨t, ht, rfl⟩ := (mem_complexParents L hL P).mp hP
    exact simplex_has_cellData t (L.nonempty_of_mem_faces ht) (L.indep ht)
  have hinter : ∀ P ∈ complexParents L hL, ∀ Q ∈ complexParents L hL,
      SupportingFace (P ∩ Q) P := by
    intro P hP Q hQ
    obtain ⟨s, hs, rfl⟩ := (mem_complexParents L hL P).mp hP
    obtain ⟨t, ht, rfl⟩ := (mem_complexParents L hL Q).mp hQ
    rw [L.convexHull_inter_convexHull hs ht, ← Finset.coe_inter]
    exact simplex_face_supporting s (s ∩ t) (L.indep hs) Finset.inter_subset_left
  obtain ⟨B, hB, htr⟩ := exists_embedded_canonical_cutTriangulation
    (complexParents L hL) hdata hinter f hf a b
  have htr' : ∀ P ∈ (complexParents L hL).image (fun P => f '' P), ∀ e : J → Bool,
      RespectsSet B.complex (cutCell P a b e) := by
    intro P hP e
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact htr Q hQ e
  have hres : ∃ C : CellTriangulation ((complexParents L hL).image (fun P => f '' P)),
      C.complex.faces = chainFaces
        (faceClosure (cutParents ((complexParents L hL).image (fun P => f '' P)) a b)) canonicalCenter ∧
      ∀ P ∈ (complexParents L hL).image (fun P => f '' P), ∀ e : J → Bool,
        RespectsSet C.complex (cutCell P a b e) := ⟨B, hB, htr'⟩
  rw [hA] at hres
  obtain ⟨C, hC, hCt⟩ := hres
  exact ⟨C, hC, fun s hs e => hCt _ ((mem_complexParents K hK _).mpr ⟨s, hs, rfl⟩) e⟩
end FiniteComplexPatches
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
def directedUnionComplex {I : Type*} (K : I → Geometry.SimplicialComplex ℝ V)
    (hK : Directed (· ≤ ·) K) : Geometry.SimplicialComplex ℝ V where
  faces := {s | ∃ i, s ∈ (K i).faces}
  indep := by
    rintro s ⟨i, hi⟩
    exact (K i).indep hi
  isRelLowerSet_faces := by
    rintro s ⟨i, hi⟩
    exact ⟨(K i).nonempty_of_mem_faces hi, fun t hts ht =>
      ⟨i, (K i).down_closed hi hts ht⟩⟩
  inter_subset_convexHull := by
    rintro s t ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hik, hjk⟩ := hK i j
    exact (K k).inter_subset_convexHull (hik hi) (hjk hj)
lemma directedUnionComplex_space {I : Type*} (K : I → Geometry.SimplicialComplex ℝ V)
    (hK : Directed (· ≤ ·) K) : (directedUnionComplex K hK).space = ⋃ i, (K i).space := by
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff, Set.mem_iUnion]
  exact ⟨fun ⟨s, ⟨i, hs⟩, hx⟩ => ⟨i, s, hs, hx⟩,
    fun ⟨i, s, hs, hx⟩ => ⟨s, ⟨i, hs⟩, hx⟩⟩
def finitePatch (K : Geometry.SimplicialComplex ℝ V)
    (A : Finset (Finset V)) (hA : ∀ s ∈ A, s ∈ K.faces) : Geometry.SimplicialComplex ℝ V where
  faces := {s | s.Nonempty ∧ ∃ t ∈ A, s ⊆ t}
  indep := by
    rintro s ⟨hs, t, ht, hst⟩
    exact K.indep (K.down_closed (hA t ht) hst hs)
  isRelLowerSet_faces := by
    rintro s ⟨hs, t, ht, hst⟩
    exact ⟨hs, fun u hus hu => ⟨hu, t, ht, hus.trans hst⟩⟩
  inter_subset_convexHull := by
    rintro s t ⟨hs, u, hu, hsu⟩ ⟨ht, v, hv, htv⟩
    exact K.inter_subset_convexHull (K.down_closed (hA u hu) hsu hs)
      (K.down_closed (hA v hv) htv ht)
lemma finitePatch_finite (K : Geometry.SimplicialComplex ℝ V)
    (A : Finset (Finset V)) (hA : ∀ s ∈ A, s ∈ K.faces) :
    (finitePatch K A hA).faces.Finite := by
  classical
  apply (A.biUnion Finset.powerset).finite_toSet.subset
  rintro s ⟨_, t, ht, hst⟩
  exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_powerset.mpr hst⟩
lemma finitePatch_mono (K : Geometry.SimplicialComplex ℝ V)
    {A B : Finset (Finset V)} (hA : ∀ s ∈ A, s ∈ K.faces) (hB : ∀ s ∈ B, s ∈ K.faces)
    (hAB : A ⊆ B) : finitePatch K A hA ≤ finitePatch K B hB := by
  rintro s ⟨hs, t, ht, hst⟩
  exact ⟨hs, t, hAB ht, hst⟩
lemma mem_finitePatch (K : Geometry.SimplicialComplex ℝ V)
    (A : Finset (Finset V)) (hA : ∀ s ∈ A, s ∈ K.faces) {s : Finset V} (hs : s ∈ A) :
    s ∈ (finitePatch K A hA).faces :=
  ⟨K.nonempty_of_mem_faces (hA s hs), s, hs, Finset.Subset.refl s⟩
end BassTrace.Sparse.Cuts
end OAI
end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
open Set Finset
open scoped Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
section LocallyFiniteCuts
variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma faceClosure_mono {A B : Finset (Set V)} (h : A ⊆ B) :
    faceClosure A ⊆ faceClosure B := by
  classical
  intro P hP
  obtain ⟨Q, hQ, hPQ⟩ := Finset.mem_biUnion.mp hP
  exact Finset.mem_biUnion.mpr ⟨Q, h hQ, hPQ⟩
omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma chainFaces_mono {A B : Finset (Set V)} {c : Set V → V} (h : A ⊆ B) :
    chainFaces A c ⊆ chainFaces B c := by
  rintro s ⟨t, hn, ht, hc, he⟩
  exact ⟨t, hn, ht.trans h, hc, he⟩
lemma cutCell_extend_irrelevant (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    {I L : Finset J} (hIL : I ⊆ L) (s : I → Bool)
    (hz : ∀ j ∈ L, j ∉ I → ∀ x ∈ P, a j x = 0)
    (hb : ∀ j ∈ L, 0 ≤ b j) :
    ∃ t : L → Bool, cutCell P (fun j : I => a j) (fun j : I => b j) s =
      cutCell P (fun j : L => a j) (fun j : L => b j) t := by
  classical
  let t : L → Bool := fun j => if h : j.val ∈ I then s ⟨j.val, h⟩ else true
  refine ⟨t, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hs⟩
    refine ⟨hx, ?_⟩
    intro j
    by_cases hj : j.val ∈ I
    · simpa only [signedForm, signedBound, t, dite_eq_left hj] using hs ⟨j.val, hj⟩
    · simp only [signedForm, signedBound, t, dite_eq_right hj, ↓reduceIte]
      rw [hz j.val j.property hj x hx]
      exact hb j.val j.property
  · rintro ⟨hx, ht⟩
    refine ⟨hx, ?_⟩
    intro j
    simpa only [signedForm, signedBound, t, dite_eq_left j.property] using
      ht ⟨j.val, hIL j.property⟩
lemma cutParents_mono_irrelevant {A B : Finset (Set V)} (hAB : A ⊆ B)
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) {I L : Finset J} (hIL : I ⊆ L)
    (hz : ∀ P ∈ A, ∀ j ∈ L, j ∉ I → ∀ x ∈ P, a j x = 0)
    (hb : ∀ j ∈ L, 0 ≤ b j) :
    cutParents A (fun j : I => a j) (fun j : I => b j) ⊆
      cutParents B (fun j : L => a j) (fun j : L => b j) := by
  intro Q hQ
  obtain ⟨P, hP, s, rfl, hn⟩ := (mem_cutParents _ _ _ _).mp hQ
  obtain ⟨t, ht⟩ := cutCell_extend_irrelevant P a b hIL s (hz P hP) hb
  exact (mem_cutParents _ _ _ _).mpr ⟨P, hAB hP, t, ht, hn⟩
lemma complexParents_mono {K L : Geometry.SimplicialComplex ℝ V}
    (hK : K.faces.Finite) (hL : L.faces.Finite) (hKL : K ≤ L) :
    complexParents K hK ⊆ complexParents L hL := by
  intro P hP
  obtain ⟨s, hs, rfl⟩ := (mem_complexParents K hK P).mp hP
  exact (mem_complexParents L hL _).mpr ⟨s, hKL hs, rfl⟩
lemma finiteComplex_space_finiteHull (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) (hc : Convex ℝ K.space) :
    ∃ s : Finset V, K.space = convexHull ℝ (s : Set V) := by
  classical
  let s : Finset V := hK.toFinset.biUnion id
  refine ⟨s, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨t, ht, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    apply convexHull_mono (t := (s : Set V)) ?_ hx
    intro y hy
    exact Finset.mem_biUnion.mpr ⟨t, by simpa using ht, hy⟩
  · apply convexHull_min ?_ hc
    intro x hx
    obtain ⟨t, ht, hx⟩ := Finset.mem_biUnion.mp hx
    exact K.subset_space (by simpa using ht) hx
lemma finiteHull_of_respects (K : Geometry.SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (P : Set V) (hc : Convex ℝ P) (hP : P ⊆ K.space) (htr : RespectsSet K P) :
    ∃ s : Finset V, P = convexHull ℝ (s : Set V) := by
  have he : (restrictComplex K P).space = P := by
    rw [restrictComplex_space_of_respects K P htr]
    exact Set.inter_eq_right.mpr hP
  obtain ⟨s, hs⟩ := finiteComplex_space_finiteHull (restrictComplex K P)
    (restrictComplex_finite K P hK) (he.symm ▸ hc)
  exact ⟨s, he.symm.trans hs⟩
lemma cutParents_finiteHull_simplicial (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) {I : Type*} [Fintype I]
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) :
    ∀ P ∈ cutParents (complexParents K hK) a b,
      ∃ s : Finset V, P = convexHull ℝ (s : Set V) := by
  obtain ⟨B, _, htr⟩ := exists_canonical_simplicialCuts K hK a b
  intro P hP
  obtain ⟨Q, hQ, e, rfl, _⟩ := (mem_cutParents _ _ _ _).mp hP
  obtain ⟨t, ht, rfl⟩ := (mem_complexParents K hK Q).mp hQ
  apply finiteHull_of_respects B.complex B.finite _
    ((convex_convexHull ℝ _).inter (convex_cell _ _)) ?_ (htr t ht e)
  rw [B.space, complexParents_space]
  exact Set.inter_subset_left.trans (K.convexHull_subset_space ht)
lemma canonicalCenter_supporting_iff {P Q : Set V}
    (hn : Q.Nonempty) (hv : ∃ s : Finset V, Q = convexHull ℝ (s : Set V))
    (hface : SupportingFace (Q ∩ P) Q) : canonicalCenter Q ∈ P ↔ Q ⊆ P := by
  obtain ⟨s, rfl⟩ := hv
  have hs : s.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp hn)
  have hmem := canonicalCenter_mem_finiteHull hs
  constructor
  · intro hc
    obtain ⟨f, b, hf, he⟩ := hface
    have hcb : f (canonicalCenter (convexHull ℝ (s : Set V))) = b :=
      (he.subset ⟨hmem, hc⟩).2
    intro x hx
    exact (he.symm.subset ⟨hx, canonicalCenter_supports_finiteHull hs f b hf hcb x hx⟩).2
  · exact fun h => h hmem
lemma simplicialParents_inter_supporting (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) {P Q : Set V} (hP : P ∈ complexParents K hK)
    (hQ : Q ∈ complexParents K hK) : SupportingFace (P ∩ Q) P := by
  obtain ⟨s, hs, rfl⟩ := (mem_complexParents _ _ _).mp hP
  obtain ⟨t, ht, rfl⟩ := (mem_complexParents _ _ _).mp hQ
  rw [K.convexHull_inter_convexHull hs ht, ← Finset.coe_inter]
  exact simplex_face_supporting s (s ∩ t) (K.indep hs) Finset.inter_subset_left
lemma cutParents_mono {I : Type*} [Fintype I] {A B : Finset (Set V)}
    (hAB : A ⊆ B) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) :
    cutParents A a b ⊆ cutParents B a b := by
  intro P hP
  obtain ⟨Q, hQ, e, he, hn⟩ := (mem_cutParents _ _ _ _).mp hP
  exact (mem_cutParents _ _ _ _).mpr ⟨Q, hAB hQ, e, he, hn⟩
lemma faceClosure_cutParents_filter {I : Type*} [Fintype I]
    (A : Finset (Set V)) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hv : ∀ Q ∈ cutParents A a b, ∃ s : Finset V, Q = convexHull ℝ (s : Set V))
    (hi : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P)
    {P : Set V} (hP : P ∈ A) :
    (faceClosure (cutParents A a b)).filter (fun Q => Q ⊆ P) =
      faceClosure (cutParents {P} a b) := by
  classical
  have hsub : cutParents {P} a b ⊆ cutParents A a b :=
    cutParents_mono (Finset.singleton_subset_iff.mpr hP) a b
  have hvP := fun Q hQ => hv Q (hsub hQ)
  apply Finset.ext
  intro Q
  rw [Finset.mem_filter, mem_faceClosure _ hv, mem_faceClosure _ hvP]
  constructor
  · rintro ⟨⟨R, hR, hn, hQR⟩, hQP⟩
    obtain ⟨S, hS, e, rfl, _⟩ := (mem_cutParents _ _ _ _).mp hR
    let X := cutCell P a b e
    have hQX : Q ⊆ X := fun x hx => ⟨hQP hx, (hQR.subset hx).2⟩
    have hX : X ∈ cutParents {P} a b :=
      (mem_cutParents _ _ _ _).mpr ⟨P, Finset.mem_singleton_self _, e, rfl, hn.mono hQX⟩
    obtain ⟨s, hs⟩ := hvP X hX
    have hface := (supportingFace_self X).inter_of_parent_inter hQR
      (cutCell_inter_parents_supporting (hi P hP S hS) a b e e) hs
    rw [Set.inter_eq_right.mpr hQX] at hface
    exact ⟨X, hX, hn, hface⟩
  · rintro ⟨R, hR, hn, hQR⟩
    refine ⟨⟨R, hsub hR, hn, hQR⟩, ?_⟩
    obtain ⟨S, hS, e, rfl, _⟩ := (mem_cutParents _ _ _ _).mp hR
    have hSP : S = P := Finset.mem_singleton.mp hS
    subst S
    exact hQR.subset.trans Set.inter_subset_left
lemma canonical_chainFaces_restrict_parent {I : Type*} [Fintype I]
    (A : Finset (Set V)) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hv : ∀ Q ∈ cutParents A a b, ∃ s : Finset V, Q = convexHull ℝ (s : Set V))
    (hi : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P)
    {P : Set V} (hP : P ∈ A) (s : Finset V) :
    s ∈ chainFaces (faceClosure (cutParents A a b)) canonicalCenter ∧ (s : Set V) ⊆ P ↔
      s ∈ chainFaces (faceClosure (cutParents {P} a b)) canonicalCenter := by
  have hc : ∀ Q ∈ faceClosure (cutParents A a b), canonicalCenter Q ∈ P ↔ Q ⊆ P := by
    intro Q hQ
    obtain ⟨R, hR, hn, hQR⟩ := (mem_faceClosure _ hv Q).mp hQ
    obtain ⟨v, hvR⟩ := hv R hR
    have hvQ : ∃ u : Finset V, Q = convexHull ℝ (u : Set V) := by
      rw [hvR] at hQR
      obtain ⟨u, _, hu⟩ := hQR.eq_convexHull_subset
      exact ⟨u, hu⟩
    obtain ⟨S, hS, e, rfl, _⟩ := (mem_cutParents _ _ _ _).mp hR
    exact canonicalCenter_supporting_iff hn hvQ
      ((hi S hS P hP).inter_restrict (hQR.subset.trans Set.inter_subset_left))
  rw [chainFaces_restrict _ _ P hc s, faceClosure_cutParents_filter A a b hv hi hP]
lemma cutCell_restrict_irrelevant (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    {I L : Finset J} (hIL : I ⊆ L) (t : L → Bool)
    (hz : ∀ j ∈ L, j ∉ I → ∀ x ∈ P, a j x = 0)
    (hb : ∀ j ∈ L, 0 ≤ b j)
    (hn : (cutCell P (fun j : L => a j) (fun j : L => b j) t).Nonempty) :
    cutCell P (fun j : L => a j) (fun j : L => b j) t =
      cutCell P (fun j : I => a j) (fun j : I => b j)
        (fun j => t ⟨j.val, hIL j.property⟩) := by
  classical
  obtain ⟨z, hzP, hzt⟩ := hn
  ext x
  constructor
  · rintro ⟨hx, hxL⟩
    exact ⟨hx, fun j => hxL ⟨j.val, hIL j.property⟩⟩
  · rintro ⟨hx, hxI⟩
    refine ⟨hx, ?_⟩
    intro j
    by_cases hj : j.val ∈ I
    · exact hxI ⟨j.val, hj⟩
    · have hh := hzt j
      cases he : t j <;> simpa [signedForm,signedBound,he,hz j.val j.property hj x hx,hz j.val j.property hj z hzP] using hh
lemma cutParents_eq_irrelevant (A : Finset (Set V))
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) {I L : Finset J} (hIL : I ⊆ L)
    (hz : ∀ P ∈ A, ∀ j ∈ L, j ∉ I → ∀ x ∈ P, a j x = 0)
    (hb : ∀ j ∈ L, 0 ≤ b j) :
    cutParents A (fun j : I => a j) (fun j : I => b j) =
      cutParents A (fun j : L => a j) (fun j : L => b j) := by
  apply Finset.Subset.antisymm
  · exact cutParents_mono_irrelevant (Finset.Subset.refl _) a b hIL hz
      (fun j hj => hb j hj)
  · intro Q hQ
    obtain ⟨P, hP, e, rfl, hn⟩ := (mem_cutParents _ _ _ _).mp hQ
    exact (mem_cutParents _ _ _ _).mpr ⟨P, hP, _,
      cutCell_restrict_irrelevant P a b hIL e (hz P hP) hb hn, hn⟩
omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma chainFaces_finite (F : Finset (Set V)) (c : Set V → V) : (chainFaces F c).Finite := by
  classical
  apply (F.powerset.image (fun t : Finset (Set V) => t.image c)).finite_toSet.subset
  rintro s ⟨t, _, ht, _, rfl⟩
  exact Finset.mem_image_of_mem _ (Finset.mem_powerset.mpr ht)
structure LocalCutData (K : Geometry.SimplicialComplex ℝ V) (J : Type*) where
  form : J → V →ₗ[ℝ] ℝ
  level : J → ℝ
  positive : ∀ j, 0 ≤ level j
  relevant : Finset V → Finset J
  vanish : ∀ s ∈ K.faces, ∀ j, j ∉ relevant s →
    ∀ x ∈ convexHull ℝ (s : Set V), form j x = 0
abbrev CutPatch (K : Geometry.SimplicialComplex ℝ V) :=
  {A : Finset (Finset V) // ∀ s ∈ A, s ∈ K.faces}
lemma finitePatch_le (K : Geometry.SimplicialComplex ℝ V) (p : CutPatch K) :
    finitePatch K p.val p.property ≤ K := by
  rintro s ⟨hs, t, ht, hst⟩
  exact K.down_closed (p.property t ht) hst hs
namespace LocalCutData
variable {K : Geometry.SimplicialComplex ℝ V} (d : LocalCutData K J)
noncomputable def patchIndices (p : CutPatch K) : Finset J := p.val.biUnion d.relevant
lemma patchIndices_mono {p q : CutPatch K} (hpq : p.val ⊆ q.val) :
    d.patchIndices p ⊆ d.patchIndices q := by
  classical
  intro j hj
  obtain ⟨s, hs, hj⟩ := Finset.mem_biUnion.mp hj
  exact Finset.mem_biUnion.mpr ⟨s, hpq hs, hj⟩
lemma patch_vanish (p : CutPatch K) (P : Set V)
    (hP : P ∈ complexParents (finitePatch K p.val p.property)
      (finitePatch_finite K p.val p.property)) (j : J) (hj : j ∉ d.patchIndices p) :
    ∀ x ∈ P, d.form j x = 0 := by
  classical
  obtain ⟨s, ⟨_, t, ht, hst⟩, rfl⟩ := (mem_complexParents _ _ P).mp hP
  have hjt : j ∉ d.relevant t := fun h =>
    hj (Finset.mem_biUnion.mpr ⟨t, ht, h⟩)
  exact fun x hx => d.vanish t (p.property t ht) j hjt x (convexHull_mono hst hx)
noncomputable def patchTriangulation (p : CutPatch K) :
    CellTriangulation (complexParents (finitePatch K p.val p.property)
      (finitePatch_finite K p.val p.property)) :=
  Classical.choose (exists_canonical_simplicialCuts (finitePatch K p.val p.property)
    (finitePatch_finite K p.val p.property)
    (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j))
lemma patchTriangulation_faces (p : CutPatch K) :
    (d.patchTriangulation p).complex.faces = chainFaces
      (faceClosure (cutParents (complexParents (finitePatch K p.val p.property)
        (finitePatch_finite K p.val p.property))
        (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j)))
      canonicalCenter :=
  (Classical.choose_spec (exists_canonical_simplicialCuts (finitePatch K p.val p.property)
    (finitePatch_finite K p.val p.property)
    (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j))).1
lemma patchTriangulation_trace (p : CutPatch K) (s : Finset V)
    (hs : s ∈ (finitePatch K p.val p.property).faces) (e : d.patchIndices p → Bool) :
    RespectsSet (d.patchTriangulation p).complex
      (cutCell (convexHull ℝ (s : Set V))
        (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j) e) :=
  (Classical.choose_spec (exists_canonical_simplicialCuts (finitePatch K p.val p.property)
    (finitePatch_finite K p.val p.property)
    (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j))).2 s hs e
lemma patchTriangulation_mono {p q : CutPatch K} (hpq : p.val ⊆ q.val) :
    (d.patchTriangulation p).complex ≤ (d.patchTriangulation q).complex := by
  intro s hs
  change s ∈ (d.patchTriangulation p).complex.faces at hs
  change s ∈ (d.patchTriangulation q).complex.faces
  rw [d.patchTriangulation_faces] at hs ⊢
  refine chainFaces_mono (faceClosure_mono (cutParents_mono_irrelevant ?_
    d.form d.level (d.patchIndices_mono hpq) ?_ ?_)) hs
  · exact complexParents_mono _ _ (finitePatch_mono K p.property q.property hpq)
  · intro P hP j _ hj
    exact d.patch_vanish p P hP j hj
  · exact fun j _ => d.positive j
lemma patchTriangulation_directed : Directed (· ≤ ·) (fun p : CutPatch K =>
    (d.patchTriangulation p).complex) := by
  classical
  intro p q
  let u : CutPatch K := ⟨p.val ∪ q.val, fun s hs => (Finset.mem_union.mp hs).elim
    (p.property s) (q.property s)⟩
  exact ⟨u, d.patchTriangulation_mono Finset.subset_union_left,
    d.patchTriangulation_mono Finset.subset_union_right⟩
noncomputable def globalComplex : Geometry.SimplicialComplex ℝ V :=
  directedUnionComplex (fun p : CutPatch K => (d.patchTriangulation p).complex)
    d.patchTriangulation_directed
lemma globalComplex_space : d.globalComplex.space = K.space := by
  change (directedUnionComplex _ d.patchTriangulation_directed).space = _
  rw [directedUnionComplex_space]
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    rw [(d.patchTriangulation p).space, complexParents_space] at hp
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hp
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, finitePatch_le K p hs, hx⟩
  · intro hx
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    let p : CutPatch K := ⟨{s}, by simpa using hs⟩
    apply Set.mem_iUnion.mpr
    refine ⟨p, ?_⟩
    rw [(d.patchTriangulation p).space, complexParents_space]
    exact Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨s, mem_finitePatch K p.val p.property (Finset.mem_singleton_self s), hx⟩
lemma globalComplex_carrier {s : Finset V} (hs : s ∈ d.globalComplex.faces) :
    ∃ t ∈ K.faces, convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V) := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨P, hP, hsP⟩ := (d.patchTriangulation p).carrier s hp
  obtain ⟨t, ht, rfl⟩ := (mem_complexParents _ _ P).mp hP
  exact ⟨t, finitePatch_le K p ht, hsP⟩
lemma globalComplex_trace (s : Finset V) (hs : s ∈ K.faces) :
    RespectsSet d.globalComplex (convexHull ℝ (s : Set V)) := by
  classical
  rintro t ⟨p, hp⟩
  let q : CutPatch K := ⟨insert s p.val, by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hs
    · exact p.property u hu⟩
  have hpq : p.val ⊆ q.val := Finset.subset_insert _ _
  have hsq : s ∈ (finitePatch K q.val q.property).faces :=
    mem_finitePatch K q.val q.property (Finset.mem_insert_self _ _)
  exact (d.patchTriangulation q).trace _ ((mem_complexParents _ _ _).mpr ⟨s, hsq, rfl⟩)
    t (d.patchTriangulation_mono hpq hp)
lemma globalComplex_cut_trace (s : Finset V) (hs : s ∈ K.faces)
    (e : d.relevant s → Bool) : RespectsSet d.globalComplex
      (cutCell (convexHull ℝ (s : Set V)) (fun j : d.relevant s => d.form j)
        (fun j : d.relevant s => d.level j) e) := by
  classical
  rintro t ⟨p, hp⟩
  let q : CutPatch K := ⟨insert s p.val, by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hs
    · exact p.property u hu⟩
  have hsq : s ∈ (finitePatch K q.val q.property).faces :=
    mem_finitePatch K q.val q.property (Finset.mem_insert_self _ _)
  have hi : d.relevant s ⊆ d.patchIndices q := fun j hj =>
    Finset.mem_biUnion.mpr ⟨s, Finset.mem_insert_self _ _, hj⟩
  obtain ⟨e', he⟩ := cutCell_extend_irrelevant (convexHull ℝ (s : Set V))
    d.form d.level hi e (fun j _ hj => d.vanish s hs j hj) (fun j _ => d.positive j)
  rw [he]
  exact d.patchTriangulation_trace q s hsq e' t
    (d.patchTriangulation_mono (Finset.subset_insert _ _) hp)
lemma patchTriangulation_restrict_faces (p : CutPatch K) (s : Finset V)
    (hs : s ∈ p.val) :
    (restrictComplex (d.patchTriangulation p).complex
      (convexHull ℝ (s : Set V))).faces =
      chainFaces (faceClosure (cutParents {convexHull ℝ (s : Set V)}
        (fun j : d.relevant s => d.form j) (fun j : d.relevant s => d.level j)))
        canonicalCenter := by
  classical
  let L := finitePatch K p.val p.property
  have hsL : s ∈ L.faces := mem_finitePatch K p.val p.property hs
  have hsub : d.relevant s ⊆ d.patchIndices p := fun j hj =>
    Finset.mem_biUnion.mpr ⟨s, hs, hj⟩
  have he := cutParents_eq_irrelevant {convexHull ℝ (s : Set V)}
    d.form d.level hsub (by
      intro P hP j _ hj x hx
      have hP' : P = convexHull ℝ (s : Set V) := Finset.mem_singleton.mp hP
      subst P
      exact d.vanish s (p.property s hs) j hj x hx)
    (fun j _ => d.positive j)
  ext t
  change t ∈ (d.patchTriangulation p).complex.faces ∧
    (t : Set V) ⊆ convexHull ℝ (s : Set V) ↔ _
  rw [d.patchTriangulation_faces]
  rw [canonical_chainFaces_restrict_parent _ _ _
    (cutParents_finiteHull_simplicial L (finitePatch_finite K p.val p.property) _ _)
    (fun P hP Q hQ => simplicialParents_inter_supporting L _ hP hQ)
    ((mem_complexParents L _ _).mpr ⟨s, hsL, rfl⟩)]
  rw [← he]
lemma globalComplex_restrict_faces (s : Finset V) (hs : s ∈ K.faces) :
    (restrictComplex d.globalComplex (convexHull ℝ (s : Set V))).faces =
      chainFaces (faceClosure (cutParents {convexHull ℝ (s : Set V)}
        (fun j : d.relevant s => d.form j) (fun j : d.relevant s => d.level j)))
        canonicalCenter := by
  classical
  ext t
  constructor
  · rintro ⟨⟨p, hp⟩, ht⟩
    let q : CutPatch K := ⟨insert s p.val, by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hs
      · exact p.property u hu⟩
    have hq : t ∈ (restrictComplex (d.patchTriangulation q).complex
        (convexHull ℝ (s : Set V))).faces :=
      ⟨d.patchTriangulation_mono (Finset.subset_insert _ _) hp, ht⟩
    rwa [d.patchTriangulation_restrict_faces q s (Finset.mem_insert_self _ _)] at hq
  · intro ht
    let p : CutPatch K := ⟨{s}, by simpa using hs⟩
    rw [← d.patchTriangulation_restrict_faces p s (Finset.mem_singleton_self _)] at ht
    exact ⟨⟨p, ht.1⟩, ht.2⟩
end LocalCutData
end LocallyFiniteCuts
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {I J : Type*} [Fintype I] [Fintype J]
omit [Fintype I] [Fintype J] in
lemma cutCell_reindex (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (e : I ≃ J) (s : J → Bool) :
    cutCell P (a ∘ e) (b ∘ e) (s ∘ e) = cutCell P a b s := by
  ext x
  have h (i : I) :
      signedForm (a ∘ e) (s ∘ e) i x ≤ signedBound (b ∘ e) (s ∘ e) i ↔
      signedForm a s (e i) x ≤ signedBound b s (e i) := Iff.rfl
  change (x ∈ P ∧ ∀ i, signedForm (a ∘ e) (s ∘ e) i x ≤
    signedBound (b ∘ e) (s ∘ e) i) ↔
    (x ∈ P ∧ ∀ j, signedForm a s j x ≤ signedBound b s j)
  simp only [h]
  constructor
  · rintro ⟨hx, hle⟩
    exact ⟨hx, fun j => by simpa using hle (e.symm j)⟩
  · rintro ⟨hx, hle⟩
    exact ⟨hx, fun i => hle (e i)⟩
lemma cutParents_reindex (A : Finset (Set V)) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (e : I ≃ J) : cutParents A (a ∘ e) (b ∘ e) = cutParents A a b := by
  classical
  apply Finset.ext
  intro Q
  rw [mem_cutParents, mem_cutParents]
  constructor
  · rintro ⟨P, hP, s, rfl, hn⟩
    let t : J → Bool := s ∘ e.symm
    have he : t ∘ e = s := by funext i; simp [t]
    rw [← he, cutCell_reindex] at hn ⊢
    exact ⟨P, hP, t, rfl, hn⟩
  · rintro ⟨P, hP, s, rfl, hn⟩
    refine ⟨P, hP, s ∘ e, ?_, hn⟩
    exact (cutCell_reindex P a b e s).symm
end BassTrace.Sparse.Cuts
end OAI
end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse
open Set
open scoped Topology
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
end Sparse
namespace Sparse.Cuts
section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {J : Type*}
end
section
open Set Finset
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
def geometricRestriction (K : Geometry.SimplicialComplex ℝ E) (P : Set E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ P}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨K.down_closed hs.1 hts ht, (convexHull_mono hts).trans hs.2⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1
def IsMarked (K : Geometry.SimplicialComplex ℝ E) (P : Set E) : Prop :=
  ∀ x ∈ P, ∃ s ∈ K.faces, x ∈ convexHull ℝ (s : Set E) ∧
    convexHull ℝ (s : Set E) ⊆ P
lemma IsMarked.subset_space {K : Geometry.SimplicialComplex ℝ E} {P : Set E}
    (hP : IsMarked K P) : P ⊆ K.space := by
  intro x hx
  obtain ⟨s, hs, hxs, _⟩ := hP x hx
  exact K.convexHull_subset_space hs hxs
lemma IsMarked.restriction_space {K : Geometry.SimplicialComplex ℝ E} {P : Set E}
    (hP : IsMarked K P) : (geometricRestriction K P).space = P := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact hs.2 hxs
  · intro hx
    obtain ⟨s, hs, hxs, hsub⟩ := hP x hx
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, ⟨hs, hsub⟩, hxs⟩
lemma isMarked_empty (K : Geometry.SimplicialComplex ℝ E) : IsMarked K ∅ := by
  intro x hx
  exact hx.elim
lemma isMarked_space (K : Geometry.SimplicialComplex ℝ E) : IsMarked K K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  exact ⟨s, hs, hxs, K.convexHull_subset_space hs⟩
lemma IsMarked.iUnion {K : Geometry.SimplicialComplex ℝ E} {I : Sort*}
    {P : I → Set E} (hP : ∀ i, IsMarked K (P i)) : IsMarked K (⋃ i, P i) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨s, hs, hxs, hsub⟩ := hP i x hxi
  exact ⟨s, hs, hxs, hsub.trans (Set.subset_iUnion P i)⟩
lemma IsMarked.union {K : Geometry.SimplicialComplex ℝ E} {P Q : Set E}
    (hP : IsMarked K P) (hQ : IsMarked K Q) : IsMarked K (P ∪ Q) := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨s, hs, hxs, hsub⟩ := hP x hx
    exact ⟨s, hs, hxs, hsub.trans Set.subset_union_left⟩
  · obtain ⟨s, hs, hxs, hsub⟩ := hQ x hx
    exact ⟨s, hs, hxs, hsub.trans Set.subset_union_right⟩
lemma IsMarked.inter {K : Geometry.SimplicialComplex ℝ E} {P Q : Set E}
    (hP : IsMarked K P) (hQ : IsMarked K Q) : IsMarked K (P ∩ Q) := by
  classical
  intro x hx
  obtain ⟨s, hs, hxs, hsP⟩ := hP x hx.1
  obtain ⟨t, ht, hxt, htQ⟩ := hQ x hx.2
  have hxst : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    exact ⟨hxs, hxt⟩
  have hne : (s ∩ t).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxst⟩)
  refine ⟨s ∩ t, K.down_closed hs Finset.inter_subset_left hne, hxst, ?_⟩
  exact subset_inter ((convexHull_mono Finset.inter_subset_left).trans hsP)
    ((convexHull_mono Finset.inter_subset_right).trans htQ)
lemma IsMarked.refinement {K L : Geometry.SimplicialComplex ℝ E} {P : Set E}
    (hP : IsMarked K P)
    (hcover : ∀ s ∈ K.faces, IsMarked L (convexHull ℝ (s : Set E))) :
    IsMarked L P := by
  intro x hx
  obtain ⟨s, hs, hxs, hsP⟩ := hP x hx
  obtain ⟨t, ht, hxt, hts⟩ := hcover s hs x hxs
  exact ⟨t, ht, hxt, hts.trans hsP⟩
lemma card_lt_of_generic_hyperplane {s t : Finset E}
    (ht : AffineIndependent ℝ ((↑) : t → E))
    (hst : (t : Set E) ⊆ convexHull ℝ (s : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (heq : ∀ x ∈ t, f x = b) (hne : ∃ x ∈ s, f x ≠ b) :
    t.card < s.card := by
  apply ht.card_lt_card_of_affineSpan_lt_affineSpan
  have hle : affineSpan ℝ (t : Set E) ≤ affineSpan ℝ (s : Set E) := by
    apply affineSpan_le.mpr
    exact hst.trans (convexHull_subset_affineSpan (s : Set E))
  apply lt_of_le_of_ne hle
  intro h
  have he : (t : Set E).EqOn f.toAffineMap (AffineMap.const ℝ E b) := heq
  have he' := AffineMap.eqOn_affineSpan he
  obtain ⟨x, hx, hnx⟩ := hne
  apply hnx
  exact he' (by rw [h]; exact subset_affineSpan ℝ (s : Set E) hx)
lemma exists_branch_eq_on_simplex {I : Type*} (a : I → E →ₗ[ℝ] ℝ)
    (b : ℝ) {t : Finset E} (ht : t.Nonempty)
    (hle : ∀ x ∈ convexHull ℝ (t : Set E), ∀ i, a i x ≤ b)
    (heq : ∀ x ∈ convexHull ℝ (t : Set E), ∃ i, a i x = b) :
    ∃ i, ∀ x ∈ t, a i x = b := by
  obtain ⟨i, hi⟩ := heq (vertexMean t) (vertexMean_mem_convexHull ht)
  refine ⟨i, (linear_vertexMean_eq_iff (a i) ht ?_).mp hi⟩
  intro x hx
  exact hle x (subset_convexHull ℝ (t : Set E) hx) i
lemma card_lt_of_generic_max_level {I : Type*} (a : I → E →ₗ[ℝ] ℝ)
    (b : ℝ) {s t : Finset E} (ht : t.Nonempty)
    (hind : AffineIndependent ℝ ((↑) : t → E))
    (hst : (t : Set E) ⊆ convexHull ℝ (s : Set E))
    (hgeneric : ∀ i, ∃ x ∈ s, a i x ≠ b)
    (hle : ∀ x ∈ convexHull ℝ (t : Set E), ∀ i, a i x ≤ b)
    (heq : ∀ x ∈ convexHull ℝ (t : Set E), ∃ i, a i x = b) :
    t.card < s.card := by
  obtain ⟨i, hi⟩ := exists_branch_eq_on_simplex a b ht hle heq
  exact card_lt_of_generic_hyperplane hind hst (a i) b hi (hgeneric i)
end
section
open Set
lemma exists_generic_level {T I E : Type*} [Countable T] [Countable I]
    (s : T → Finset E) (a : I → E → ℝ) {r R : ℝ} (h : r < R) :
    ∃ b ∈ Set.Ioo r R, ∀ t i x, x ∈ s t → a i x ≠ b := by
  let bad : Set ℝ := ⋃ t, ⋃ i, a i '' (s t : Set E)
  have hbad : bad.Countable := by
    apply Set.countable_iUnion
    intro t
    apply Set.countable_iUnion
    intro i
    exact (s t).countable_toSet.image (a i)
  obtain ⟨b, hbnot, hb⟩ := hbad.dense_compl ℝ |>.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr h)
  refine ⟨b, hb, ?_⟩
  intro t i x hx he
  apply hbnot
  exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨i, x, hx, he⟩⟩
end
section
open Set Finset
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma RespectsSet.isMarked {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (h : RespectsSet K P) : IsMarked K (K.space ∩ P) := by
  intro x hx
  have hx' : x ∈ (restrictComplex K P).space := by
    rw [restrictComplex_space_of_respects K P h]
    exact hx
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx'
  refine ⟨s, hs.1, hxs, fun y hy => ⟨K.convexHull_subset_space hs.1 hy, ?_⟩⟩
  have he : (s : Set V) ∩ P = s := Set.inter_eq_left.mpr hs.2
  have hy' : y ∈ convexHull ℝ (s : Set V) ∩ P := by
    rw [h s hs.1, he]
    exact hy
  exact hy'.2
end
section
open Set Finset
section
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
lemma cutParents_singleton_finiteHull (K : Geometry.SimplicialComplex ℝ V)
    (s : Finset V) (hs : s ∈ K.faces) {I : Type*} [Fintype I]
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) :
    ∀ P ∈ cutParents {convexHull ℝ (s : Set V)} a b,
      ∃ t : Finset V, P = convexHull ℝ (t : Set V) := by
  classical
  let p : CutPatch K := ⟨{s},by simpa using hs⟩
  let L := finitePatch K p.val p.property
  have hsub : {convexHull ℝ (s : Set V)} ⊆
      complexParents L (finitePatch_finite K p.val p.property) := by
    intro P hP
    have hP' := Finset.mem_singleton.mp hP
    subst P
    exact (mem_complexParents _ _ _).mpr
      ⟨s,mem_finitePatch K p.val p.property (Finset.mem_singleton_self _),rfl⟩
  intro P hP
  exact cutParents_finiteHull_simplicial L (finitePatch_finite K p.val p.property) a b P
    (cutParents_mono hsub a b hP)
lemma canonicalCuts_linear_map (K : Geometry.SimplicialComplex ℝ V)
    (s : Finset V) (hs : s ∈ K.faces) (f : V →ₗ[ℝ] W) (hf : Function.Injective f)
    {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (a' : J → W →ₗ[ℝ] ℝ) (b' : J → ℝ)
    (ha : ∀ i, (a' (e i)).comp f = a i) (hb : ∀ i, b' (e i) = b i) :
    chainFaces (faceClosure (cutParents {convexHull ℝ ((s.map ⟨f,hf⟩) : Set W)} a' b'))
      canonicalCenter =
      (fun t : Finset V => t.map ⟨f,hf⟩) ''
        chainFaces (faceClosure (cutParents {convexHull ℝ (s : Set V)} a b)) canonicalCenter := by
  have hp : cutParents {convexHull ℝ ((s.map ⟨f,hf⟩) : Set W)} a' b' =
      (cutParents {convexHull ℝ (s : Set V)} a b).image (fun P => f '' P) := by
    rw [← cutParents_reindex _ a' b' e]
    have hcoe : convexHull ℝ ((s.map ⟨f,hf⟩) : Set W) = f '' convexHull ℝ (s : Set V) := by
      rw [Finset.coe_map]
      exact (f.toAffineMap.image_convexHull _).symm
    rw [hcoe,← Finset.image_singleton,cutParents_linear_image]
    congr 1
    · congr 1
      · exact funext ha
      · exact funext hb
  rw [hp]
  have hfinite := cutParents_singleton_finiteHull K s hs a b
  have hfaces := faceClosure_affine_map_injective f.toAffineMap hf _ hfinite
  change faceClosure ((cutParents {convexHull ℝ (s : Set V)} a b).image
    (fun P => f '' P)) = (faceClosure (cutParents {convexHull ℝ (s : Set V)} a b)).image
    (fun P => f '' P) at hfaces
  rw [hfaces]
  exact canonical_chainFaces_map_injective _ f.toAffineMap hf
    (faceClosure_finiteHull _ hfinite)
namespace LocalCutData
variable {K : Geometry.SimplicialComplex ℝ V} {K' : Geometry.SimplicialComplex ℝ W}
  {I J : Type*} (d : LocalCutData K I) (d' : LocalCutData K' J)
lemma globalComplex_map (f : V →ₗ[ℝ] W) (hf : Function.Injective f)
    (hk : ∀ s ∈ K.faces, s.map ⟨f,hf⟩ ∈ K'.faces)
    (e : ∀ s, s ∈ K.faces → d.relevant s ≃ d'.relevant (s.map ⟨f,hf⟩))
    (ha : ∀ s hs i, (d'.form (e s hs i)).comp f = d.form i)
    (hb : ∀ s hs i, d'.level (e s hs i) = d.level i)
    {u : Finset V} (hu : u ∈ d.globalComplex.faces) :
    u.map ⟨f,hf⟩ ∈ d'.globalComplex.faces := by
  obtain ⟨s,hs,hus⟩ := d.globalComplex_carrier hu
  have hlocal : u ∈ (restrictComplex d.globalComplex (convexHull ℝ (s : Set V))).faces :=
    ⟨hu,Subset.trans (subset_convexHull ℝ _) hus⟩
  rw [d.globalComplex_restrict_faces s hs] at hlocal
  have hlocal' := Set.mem_image_of_mem (fun t : Finset V => t.map ⟨f,hf⟩) hlocal
  rw [← canonicalCuts_linear_map K s hs f hf (e s hs)
    (fun i : d.relevant s => d.form i) (fun i : d.relevant s => d.level i)
    (fun j : d'.relevant (s.map ⟨f,hf⟩) => d'.form j)
    (fun j : d'.relevant (s.map ⟨f,hf⟩) => d'.level j) (ha s hs) (hb s hs),
    ← d'.globalComplex_restrict_faces _ (hk s hs)] at hlocal'
  exact hlocal'.1
end LocalCutData
end
open Set Finset
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma exists_smallest_carrier (K : Geometry.SimplicialComplex ℝ V) {x : V}
    (hx : x ∈ K.space) :
    ∃ s ∈ K.faces, x ∈ convexHull ℝ (s : Set V) ∧
      ∀ t ∈ K.faces, x ∈ convexHull ℝ (t : Set V) → s ⊆ t := by
  classical
  let P : ℕ → Prop := fun n => ∃ s ∈ K.faces,
    x ∈ convexHull ℝ (s : Set V) ∧ s.card = n
  have hex : ∃ n, P n := by
    obtain ⟨s,hs,hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact ⟨s.card,s,hs,hxs,rfl⟩
  obtain ⟨s,hs,hxs,hcard⟩ := Nat.find_spec hex
  refine ⟨s,hs,hxs,fun t ht hxt => ?_⟩
  have hxst : x ∈ convexHull ℝ ((s ∩ t : Finset V) : Set V) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    exact ⟨hxs,hxt⟩
  have hne : (s ∩ t).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x,hxst⟩)
  have hst := K.down_closed hs Finset.inter_subset_left hne
  have hmin : s.card ≤ (s ∩ t).card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨s ∩ t,hst,hxst,rfl⟩
  have he : s ∩ t = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hmin
  exact he ▸ Finset.inter_subset_right
namespace LocalCutData
variable {J : Type*} {K : Geometry.SimplicialComplex ℝ V} (d : LocalCutData K J)
lemma globalComplex_marked_le (j : J) :
    IsMarked d.globalComplex (K.space ∩ {x | d.form j x ≤ d.level j}) := by
  classical
  intro x hx
  have hxj : d.form j x ≤ d.level j := hx.2
  obtain ⟨s,hs,hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx.1
  let e : d.relevant s → Bool := fun i => decide (d.form i x ≤ d.level i)
  have hxc : x ∈ cutCell (convexHull ℝ (s : Set V))
      (fun i : d.relevant s => d.form i) (fun i : d.relevant s => d.level i) e := by
    refine ⟨hxs,fun i => ?_⟩
    simp only [signedForm,signedBound,e,decide_eq_true_eq]
    split_ifs with h
    · exact h
    · exact neg_le_neg (le_of_not_ge h)
  have hm := (d.globalComplex_cut_trace s hs e).isMarked
  obtain ⟨t,ht,hxt,htc⟩ := hm x ⟨d.globalComplex_space.symm ▸ hx.1,hxc⟩
  refine ⟨t,ht,hxt,fun y hy => ⟨d.globalComplex_space ▸
    d.globalComplex.convexHull_subset_space ht hy,?_⟩⟩
  change d.form j y ≤ d.level j
  by_cases hj : j ∈ d.relevant s
  · have he : e ⟨j,hj⟩ = true := by simpa only [e,decide_eq_true_eq] using hxj
    have hh := (htc hy).2.2 ⟨j,hj⟩
    simpa only [signedForm,signedBound,he,ite_true] using hh
  · rw [d.vanish s hs j hj y (htc hy).2.1]
    exact d.positive j
lemma globalComplex_marked_ge (j : J) :
    IsMarked d.globalComplex (K.space ∩ {x | d.level j ≤ d.form j x}) := by
  classical
  intro x hx
  have hxj : d.level j ≤ d.form j x := hx.2
  obtain ⟨s,hs,hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx.1
  let e : d.relevant s → Bool := fun i => decide (d.form i x < d.level i)
  have hxc : x ∈ cutCell (convexHull ℝ (s : Set V))
      (fun i : d.relevant s => d.form i) (fun i : d.relevant s => d.level i) e := by
    refine ⟨hxs,fun i => ?_⟩
    simp only [signedForm,signedBound,e,decide_eq_true_eq]
    split_ifs with h
    · exact h.le
    · exact neg_le_neg (le_of_not_gt h)
  have hm := (d.globalComplex_cut_trace s hs e).isMarked
  obtain ⟨t,ht,hxt,htc⟩ := hm x ⟨d.globalComplex_space.symm ▸ hx.1,hxc⟩
  refine ⟨t,ht,hxt,fun y hy => ⟨d.globalComplex_space ▸
    d.globalComplex.convexHull_subset_space ht hy,?_⟩⟩
  change d.level j ≤ d.form j y
  by_cases hj : j ∈ d.relevant s
  · have he : e ⟨j,hj⟩ = false := by simp only [e,decide_eq_false_iff_not,not_lt]; exact hxj
    have hh := (htc hy).2.2 ⟨j,hj⟩
    simpa only [signedForm,signedBound,he,Bool.false_eq_true,ite_false,
      LinearMap.neg_apply,neg_le_neg_iff] using hh
  · rw [d.vanish s hs j hj y (htc hy).2.1]
    simpa only [d.vanish s hs j hj x hxs] using hxj
lemma globalComplex_marked_eq (j : J) :
    IsMarked d.globalComplex (K.space ∩ {x | d.form j x = d.level j}) := by
  have hh := (d.globalComplex_marked_le j).inter (d.globalComplex_marked_ge j)
  convert hh using 1
  ext x
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨⟨h.1,h.2.le⟩,h.1,h.2.ge⟩,
    fun h => ⟨h.1.1,le_antisymm h.1.2 h.2.2⟩⟩
end LocalCutData
end
open Set Finset
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
open scoped Classical
omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma coe_filter_mem (s : Finset V) (P : Set V) :
    ((s.filter (· ∈ P) : Finset V) : Set V) = (s : Set V) ∩ P := by
  ext x
  simp
lemma respectsSet_face {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : RespectsSet K P) {s : Finset V} (hs : s ∈ K.faces)
    (hne : (convexHull ℝ (s : Set V) ∩ P).Nonempty) :
    s.filter (· ∈ P) ∈ K.faces := by
  classical
  apply K.down_closed hs (Finset.filter_subset _ _)
  have hh := hP s hs
  rw [hh] at hne
  rw [← coe_filter_mem s P] at hne
  exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp hne)
namespace LocalCutData
variable {J : Type*} {K : Geometry.SimplicialComplex ℝ V} (d : LocalCutData K J)
lemma globalComplex_carrier_in {P : Set V} (hP : RespectsSet K P)
    {s : Finset V} (hs : s ∈ d.globalComplex.faces) (hsP : (s : Set V) ⊆ P) :
    ∃ t ∈ K.faces, (t : Set V) ⊆ P ∧
      convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V) := by
  classical
  obtain ⟨t,ht,hst⟩ := d.globalComplex_carrier hs
  have hv : (s : Set V) ⊆ convexHull ℝ (t : Set V) ∩ P :=
    subset_inter ((subset_convexHull ℝ _).trans hst) hsP
  have hne : (convexHull ℝ (t : Set V) ∩ P).Nonempty :=
    (d.globalComplex.nonempty_of_mem_faces hs).to_set.mono hv
  refine ⟨t.filter (· ∈ P),respectsSet_face hP ht hne,?_,?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · apply convexHull_min
    · simpa only [coe_filter_mem] using (hP t ht ▸ hv)
    · exact convex_convexHull ℝ _
lemma globalComplex_preserves_respects {P : Set V} (hP : RespectsSet K P) :
    RespectsSet d.globalComplex P := by
  classical
  intro s hs
  obtain ⟨t,ht,hst⟩ := d.globalComplex_carrier hs
  by_cases hh : (convexHull ℝ (t : Set V) ∩ P).Nonempty
  · let u := t.filter (· ∈ P)
    have hu : u ∈ K.faces := respectsSet_face hP ht hh
    have huet : convexHull ℝ (u : Set V) = convexHull ℝ (t : Set V) ∩ P := by
      simpa only [u,coe_filter_mem] using (hP t ht).symm
    have htrace := d.globalComplex_trace u hu s hs
    have hleft : convexHull ℝ (s : Set V) ∩ convexHull ℝ (u : Set V) =
        convexHull ℝ (s : Set V) ∩ P := by
      rw [huet]
      rw [← Set.inter_assoc,Set.inter_eq_left.mpr hst]
    have hv : (s : Set V) ∩ convexHull ℝ (u : Set V) = (s : Set V) ∩ P := by
      rw [huet]
      have hsub := (subset_convexHull ℝ (s : Set V)).trans hst
      rw [← Set.inter_assoc,Set.inter_eq_left.mpr hsub]
    simpa only [hleft,hv] using htrace
  · have he : convexHull ℝ (s : Set V) ∩ P = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun y hy => hh ⟨y,hst hy.1,hy.2⟩)
    have hv : (s : Set V) ∩ P = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun y hy => hh ⟨y,
        hst (subset_convexHull ℝ _ hy.1),hy.2⟩)
    rw [he,hv,convexHull_empty]
end LocalCutData
structure UniversalCuts (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (J : Type*) where
  form : J → V →ₗ[ℝ] ℝ
  level : J → ℝ
  positive : ∀ j, 0 ≤ level j
  relevant : Finset V → Finset J
  vanish : ∀ s j, j ∉ relevant s →
    ∀ x ∈ convexHull ℝ (s : Set V), form j x = 0
namespace UniversalCuts
variable {J : Type*} (d : UniversalCuts V J)
def onComplex (K : Geometry.SimplicialComplex ℝ V) : LocalCutData K J :=
  ⟨d.form,d.level,d.positive,d.relevant,fun s _ => d.vanish s⟩
def localFaces (s : Finset V) : Set (Finset V) :=
  chainFaces (faceClosure (cutParents {convexHull ℝ (s : Set V)}
    (fun i : d.relevant s => d.form i) (fun i : d.relevant s => d.level i))) canonicalCenter
lemma mem_global_iff {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : RespectsSet K P) (s : Finset V) :
    s ∈ (restrictComplex (d.onComplex K).globalComplex P).faces ↔
      ∃ t ∈ (restrictComplex K P).faces, s ∈ d.localFaces t := by
  constructor
  · intro hs
    obtain ⟨t,ht,htP,hst⟩ := (d.onComplex K).globalComplex_carrier_in hP hs.1 hs.2
    refine ⟨t,⟨ht,htP⟩,?_⟩
    have hh : s ∈ (restrictComplex (d.onComplex K).globalComplex
        (convexHull ℝ (t : Set V))).faces :=
      ⟨hs.1,(subset_convexHull ℝ _).trans hst⟩
    rwa [(d.onComplex K).globalComplex_restrict_faces t ht] at hh
  · rintro ⟨t,⟨ht,htP⟩,hst⟩
    have hh : s ∈ (restrictComplex (d.onComplex K).globalComplex
        (convexHull ℝ (t : Set V))).faces := by
      rw [(d.onComplex K).globalComplex_restrict_faces t ht]
      exact hst
    have htrace := hP t ht
    have htconv : convexHull ℝ (t : Set V) ⊆ P := by
      have he : (t : Set V) ∩ P = t := Set.inter_eq_left.mpr htP
      rw [he] at htrace
      exact Set.inter_eq_left.mp htrace
    exact ⟨hh.1,hh.2.trans htconv⟩
end UniversalCuts
end Sparse.Cuts
end BassTrace
end
end OAI
end
/- Geometry interface for the port of OpenAI openai/math@3344da5. -/
open Set
namespace FiniteTraceCut
noncomputable section
open scoped Classical
def H : Prop := ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V],
 let c := fun s : Finset V => convexHull ℝ (s : Set V)
 let C := Geometry.SimplicialComplex ℝ V
 let tr := fun (K : C) (p : Set V) => {u ∈ K.faces | (u : Set V) ⊆ p}
 let clip := fun (s : Finset V) (A : Finset (Set V)) =>
   A.image (fun p => c s ∩ p)
 ∃ F : Finset V → Finset (Set V) → C, ∀ (s : Finset V) (A : Finset (Set V)),
   AffineIndependent ℝ ((↑) : s → V) → s.Nonempty →
   (∀ p ∈ A, ∃ (l : V →ₗ[ℝ] ℝ) (r : ℝ), p = {v | l v ≤ r}) →
   (F s A).faces.Finite ∧ (F s A).space = c s ∧
   (∀ u ∈ (F s A).faces, ∀ (l : V →ₗ[ℝ] ℝ) (r : ℝ), {v | l v ≤ r} ∈ A →
     c u ⊆ {v | l v ≤ r} ∨ c u ⊆ {v | r ≤ l v}) ∧
   (∀ t ⊆ s, t.Nonempty → ∀ B, (∀ p ∈ B, ∃ (l : V →ₗ[ℝ] ℝ) (r : ℝ), p = {v | l v ≤ r}) →
     (clip t A).filter (fun q => q.Nonempty ∧ q ≠ c t) =
       (clip t B).filter (fun q => q.Nonempty ∧ q ≠ c t) →
     tr (F s A) (c t) = (F t B).faces) ∧
   (∀ e : V ≃L[ℝ] V, (F (s.map e.toEquiv.toEmbedding) (A.image (fun p => e '' p))).faces =
     (fun u : Finset V => u.map e.toEquiv.toEmbedding) '' (F s A).faces)
end
end FiniteTraceCut
open Set
namespace FiniteTraceCut
open scoped Classical
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
abbrev hull (s : Finset V) := convexHull ℝ (s : Set V)
abbrev SC (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] := Geometry.SimplicialComplex ℝ V
variable (K : SC V) (L : Finset V → SC V)
variable (space : ∀ s ∈ K.faces, (L s).space = hull s)
variable (incl : ∀ s ∈ K.faces, ∀ t ⊆ s, t.Nonempty → L t ≤ L s)
private theorem common {u w : Finset V} {x : V} (M : SC V) (hu : u ∈ M.faces)
    (hw : w ∈ M.faces) (hx : x ∈ hull u ∩ hull w) :
    x ∈ hull (u ∩ w) ∧ u ∩ w ∈ M.faces := by
  have h : x ∈ hull (u ∩ w) := by simpa only [hull, Finset.coe_inter] using M.inter_subset_convexHull hu hw hx
  exact ⟨h,M.down_closed hw Finset.inter_subset_right (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x,h⟩))⟩
include space incl in
private theorem meet {s t u v : Finset V} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hu : u ∈ (L s).faces) (hv : v ∈ (L t).faces)
    (restrict : ∀ a ∈ K.faces, ∀ b ⊆ a, b.Nonempty → ∀ z ∈ (L a).faces,
      (z : Set V) ⊆ hull b → z ∈ (L b).faces) :
    hull u ∩ hull v ⊆ convexHull ℝ ((u : Set V) ∩ v) := by
  rintro x ⟨hxu,hxv⟩
  have sub {a z : Finset V} (ha : a ∈ K.faces) (hz : z ∈ (L a).faces) : hull z ⊆ hull a :=
    space a ha ▸ (L a).convexHull_subset_space hz
  obtain ⟨hx,hab⟩ := common K hs ht ⟨sub hs hu hxu,sub ht hv hxv⟩
  have hn := K.nonempty_of_mem_faces hab
  obtain ⟨w,hw,hxw⟩ := Geometry.SimplicialComplex.mem_space_iff.mp ((space _ hab).symm ▸ hx)
  have aux {a z : Finset V} (ha : a ∈ K.faces) (hh : s ∩ t ⊆ a) (hz : z ∈ (L a).faces)
      (hxz : x ∈ hull z) : x ∈ hull (z ∩ w) ∧ z ∩ w ∈ (L (s ∩ t)).faces := by
    obtain ⟨h1,h2⟩ := common (L a) hz (incl a ha _ hh hn hw) ⟨hxz,hxw⟩
    exact ⟨h1,restrict a ha _ hh hn _ h2 (fun y hy => sub hab hw (subset_convexHull ℝ _ (Finset.mem_inter.mp hy).2))⟩
  obtain ⟨h1,h2⟩ := aux hs Finset.inter_subset_left hu hxu
  obtain ⟨h3,h4⟩ := aux ht Finset.inter_subset_right hv hxv
  exact convexHull_mono (show (((u ∩ w : Finset V) : Set V) ∩ (v ∩ w : Finset V)) ⊆ ((u : Set V) ∩ v) from
    fun y hy => ⟨(Finset.mem_inter.mp hy.1).1,(Finset.mem_inter.mp hy.2).1⟩) ((L _).inter_subset_convexHull h2 h4 ⟨h1,h3⟩)
def glue (space : ∀ s ∈ K.faces, (L s).space = hull s) (incl : ∀ s ∈ K.faces, ∀ t ⊆ s, t.Nonempty → L t ≤ L s) (restrict : ∀ a ∈ K.faces, ∀ b ⊆ a, b.Nonempty → ∀ z ∈ (L a).faces,
      (z : Set V) ⊆ hull b → z ∈ (L b).faces) : SC V where
  faces := {u | ∃ s ∈ K.faces, u ∈ (L s).faces}
  indep := by rintro u ⟨s,hs,hu⟩; exact (L s).indep hu
  isRelLowerSet_faces := by
    rintro u ⟨s,hs,hu⟩
    exact ⟨(L s).nonempty_of_mem_faces hu,fun t h hn => ⟨s,hs,(L s).down_closed hu h hn⟩⟩
  inter_subset_convexHull := by
    rintro u v ⟨s,hs,hu⟩ ⟨t,ht,hv⟩
    exact meet K L space incl hs ht hu hv restrict
end FiniteTraceCut
open Set
namespace FiniteTraceCut
open scoped Classical
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
abbrev half (p : Set V) := ∃ (l : V →ₗ[ℝ] ℝ) (r : ℝ), p = {v | l v ≤ r}
noncomputable def active (s : Finset V) (A : Finset (Set V)) :=
  (A.image (fun p => hull s ∩ p)).filter (fun q => q.Nonempty ∧ q ≠ hull s)
theorem fromH (h : H) (K : SC V) (A : Finset V → Finset (Set V))
    (hh : ∀ s ∈ K.faces, ∀ p ∈ A s, half p)
    (compat : ∀ s ∈ K.faces, ∀ t ⊆ s, t.Nonempty → active t (A s) = active t (A t)) :
    ∃ (L : Finset V → SC V) (G : SC V), G.faces = {u | ∃ s ∈ K.faces, u ∈ (L s).faces} ∧
      G.space = K.space ∧ ∀ s ∈ K.faces, (L s).faces.Finite ∧ (L s).space = hull s ∧
      {u ∈ G.faces | (u : Set V) ⊆ hull s} = (L s).faces ∧
      ∀ u ∈ (L s).faces, ∀ (l : V →ₗ[ℝ] ℝ) (r : ℝ), {x | l x ≤ r} ∈ A s →
        hull u ⊆ {x | l x ≤ r} ∨ hull u ⊆ {x | r ≤ l x} := by
  obtain ⟨F,hF⟩ := h V
  let L := fun s => F s (A s)
  have spec := fun s (hs : s ∈ K.faces) => hF s (A s) (K.indep hs) (K.nonempty_of_mem_faces hs) (hh s hs)
  have sp : ∀ s ∈ K.faces, (L s).space = hull s := fun s hs => (spec s hs).2.1
  have sub {s u} (hs : s ∈ K.faces) (hu : u ∈ (L s).faces) : (u : Set V) ⊆ hull s :=
    (subset_convexHull ℝ _).trans (sp s hs ▸ (L s).convexHull_subset_space hu)
  have eqn (s) (hs : s ∈ K.faces) (t) (ht : t ⊆ s) (hn : t.Nonempty) :
      {u ∈ (L s).faces | (u : Set V) ⊆ hull t} = (L t).faces :=
    (spec s hs).2.2.2.1 t ht hn _ (hh t (K.down_closed hs ht hn)) (compat s hs t ht hn)
  let G := glue K L sp (fun s hs t ht hn u hu => ((eqn s hs t ht hn).symm ▸ hu : u ∈ {u ∈ (L s).faces | (u : Set V) ⊆ hull t}).1)
    (fun s hs t ht hn u hu hsub => eqn s hs t ht hn ▸ (show u ∈ {u ∈ (L s).faces | (u : Set V) ⊆ hull t} from ⟨hu,hsub⟩))
  refine ⟨L,G,rfl,?_,fun s hs => ⟨(spec s hs).1,sp s hs,?_,(spec s hs).2.2.1⟩⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨u,⟨s,hs,hu⟩,hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
      exact K.convexHull_subset_space hs (show x ∈ hull s from sp s hs ▸ (L s).convexHull_subset_space hu hx)
    · intro hx
      obtain ⟨s,hs,hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
      obtain ⟨u,hu,hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp ((sp s hs).symm ▸ (show x ∈ hull s from hx))
      exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨u,⟨s,hs,hu⟩,hx⟩
  · ext u
    constructor
    · rintro ⟨⟨t,ht,hu⟩,hus⟩
      have hsub : (u : Set V) ⊆ hull (s ∩ t) := by
        intro x hx
        simpa only [hull,Finset.coe_inter] using K.inter_subset_convexHull hs ht ⟨hus hx,sub ht hu hx⟩
      have hn := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp (((L t).nonempty_of_mem_faces hu).to_set.mono hsub))
      have hq : u ∈ (L (s ∩ t)).faces := eqn t ht _ Finset.inter_subset_right hn ▸ (show u ∈ {u ∈ (L t).faces | (u : Set V) ⊆ hull (s ∩ t)} from ⟨hu,hsub⟩)
      exact ((eqn s hs _ Finset.inter_subset_left hn).symm ▸ hq : u ∈ {u ∈ (L s).faces | (u : Set V) ⊆ hull (s ∩ t)}).1
    · exact fun hu => ⟨⟨s,hs,hu⟩,sub hs hu⟩
end FiniteTraceCut
open Set OAI.BassTrace.Sparse.Cuts
namespace FiniteTraceCut
noncomputable section
open scoped Classical
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
abbrev low (f : V →ₗ[ℝ] ℝ) (r : ℝ) := {x | f x ≤ r}
abbrev high (f : V →ₗ[ℝ] ℝ) (r : ℝ) := {x | r ≤ f x}
def Side (Q : Set V) (f : V →ₗ[ℝ] ℝ) (r : ℝ) := Q ⊆ low f r ∨ Q ⊆ high f r
lemma side_transfer {P Q : Set V} (hQ : Convex ℝ Q) (hQP : Q ⊆ P)
    {a f : V →ₗ[ℝ] ℝ} {b r : ℝ} (he : P ∩ low a b = P ∩ low f r)
    (hs : Side Q a b) : Side Q f r := by
  have iff' {x} (hx : x ∈ Q) : a x ≤ b ↔ f x ≤ r := by
    have h := Set.ext_iff.mp he x
    simpa only [mem_inter_iff, hQP hx, true_and,mem_setOf_eq] using h
  rcases hs with hs | hs
  · exact Or.inl fun x hx => (iff' hx).mp (hs hx)
  by_contra! hn
  change ¬ (_ ∨ _) at hn
  rw [not_or] at hn
  obtain ⟨y,hy,hyf⟩ := Set.not_subset.mp hn.1
  obtain ⟨x,hx,hxf⟩ := Set.not_subset.mp hn.2
  change ¬ f y ≤ r at hyf
  change ¬ r ≤ f x at hxf
  have hy' := lt_of_not_ge hyf
  have hx' := lt_of_not_ge hxf
  have hya : b < a y := lt_of_not_ge (fun h => hyf ((iff' hy).mp h))
  let u := (f y - r) / (f y - f x)
  let v := (r - f x) / (f y - f x)
  have hd : 0 < f y - f x := by linarith
  have hu : 0 < u := div_pos (sub_pos.mpr hy') hd
  have hv : 0 < v := div_pos (sub_pos.mpr hx') hd
  have huv : u + v = 1 := by dsimp [u,v]; rw [← add_div]; field_simp; ring
  have hz := hQ hx hy hu.le hv.le huv
  have hfz : f (u • x + v • y) ≤ r := by
    simp only [map_add,map_smul, smul_eq_mul]; dsimp [u,v]; apply le_of_eq; field_simp; ring
  have haz := (iff' hz).mpr hfz
  simp only [map_add,map_smul,smul_eq_mul] at haz
  have hxa : b ≤ a x := hs hx
  nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hxa),mul_pos hv (sub_pos.mpr hya),congrArg (· * b) huv]
variable {I J : Type} [Fintype I] [Fintype J]
def sides (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) := Finset.univ.image (fun i => low (a i) (b i))
lemma cutSide {P : Set V} (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (e : I → Bool) (i : I) :
    Side (cutCell P a b e) (a i) (b i) := by
  cases h : e i with
  | true => exact Or.inl fun x hx => by simpa [signedForm,signedBound,h] using hx.2 i
  | false => exact Or.inr fun x hx => by simpa [signedForm,signedBound,h] using hx.2 i
lemma normalize_side (s : Finset V) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (f : J → V →ₗ[ℝ] ℝ) (r : J → ℝ) (he : active s (sides f r) ⊆ active s (sides a b))
    (e : I → Bool) (j : J) : Side (cutCell (hull s) a b e) (f j) (r j) := by
  let p := low (f j) (r j)
  by_cases hn : (hull s ∩ p).Nonempty
  · by_cases ht : hull s ∩ p = hull s
    · exact Or.inl (Set.inter_subset_left.trans (Set.inter_eq_left.mp ht))
    have hp : hull s ∩ p ∈ active s (sides f r) := Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _
      (Finset.mem_image_of_mem _ (Finset.mem_univ j)),hn,ht⟩
    obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp (he hp)).1
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
    exact side_transfer ((convex_convexHull ℝ _).inter (convex_cell _ _)) Set.inter_subset_left heq (cutSide a b e i)
  · exact Or.inr fun x hx => (show r j ≤ f j x from le_of_not_ge fun h => hn ⟨x,hx.1,h⟩)
lemma coarsen (s : Finset V) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (f : J → V →ₗ[ℝ] ℝ) (r : J → ℝ) (he : active s (sides f r) ⊆ active s (sides a b))
    (Q) (hQ : Q ∈ cutParents {hull s} a b) : ∃ R ∈ cutParents {hull s} f r, Q ⊆ R := by
  obtain ⟨P,hP,e,rfl,hn⟩ := (mem_cutParents _ _ _ _).mp hQ
  obtain rfl := Finset.mem_singleton.mp hP
  let k : J → Bool := fun j => decide (cutCell (hull s) a b e ⊆ low (f j) (r j))
  have hh : cutCell (hull s) a b e ⊆ cutCell (hull s) f r k := by
    rintro x hx
    refine ⟨hx.1,fun j => ?_⟩
    have h := normalize_side s a b f r he e j
    by_cases hj : cutCell (hull s) a b e ⊆ low (f j) (r j)
    · simpa [signedForm,signedBound,k,hj] using hj hx
    · simpa [signedForm,signedBound,k,hj] using (h.resolve_left hj) hx
  exact ⟨_,(mem_cutParents _ _ _ _).mpr ⟨_,Finset.mem_singleton_self _,k,rfl,hn.mono hh⟩,hh⟩
lemma face_normalize (K : SC V) (s : Finset V) (hs : s ∈ K.faces)
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (f : J → V →ₗ[ℝ] ℝ) (r : J → ℝ)
    (he : active s (sides a b) = active s (sides f r)) :
    faceClosure (cutParents {hull s} a b) ⊆ faceClosure (cutParents {hull s} f r) := by
  intro X hX
  obtain ⟨Q,hQ,hn,hXQ⟩ := (mem_faceClosure _ (cutParents_singleton_finiteHull K s hs a b) _).mp hX
  obtain ⟨R,hR,hQR⟩ := coarsen s a b f r he.ge Q hQ
  obtain ⟨S,hS,hRS⟩ := coarsen s f r a b he.le R hR
  apply (mem_faceClosure _ (cutParents_singleton_finiteHull K s hs f r) _).mpr
  refine ⟨R,hR,hn,?_⟩
  obtain ⟨P,hP,e,rfl,_⟩ := (mem_cutParents _ _ _ _).mp hQ
  obtain ⟨P',hP',e',rfl,_⟩ := (mem_cutParents _ _ _ _).mp hS
  obtain rfl := Finset.mem_singleton.mp hP
  obtain rfl := Finset.mem_singleton.mp hP'
  have hh := (cutCell_inter_supporting (hull s) a b e' e).inter_restrict hRS
  rw [Set.inter_eq_right.mpr hQR] at hh
  obtain ⟨v,hv⟩ := cutParents_singleton_finiteHull K s hs f r R hR
  subst R
  exact hh.trans_finite_hull hXQ
end
end FiniteTraceCut
open Set OAI.BassTrace.Sparse.Cuts
namespace FiniteTraceCut
noncomputable section
open scoped Classical
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {I : Type} [Fintype I]
def simple (s : Finset V) (hi : AffineIndependent ℝ ((↑) : s → V)) : SC V where
  faces := {u | u.Nonempty ∧ u ⊆ s}
  indep := by intro u hu; exact hi.mono hu.2
  isRelLowerSet_faces := fun _ hu => ⟨hu.1,fun _ ht hn => ⟨hn,ht.trans hu.2⟩⟩
  inter_subset_convexHull := by intro u v hu hv; exact (hi.convexHull_inter hu.2 hv.2).symm.subset
abbrev flags (s : Finset V) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) :=
  chainFaces (faceClosure (cutParents {hull s} a b)) canonicalCenter
lemma realize (s : Finset V) (hi : AffineIndependent ℝ ((↑) : s → V)) (hn : s.Nonempty)
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) : ∃ L : SC V, L.faces.Finite ∧ L.space = hull s ∧
    ∀ t ⊆ s, t.Nonempty → {u ∈ L.faces | (u : Set V) ⊆ hull t} = flags t a b := by
  let K := simple s hi
  have hf : K.faces.Finite := s.powerset.finite_toSet.subset fun u hu => Finset.mem_powerset.mpr hu.2
  obtain ⟨B,hB,_⟩ := exists_canonical_simplicialCuts K hf a b
  refine ⟨B.complex,B.finite,?_,?_⟩
  · rw [B.space,complexParents_space]; ext x
    constructor
    · intro hx; obtain ⟨t,ht,hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
      exact convexHull_mono ht.2 hxt
    · exact fun hx => Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s,⟨hn,Finset.Subset.refl _⟩,hx⟩
  · intro t ht hnt; ext u; change u ∈ B.complex.faces ∧ _ ↔ _; rw [hB]
    exact canonical_chainFaces_restrict_parent _ _ _ (cutParents_finiteHull_simplicial K hf a b)
      (fun P hP Q hQ => simplicialParents_inter_supporting K _ hP hQ)
      ((mem_complexParents K hf _).mpr ⟨t,⟨hnt,ht⟩,rfl⟩) u
lemma flag_side (K : SC V) (s : Finset V) (hs : s ∈ K.faces) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    {u} (hu : u ∈ flags s a b) (i : I) : Side (hull u) (a i) (b i) := by
  obtain ⟨T,hn,ht,hch,rfl⟩ := hu
  obtain ⟨P,hm⟩ := T.exists_maximal hn
  have hall : ∀ Q ∈ T, Q ⊆ P := by
    intro Q hQ
    by_cases h : Q = P
    · exact h.subset
    rcases hch hQ hm.1 h with hh | hh
    · exact hh
    · exact hm.2 hQ hh
  have hf := cutParents_singleton_finiteHull K s hs a b
  obtain ⟨R,hR,_,hPR⟩ := (mem_faceClosure _ hf _).mp (ht hm.1)
  obtain ⟨Q,hQ,e,rfl,_⟩ := (mem_cutParents _ _ _ _).mp hR
  obtain rfl := Finset.mem_singleton.mp hQ
  have hsub : hull (T.image canonicalCenter) ⊆ cutCell (hull s) a b e := by
    apply convexHull_min _ ((convex_convexHull ℝ _).inter (convex_cell _ _))
    intro x hx; obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨R,hR,hne,hQR⟩ := (mem_faceClosure _ hf _).mp (ht hQ)
    obtain ⟨v,hv⟩ := faceClosure_finiteHull _ hf Q (ht hQ)
    apply hPR.subset; apply hall Q hQ
    rw [hv.2]; exact canonicalCenter_mem_finiteHull hv.1
  exact (cutSide a b e i).imp hsub.trans hsub.trans
end
end FiniteTraceCut
open Set OAI.BassTrace.Sparse.Cuts
namespace FiniteTraceCut
noncomputable section
open scoped Classical
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
def pick (p : Set V) : (V →ₗ[ℝ] ℝ) × ℝ := if h : half p then ⟨h.choose,h.choose_spec.choose⟩ else 0
lemma pick_ok {p : Set V} (hp : half p) : low (pick p).1 (pick p).2 = p := by
  simp only [pick,dif_pos hp]; exact hp.choose_spec.choose_spec.symm
abbrev forms (A : Finset (Set V)) (i : A) := (pick i.val).1
abbrev levels (A : Finset (Set V)) (i : A) := (pick i.val).2
lemma sides_eq {A : Finset (Set V)} (ha : ∀ p ∈ A, half p) : sides (forms A) (levels A) = A := by
  ext p; simp only [sides,Finset.mem_image,Finset.mem_univ,true_and]; constructor
  · rintro ⟨i,rfl⟩; rw [show low (forms A i) (levels A i) = i.val from pick_ok (ha _ i.2)]; exact i.2
  · intro hp; exact ⟨⟨p,hp⟩,pick_ok (ha _ hp)⟩
def operator (s : Finset V) (A : Finset (Set V)) : SC V := if h : AffineIndependent ℝ ((↑) : s → V) ∧ s.Nonempty then
  (realize s h.1 h.2 (forms A) (levels A)).choose else ⊥
lemma opSpec {s : Finset V} (hi : AffineIndependent ℝ ((↑) : s → V)) (hn : s.Nonempty) (A : Finset (Set V)) :
    (operator s A).faces.Finite ∧ (operator s A).space = hull s ∧
    ∀ t ⊆ s, t.Nonempty → {u ∈ (operator s A).faces | (u : Set V) ⊆ hull t} = flags t (forms A) (levels A) := by
  rw [operator,dif_pos (And.intro hi hn)]; exact (realize s hi hn (forms A) (levels A)).choose_spec
lemma opFaces {s : Finset V} (hi : AffineIndependent ℝ ((↑) : s → V)) (hn : s.Nonempty) (A : Finset (Set V)) :
    (operator s A).faces = flags s (forms A) (levels A) := by
  have h := opSpec hi hn A; rw [← h.2.2 s (Finset.Subset.refl _) hn]; ext u
  exact ⟨fun hu => ⟨hu,(subset_convexHull ℝ _).trans (h.2.1 ▸ (operator s A).convexHull_subset_space hu)⟩, And.left⟩
lemma flags_eq {I J : Type} [Fintype I] [Fintype J] (K : SC V) (s) (hs : s ∈ K.faces)
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (f : J → V →ₗ[ℝ] ℝ) (r : J → ℝ) (he : active s (sides a b) = active s (sides f r)) :
    flags s a b = flags s f r := congrArg (fun F => chainFaces F canonicalCenter)
      (Finset.Subset.antisymm (face_normalize K s hs a b f r he) (face_normalize K s hs f r a b he.symm))
theorem proved : H := by
  intro V _ _; dsimp only
  refine ⟨operator,?_⟩; intro s A hi hn ha
  let K := simple s hi
  have hs : s ∈ K.faces := ⟨hn,Finset.Subset.refl _⟩
  have h := opSpec hi hn A
  refine ⟨h.1,h.2.1,?_,?_,?_⟩
  · intro u hu f r hf
    let i : A := ⟨low f r,hf⟩
    rw [opFaces hi hn] at hu
    have hside := flag_side K s hs (forms A) (levels A) hu i
    exact side_transfer (convex_convexHull ℝ _) (Set.subset_univ _) (congrArg (Set.univ ∩ ·) (pick_ok (ha _ hf))) hside
  · intro t ht hnt B hb he
    rw [h.2.2 t ht hnt,opFaces (hi.mono ht) hnt]; apply flags_eq K t ⟨hnt,ht⟩
    simpa only [sides_eq ha,sides_eq hb] using (show active t A = active t B from he)
  · intro e
    let f := e.toLinearEquiv.toLinearMap
    let t := s.map e.toEquiv.toEmbedding
    let B := A.image (fun p => e '' p)
    let a' : A → V →ₗ[ℝ] ℝ := fun i => (forms A i).comp e.symm.toLinearEquiv.toLinearMap
    have image_eq (i : A) : low (a' i) (levels A i) = e '' i.val := by
      ext x; constructor
      · intro hx; exact ⟨e.symm x,(pick_ok (ha _ i.2)) ▸ (show e.symm x ∈ low (forms A i) (levels A i) from hx),e.apply_symm_apply x⟩
      · rintro ⟨y,hy,rfl⟩; change (forms A i) (e.symm (e y)) ≤ _; rw [e.symm_apply_apply]; exact (show y ∈ low (pick i.val).1 (pick i.val).2 from (pick_ok (ha _ i.2)).symm ▸ hy)
    have hh : sides a' (levels A) = B := by
      ext p; simp only [sides,B,Finset.mem_image,Finset.mem_univ,true_and]; constructor
      · rintro ⟨i,rfl⟩; exact ⟨i.val,i.2,(image_eq i).symm⟩
      · rintro ⟨q,hq,rfl⟩; exact ⟨⟨q,hq⟩,image_eq ⟨q,hq⟩⟩
    have hb : ∀ p ∈ B, half p := by
      intro p hp; obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      exact ⟨a' ⟨q,hq⟩,levels A ⟨q,hq⟩,(image_eq ⟨q,hq⟩).symm⟩
    have it : AffineIndependent ℝ ((↑) : t → V) := affineIndependent_map_finset f.toAffineMap e.injective hi
    have nt : t.Nonempty := hn.map
    change (operator t B).faces = _
    rw [opFaces it nt,opFaces hi hn,flags_eq (simple t it) t (show t ∈ (simple t it).faces from ⟨nt,Finset.Subset.refl _⟩) (forms B) (levels B) a' (levels A) (by rw [hh,sides_eq hb])]
    exact canonicalCuts_linear_map K s hs f e.injective (Equiv.refl _) _ _ _ _ (fun i => by ext x; simp [a',f]) (fun _ => rfl)
end
end FiniteTraceCut

open Set
namespace FiniteTraceCut
open scoped Classical
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
end FiniteTraceCut
open Set
namespace FiniteTraceCut
open scoped Classical
def H2 : Prop := ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V],
 let C := Geometry.SimplicialComplex ℝ V
 let c (s : Finset V) := convexHull ℝ (s : Set V)
 let tr (K : C) (p : Set V) := {u ∈ K.faces | (u : Set V) ⊆ p}
 ∀ (K : C) (L : Finset V → C), (∀ s ∈ K.faces, (L s).space = c s) →
 (∀ s ∈ K.faces, ∀ t ⊆ s, t.Nonempty → tr (L s) (c t) = (L t).faces) →
 ∃ G : C, G.faces = {u | ∃ s ∈ K.faces, u ∈ (L s).faces} ∧ G.space = K.space ∧
 ∀ s ∈ K.faces, tr G (c s) = (L s).faces ∧ ∀ u ∈ G.faces,
 c u ∩ c s = convexHull ℝ ((u : Set V) ∩ c s)
theorem glueLeaf : H2 := by
  intro V _ _; dsimp only; intro K L hspace eqn
  have sp : ∀ s ∈ K.faces, (L s).space = hull s := hspace
  have sub {s u} (hs : s ∈ K.faces) (hu : u ∈ (L s).faces) : (u : Set V) ⊆ hull s :=
    (subset_convexHull ℝ _).trans (show hull u ⊆ hull s from sp s hs ▸ (L s).convexHull_subset_space hu)
  let G := glue K L sp (fun s hs t ht hn u hu => ((eqn s hs t ht hn).symm ▸ hu : u ∈ {u ∈ (L s).faces | (u : Set V) ⊆ hull t}).1)
    (fun s hs t ht hn u hu hsub => eqn s hs t ht hn ▸ (show u ∈ {u ∈ (L s).faces | (u : Set V) ⊆ hull t} from ⟨hu,hsub⟩))
  refine ⟨G,rfl,?_,fun s hs => ⟨?_,?_⟩⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨u,⟨s,hs,hu⟩,hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
      exact K.convexHull_subset_space hs (show x ∈ hull s from sp s hs ▸ (L s).convexHull_subset_space hu hx)
    · intro hx
      obtain ⟨s,hs,hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
      obtain ⟨u,hu,hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp ((sp s hs).symm ▸ (show x ∈ hull s from hx))
      exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨u,⟨s,hs,hu⟩,hx⟩
  · ext u
    constructor
    · rintro ⟨⟨t,ht,hu⟩,hus⟩
      have hsub : (u : Set V) ⊆ hull (s ∩ t) := by
        intro x hx
        simpa only [hull,Finset.coe_inter] using K.inter_subset_convexHull hs ht ⟨hus hx,sub ht hu hx⟩
      have hn := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp (((L t).nonempty_of_mem_faces hu).to_set.mono hsub))
      have hq : u ∈ (L (s ∩ t)).faces := eqn t ht _ Finset.inter_subset_right hn ▸ (show u ∈ {u ∈ (L t).faces | (u : Set V) ⊆ hull (s ∩ t)} from ⟨hu,hsub⟩)
      exact ((eqn s hs _ Finset.inter_subset_left hn).symm ▸ hq : u ∈ {u ∈ (L s).faces | (u : Set V) ⊆ hull (s ∩ t)}).1
    · exact fun hu => ⟨⟨s,hs,hu⟩,sub hs hu⟩
  · intro u hu; apply le_antisymm
    · rintro x ⟨hxu,hxs⟩
      obtain ⟨w,hw,hxw⟩ := Geometry.SimplicialComplex.mem_space_iff.mp ((sp s hs).symm ▸ (show x ∈ hull s from hxs))
      have hg : w ∈ G.faces := ⟨s,hs,hw⟩
      exact convexHull_mono (Set.inter_subset_inter_right _ (sub hs hw)) (G.inter_subset_convexHull hu hg ⟨hxu,hxw⟩)
    · exact Set.subset_inter (convexHull_mono Set.inter_subset_left) (convexHull_min Set.inter_subset_right (convex_convexHull ℝ _))
end FiniteTraceCut
open Set
open scoped Classical
namespace GlobalCut
noncomputable section
def Target : Prop := ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V],
 let C := Geometry.SimplicialComplex ℝ V
 let c (s : Finset V) := convexHull ℝ (s : Set V)
 let hs (p : Set V) := ∃ (l : V →ₗ[ℝ] ℝ) (r : ℝ), p = {x | l x ≤ r}
 let act (s : Finset V) (A : Finset (Set V)) := (A.image (fun p => c s ∩ p)).filter (fun q => q.Nonempty ∧ q ≠ c s)
 ∃ F : Finset V → Finset (Set V) → C, ∀ (K : C) (A : Finset V → Finset (Set V)),
 (∀ s ∈ K.faces, ∀ p ∈ A s, hs p) → (∀ s ∈ K.faces, ∀ t ⊆ s, t.Nonempty → act t (A s) = act t (A t)) →
 ∃ G : C, G.faces = {u | ∃ s ∈ K.faces, u ∈ (F s (A s)).faces} ∧ G.space = K.space ∧
 ∀ s ∈ K.faces, let L := F s (A s)
 L.faces.Finite ∧ L.space = c s ∧ {u ∈ G.faces | (u : Set V) ⊆ c s} = L.faces ∧
 (∀ u ∈ G.faces, c u ∩ c s = convexHull ℝ ((u : Set V) ∩ c s)) ∧
 (∀ u ∈ L.faces, ∀ (l : V →ₗ[ℝ] ℝ) (r : ℝ), {x | l x ≤ r} ∈ A s → c u ⊆ {x | l x ≤ r} ∨ c u ⊆ {x | r ≤ l x}) ∧
 ∀ e : V ≃L[ℝ] V, (F (s.map e.toEquiv.toEmbedding) ((A s).image (fun p => e '' p))).faces = (fun u : Finset V => u.map e.toEquiv.toEmbedding) '' L.faces
end
end GlobalCut
open Set
open scoped Classical
namespace CutReduction
noncomputable section
def H1 : Prop := ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V],
 let c := fun s : Finset V => convexHull ℝ (s : Set V)
 let C := Geometry.SimplicialComplex ℝ V
 let tr := fun (K : C) (p : Set V) => {u ∈ K.faces | (u : Set V) ⊆ p}
 let clip := fun (s : Finset V) (A : Finset (Set V)) =>
   A.image (fun p => c s ∩ p)
 ∃ F : Finset V → Finset (Set V) → C, ∀ (s : Finset V) (A : Finset (Set V)),
   AffineIndependent ℝ ((↑) : s → V) → s.Nonempty →
   (∀ p ∈ A, ∃ (l : V →ₗ[ℝ] ℝ) (r : ℝ), p = {v | l v ≤ r}) →
   (F s A).faces.Finite ∧ (F s A).space = c s ∧
   (∀ u ∈ (F s A).faces, ∀ (l : V →ₗ[ℝ] ℝ) (r : ℝ), {v | l v ≤ r} ∈ A →
     c u ⊆ {v | l v ≤ r} ∨ c u ⊆ {v | r ≤ l v}) ∧
   (∀ t ⊆ s, t.Nonempty → ∀ B, (∀ p ∈ B, ∃ (l : V →ₗ[ℝ] ℝ) (r : ℝ), p = {v | l v ≤ r}) →
     (clip t A).filter (fun q => q.Nonempty ∧ q ≠ c t) =
       (clip t B).filter (fun q => q.Nonempty ∧ q ≠ c t) →
     tr (F s A) (c t) = (F t B).faces) ∧
   (∀ e : V ≃L[ℝ] V, (F (s.map e.toEquiv.toEmbedding) (A.image (fun p => e '' p))).faces =
     (fun u : Finset V => u.map e.toEquiv.toEmbedding) '' (F s A).faces)
def H2 : Prop := ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V],
 let C := Geometry.SimplicialComplex ℝ V
 let c (s : Finset V) := convexHull ℝ (s : Set V)
 let tr (K : C) (p : Set V) := {u ∈ K.faces | (u : Set V) ⊆ p}
 ∀ (K : C) (L : Finset V → C), (∀ s ∈ K.faces, (L s).space = c s) →
 (∀ s ∈ K.faces, ∀ t ⊆ s, t.Nonempty → tr (L s) (c t) = (L t).faces) →
 ∃ G : C, G.faces = {u | ∃ s ∈ K.faces, u ∈ (L s).faces} ∧ G.space = K.space ∧
 ∀ s ∈ K.faces, tr G (c s) = (L s).faces ∧ ∀ u ∈ G.faces,
 c u ∩ c s = convexHull ℝ ((u : Set V) ∩ c s)
theorem main : H1 → H2 → GlobalCut.Target := by
  intro h g V _ _; dsimp only
  obtain ⟨F,hF⟩ := h V
  refine ⟨F,?_⟩; intro K A ha hc
  have spec := fun s (hs : s ∈ K.faces) => hF s (A s) (K.indep hs) (K.nonempty_of_mem_faces hs) (ha s hs)
  obtain ⟨G,faces,space,trace⟩ := g V K (fun s => F s (A s)) (fun s hs => (spec s hs).2.1)
    (fun s hs t ht hn => (spec s hs).2.2.2.1 t ht hn _ (ha t (K.down_closed hs ht hn)) (hc s hs t ht hn))
  exact ⟨G,faces,space,fun s hs => ⟨(spec s hs).1,(spec s hs).2.1,(trace s hs).1,(trace s hs).2,(spec s hs).2.2.1,(spec s hs).2.2.2.2⟩⟩
end
end CutReduction
open Set
namespace GlobalCut
open scoped Classical
variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (R : Finset V → Finset I)
noncomputable def arr (s : Finset V) := (R s).image (fun i => {x | a i x ≤ b i})
noncomputable def active (s : Finset V) (A : Finset (Set V)) :=
  (A.image (fun p => convexHull ℝ (s : Set V) ∩ p)).filter (fun q => q.Nonempty ∧ q ≠ convexHull ℝ (s : Set V))
lemma active_subset (t : Finset V) (hb : ∀ i, 0 ≤ b i)
    (hz : ∀ s i, i ∉ R s → ∀ x ∈ convexHull ℝ (s : Set V), a i x = 0) (u v : Finset V)
    (hv : t ⊆ v) : active t (arr a b R u) ⊆ active t (arr a b R v) := by
  intro q hq
  obtain ⟨hq,hn,hh⟩ := Finset.mem_filter.mp hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
  have hm : i ∈ R v := by
    by_contra h
    apply hh; apply Set.inter_eq_left.mpr; intro x hx
    change a i x ≤ b i; rw [hz v i h x (convexHull_mono hv hx)]; exact hb i
  exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hm),hn,hh⟩
theorem apply_global (g : Target) (K : Geometry.SimplicialComplex ℝ V)
    (hb : ∀ i, 0 ≤ b i) (hz : ∀ s i, i ∉ R s → ∀ x ∈ convexHull ℝ (s : Set V), a i x = 0) :
    ∃ G : Geometry.SimplicialComplex ℝ V, G.space = K.space ∧ ∀ s ∈ K.faces,
      {u ∈ G.faces | (u : Set V) ⊆ convexHull ℝ (s : Set V)}.Finite ∧
      (∀ u ∈ G.faces, convexHull ℝ (u : Set V) ∩ convexHull ℝ (s : Set V) = convexHull ℝ ((u : Set V) ∩ convexHull ℝ (s : Set V))) ∧
      ∀ u ∈ G.faces, (u : Set V) ⊆ convexHull ℝ (s : Set V) → ∀ i,
        convexHull ℝ (u : Set V) ⊆ {x | a i x ≤ b i} ∨ convexHull ℝ (u : Set V) ⊆ {x | b i ≤ a i x} := by
  obtain ⟨F,hF⟩ := g V
  obtain ⟨G,_,hG,hL⟩ := hF K (arr a b R) (by
    intro s _ p hp; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp; exact ⟨a i,b i,rfl⟩) (by
    intro s hs t ht _; apply Finset.Subset.antisymm
    · exact active_subset a b R t hb hz s t (Finset.Subset.refl _)
    · exact active_subset a b R t hb hz t s ht)
  refine ⟨G,hG,?_⟩; intro s hs
  obtain ⟨hfin,_,he,htr,hside,_⟩ := hL s hs
  refine ⟨he ▸ hfin,htr,?_⟩; intro u hu hsub i
  by_cases hi : i ∈ R s
  · apply hside u (he ▸ (show u ∈ {u ∈ G.faces | (u : Set V) ⊆ convexHull ℝ (s : Set V)} from ⟨hu,hsub⟩)) (a i) (b i)
    exact Finset.mem_image_of_mem _ hi
  · left; intro x hx; change a i x ≤ _; rw [hz s i hi x (convexHull_min hsub (convex_convexHull ℝ _) hx)]; exact hb i
end GlobalCut

theorem conditionalGlobal (h : FiniteTraceCut.H) : GlobalCut.Target := CutReduction.main h FiniteTraceCut.glueLeaf

open Set
open scoped Pointwise Classical
theorem OMA.solution : OMA.R_mo_178849_R1.H1 := conditionalGlobal FiniteTraceCut.proved

/- Upstream license (OpenAI/math):
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
