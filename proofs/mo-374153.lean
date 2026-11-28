import OMAStatements.S_mo_374153
import Mathlib

/-! Retains @caa1982’s tripod counterexample. Standard open-segment membership supplies
positive coefficients; each nonzero ray parameter handles the separating-set signs uniformly. -/

open OMA.S_mo_374153

/-- The tripod: three segments from the origin. -/
def tripod : Set (ℝ × ℝ) :=
  segment ℝ 0 (1, 0) ∪ segment ℝ 0 (0, 1) ∪ segment ℝ 0 (-1, 0)

lemma tripod_cases (p : ℝ × ℝ) (hp : p ∈ tripod) :
    ∃ θ : ℝ, 0 ≤ θ ∧ (p = (θ, 0) ∨ p = (0, θ) ∨ p = (-θ, 0)) := by
  simp only [tripod, Set.mem_union, segment_eq_image, Set.mem_image, Set.mem_Icc] at hp
  rcases hp with ((⟨θ, ⟨h0, _⟩, rfl⟩ | ⟨θ, ⟨h0, _⟩, rfl⟩) | ⟨θ, ⟨h0, _⟩, rfl⟩)
  · exact ⟨θ, h0, Or.inl (by ext <;> simp)⟩
  · exact ⟨θ, h0, Or.inr (Or.inl (by ext <;> simp))⟩
  · exact ⟨θ, h0, Or.inr (Or.inr (by ext <;> simp))⟩

/-- If a path in the tripod avoids the origin, it cannot join points separated by `u`, `v`. -/
lemma key_sep {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] (ι : tripod → V) (hι : Topology.IsEmbedding ι)
    (hconv : Convex ℝ (Set.range ι)) (o x y : tripod) (ho : (o : ℝ × ℝ) = 0)
    (u v : Set (ℝ × ℝ)) (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v)
    (hcov : ∀ p ∈ tripod, p ≠ 0 → p ∈ u ∪ v) (hx : (x : ℝ × ℝ) ∈ u) (hy : (y : ℝ × ℝ) ∈ v) :
    ι o ∈ segment ℝ (ι x) (ι y) := by
  by_contra hno
  have hseg : ∀ t : unitInterval, AffineMap.lineMap (ι x) (ι y) (t : ℝ) ∈ Set.range ι := by
    intro t
    apply hconv.segment_subset ⟨x, rfl⟩ ⟨y, rfl⟩
    rw [segment_eq_image_lineMap]
    exact ⟨t, t.2, rfl⟩
  choose g hg using hseg
  have hgc : Continuous g := by
    rw [hι.continuous_iff]
    have : (ι ∘ g) = fun t : unitInterval => AffineMap.lineMap (ι x) (ι y) (t : ℝ) := by
      funext t; exact hg t
    rw [this]
    exact (AffineMap.lineMap_continuous).comp continuous_subtype_val
  have hg0 : g 0 = x := hι.injective (by rw [hg 0]; simp)
  have hg1 : g 1 = y := hι.injective (by rw [hg 1]; simp)
  set S : Set (ℝ × ℝ) := Set.range (fun t => ((g t : tripod) : ℝ × ℝ)) with hS
  have hSc : IsPreconnected S :=
    isPreconnected_range (continuous_subtype_val.comp hgc)
  have hSuv : S ⊆ u ∪ v := by
    rintro _ ⟨t, rfl⟩
    apply hcov _ (g t).2
    intro h0
    apply hno
    have : g t = o := Subtype.ext (by rw [h0, ho])
    rw [← this, hg t, segment_eq_image_lineMap]
    exact ⟨t, t.2, rfl⟩
  rcases hSc.subset_or_subset hu hv huv hSuv with h | h
  · have : (y : ℝ × ℝ) ∈ u := by rw [← hg1]; exact h ⟨1, rfl⟩
    exact Set.disjoint_left.mp huv this hy
  · have : (x : ℝ × ℝ) ∈ v := by rw [← hg0]; exact h ⟨0, rfl⟩
    exact Set.disjoint_left.mp huv hx this

lemma seg_coeffs {V : Type} [AddCommGroup V] [Module ℝ V] (P A B : V) (hA : P ≠ A) (hB : P ≠ B)
    (h : P ∈ segment ℝ A B) : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α • (A - P) + β • (B - P) = 0 := by
  obtain ⟨α, β, ha, hb, hab, rfl⟩ := mem_openSegment_of_ne_left_right hA.symm hB.symm h
  refine ⟨α, β, ha, hb, ?_⟩
  calc α • (A - (α • A + β • B)) + β • (B - (α • A + β • B))
      = (α • A + β • B) - (α + β) • (α • A + β • B) := by module
    _ = 0 := by rw [hab, one_smul, sub_self]

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_374153.main) := by
  intro h
  have hstar : StarConvex ℝ 0 tripod :=
    (((convex_segment _ _).starConvex (left_mem_segment ℝ _ _)).union
      ((convex_segment _ _).starConvex (left_mem_segment ℝ _ _))).union
      ((convex_segment _ _).starConvex (left_mem_segment ℝ _ _))
  have hcontr : ContractibleSpace tripod := hstar.contractibleSpace ⟨0, by simp [tripod, left_mem_segment]⟩
  obtain ⟨V, _, _, _, _, _, ι, hι, hconv⟩ := h tripod hcontr
  let o : tripod := ⟨0, by simp [tripod, left_mem_segment]⟩
  let a : tripod := ⟨(1, 0), by simp only [tripod]; exact Or.inl (Or.inl (right_mem_segment _ _ _))⟩
  let b : tripod := ⟨(0, 1), by simp only [tripod]; exact Or.inl (Or.inr (right_mem_segment _ _ _))⟩
  let c : tripod := ⟨(-1, 0), by simp only [tripod]; exact Or.inr (right_mem_segment _ _ _)⟩
  set u : Set (ℝ × ℝ) := {p | |p.2| < p.1}
  set v : Set (ℝ × ℝ) := {p | p.1 < |p.2|}
  set u' : Set (ℝ × ℝ) := {p | |p.1| < p.2}
  set v' : Set (ℝ × ℝ) := {p | p.2 < |p.1|}
  have hu : IsOpen u := isOpen_lt (continuous_abs.comp continuous_snd) continuous_fst
  have hv : IsOpen v := isOpen_lt continuous_fst (continuous_abs.comp continuous_snd)
  have hu' : IsOpen u' := isOpen_lt (continuous_abs.comp continuous_fst) continuous_snd
  have hv' : IsOpen v' := isOpen_lt continuous_snd (continuous_abs.comp continuous_fst)
  have huv : Disjoint u v := Set.disjoint_left.mpr fun p h1 h2 => by
    simp only [u, v, Set.mem_ofPred_eq] at h1 h2; linarith
  have huv' : Disjoint u' v' := Set.disjoint_left.mpr fun p h1 h2 => by
    simp only [u', v', Set.mem_ofPred_eq] at h1 h2; linarith
  have hcov : ∀ p ∈ tripod, p ≠ 0 → p ∈ u ∪ v := by
    intro p hp hp0
    obtain ⟨θ, hθ, h | h | h⟩ := tripod_cases p hp <;> subst h
    all_goals
      have hpos : 0 < θ := lt_of_le_of_ne hθ (by intro he; apply hp0; simp [← he])
      simp [u, v, abs_of_pos hpos, hpos]
  have hcov' : ∀ p ∈ tripod, p ≠ 0 → p ∈ u' ∪ v' := by
    intro p hp hp0
    obtain ⟨θ, hθ, h | h | h⟩ := tripod_cases p hp <;> subst h
    all_goals
      have hpos : 0 < θ := lt_of_le_of_ne hθ (by intro he; apply hp0; simp [← he])
      simp [u', v', abs_of_pos hpos, hpos]
  have sab := key_sep ι hι hconv o a b rfl u v hu hv huv hcov
    (by simp only [u, a, Set.mem_ofPred_eq]; norm_num) (by simp only [v, b, Set.mem_ofPred_eq]; norm_num)
  have sac := key_sep ι hι hconv o a c rfl u v hu hv huv hcov
    (by simp only [u, a, Set.mem_ofPred_eq]; norm_num) (by simp only [v, c, Set.mem_ofPred_eq]; norm_num)
  have sbc := key_sep ι hι hconv o b c rfl u' v' hu' hv' huv' hcov'
    (by simp only [u', b, Set.mem_ofPred_eq]; norm_num) (by simp only [v', c, Set.mem_ofPred_eq]; norm_num)
  have ne : ∀ x y : tripod, (x : ℝ × ℝ) ≠ y → ι x ≠ ι y := fun x y hxy h => hxy (by rw [hι.injective h])
  have noa := ne o a (by simp [o, a, Prod.ext_iff])
  have nob := ne o b (by simp [o, b, Prod.ext_iff])
  have noc := ne o c (by simp [o, c, Prod.ext_iff])
  obtain ⟨α, β, hα, hβ, h1⟩ := seg_coeffs _ _ _ noa nob sab
  obtain ⟨γ, δ, hγ, hδ, h2⟩ := seg_coeffs _ _ _ nob noc sbc
  obtain ⟨ε, ζ, hε, hζ, h3⟩ := seg_coeffs _ _ _ noa noc sac
  have hw : (α * γ * ζ + β * ε * δ) • (ι c - ι o) = 0 := by
    linear_combination (norm := module) (-(γ * ε)) • h1 + (β * ε) • h2 + (α * γ) • h3
  have hpos : α * γ * ζ + β * ε * δ ≠ 0 := by positivity
  rw [smul_eq_zero] at hw
  rcases hw with hw | hw
  · exact hpos hw
  · exact noc (sub_eq_zero.mp hw).symm
