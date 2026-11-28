import OMAReductions.R_Erdos910_erdos_910_parts_ii_R1
import Mathlib

/-!
Step Erdos910.erdos_910.parts.ii.R1.H1: a connected set X in R^n, n at least 2, with an interior
point has more than continuum many connected subsets with more than one point. A ball around the
interior point contains the square of side r/3 spanned by two coordinate directions e_i, e_j. For
every set S of positions in [0, r/3], the comb made of the spine x + [0, r/3] e_i and the teeth
x + s e_i + [0, r/3] e_j for s in S is a union of connected sets through x, hence connected, and
x + s e_i + (r/3) e_j lies on it exactly when s is in S. So S determines the comb, and there are
2^c > c combs (Cantor).
-/
open scoped Cardinal

namespace OMA.Erdos910Comb

variable {n : ℕ}

lemma coord (x : EuclideanSpace ℝ (Fin n)) (i j k : Fin n) (s u : ℝ) :
    (x + s • EuclideanSpace.single i (1:ℝ) + u • EuclideanSpace.single j (1:ℝ)) k =
      x k + s * (if k = i then 1 else 0) + u * (if k = j then 1 else 0) := by
  simp

/-- The comb with spine positions in `S`: a union of connected sets through `x`. -/
lemma comb_spec (X : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) (δ : ℝ)
    (hδ : 0 < δ) (i j : Fin n) (hij : i ≠ j)
    (hX : ∀ s ∈ Set.Icc (0:ℝ) δ, ∀ u ∈ Set.Icc (0:ℝ) δ,
      x + s • EuclideanSpace.single i (1:ℝ) + u • EuclideanSpace.single j (1:ℝ) ∈ X)
    (S : Set ℝ) (hS : S ⊆ Set.Icc 0 δ) :
    let f : ℝ → ℝ → EuclideanSpace ℝ (Fin n) := fun s u =>
      x + s • EuclideanSpace.single i (1:ℝ) + u • EuclideanSpace.single j (1:ℝ)
    let spine := (fun t => f t 0) '' Set.Icc 0 δ
    let C := ⋃₀ (insert spine ((fun s => spine ∪ (f s) '' Set.Icc 0 δ) '' S))
    (C ⊆ X ∧ IsConnected C ∧ C.Nontrivial) ∧
      ∀ s ∈ Set.Icc (0:ℝ) δ, (f s δ ∈ C ↔ s ∈ S) := by
  intro f spine C
  have hspine : IsConnected spine :=
    (isConnected_Icc hδ.le).image _ (by fun_prop)
  have hx : x ∈ spine := ⟨0, ⟨le_rfl, hδ.le⟩, by simp [f]⟩
  have htooth : ∀ s, IsConnected ((f s) '' Set.Icc 0 δ) := fun s =>
    (isConnected_Icc hδ.le).image _ (by fun_prop)
  have hmeet : ∀ s ∈ Set.Icc (0:ℝ) δ, (spine ∩ (f s) '' Set.Icc 0 δ).Nonempty := fun s hs =>
    ⟨f s 0, ⟨s, hs, rfl⟩, ⟨0, ⟨le_rfl, hδ.le⟩, rfl⟩⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨T, hT, hpT⟩ := hp
    rcases hT with rfl | ⟨s, hs, rfl⟩
    · obtain ⟨t, ht, rfl⟩ := hpT
      exact hX t ht 0 ⟨le_rfl, hδ.le⟩
    · rcases hpT with ⟨t, ht, rfl⟩ | ⟨u, hu, rfl⟩
      · exact hX t ht 0 ⟨le_rfl, hδ.le⟩
      · exact hX s (hS hs) u hu
  · refine ⟨⟨x, spine, Set.mem_insert _ _, hx⟩, ?_⟩
    refine isPreconnected_sUnion x _ ?_ ?_
    · rintro T (rfl | ⟨s, hs, rfl⟩)
      · exact hx
      · exact Or.inl hx
    · rintro T (rfl | ⟨s, hs, rfl⟩)
      · exact hspine.isPreconnected
      · exact IsPreconnected.union' (hmeet s (hS hs)) hspine.isPreconnected (htooth s).isPreconnected
  · refine ⟨f 0 0, ⟨spine, Set.mem_insert _ _, 0, ⟨le_rfl, hδ.le⟩, rfl⟩,
      f δ 0, ⟨spine, Set.mem_insert _ _, δ, ⟨hδ.le, le_rfl⟩, rfl⟩, ?_⟩
    intro h
    have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) h
    simp only [f, coord] at this
    simp at this
    exact hδ.ne' this
  · intro s hs
    constructor
    · rintro ⟨T, hT, hpT⟩
      have hnot : f s δ ∉ spine := by
        rintro ⟨t, -, ht⟩
        have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v j) ht
        simp only [f, coord, if_neg hij.symm] at this
        simp at this
        exact hδ.ne' this
      rcases hT with rfl | ⟨s', hs', rfl⟩
      · exact absurd hpT hnot
      · rcases hpT with hp | ⟨u, -, hu⟩
        · exact absurd hp hnot
        · have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hu
          simp only [f, coord, if_neg hij] at this
          simp at this
          exact this ▸ hs'
    · intro hsS
      exact ⟨_, Or.inr ⟨s, hsS, rfl⟩, Or.inr ⟨δ, ⟨hδ.le, le_rfl⟩, rfl⟩⟩

theorem many_combs (X : Set (EuclideanSpace ℝ (Fin n))) (hn : 2 ≤ n)
    (hint : (interior X).Nonempty) :
    𝔠 < Cardinal.mk {Y : Set (EuclideanSpace ℝ (Fin n)) |
      Y ⊆ X ∧ IsConnected Y ∧ Y.Nontrivial} := by
  obtain ⟨x, hx⟩ := hint
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  set δ : ℝ := r / 3 with hδdef
  have hδ : 0 < δ := by positivity
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hX : ∀ s ∈ Set.Icc (0:ℝ) δ, ∀ u ∈ Set.Icc (0:ℝ) δ,
      x + s • EuclideanSpace.single i (1:ℝ) + u • EuclideanSpace.single j (1:ℝ) ∈ X := by
    intro s hs u hu
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_assoc, add_sub_cancel_left]
    calc ‖s • EuclideanSpace.single i (1:ℝ) + u • EuclideanSpace.single j (1:ℝ)‖
        ≤ ‖s • EuclideanSpace.single i (1:ℝ)‖ + ‖u • EuclideanSpace.single j (1:ℝ)‖ :=
          norm_add_le _ _
      _ = |s| + |u| := by simp [norm_smul]
      _ ≤ δ + δ := by
          rw [abs_of_nonneg hs.1, abs_of_nonneg hu.1]; exact add_le_add hs.2 hu.2
      _ < r := by rw [hδdef]; linarith
  have key := fun (T : Set (Set.Icc (0:ℝ) δ)) =>
    comb_spec X x δ hδ i j hij hX (Subtype.val '' T) (by rintro _ ⟨t, -, rfl⟩; exact t.2)
  let Φ : Set (Set.Icc (0:ℝ) δ) → {Y : Set (EuclideanSpace ℝ (Fin n)) |
      Y ⊆ X ∧ IsConnected Y ∧ Y.Nontrivial} := fun T => ⟨_, (key T).1⟩
  have hΦ : Function.Injective Φ := by
    intro T₁ T₂ h
    have h' := congrArg Subtype.val h
    ext t
    have e₁ := (key T₁).2 t.1 t.2
    have e₂ := (key T₂).2 t.1 t.2
    simp only [Φ] at h'
    rw [h'] at e₁
    have := e₁.symm.trans e₂
    simpa [Subtype.val_injective.mem_set_image] using this
  calc 𝔠 < 2 ^ 𝔠 := Cardinal.cantor 𝔠
    _ = Cardinal.mk (Set (Set.Icc (0:ℝ) δ)) := by
        rw [Cardinal.mk_set, Cardinal.mk_Icc_real hδ]
    _ ≤ _ := Cardinal.mk_le_of_injective hΦ

end OMA.Erdos910Comb

theorem OMA.solution : OMA.R_Erdos910_erdos_910_parts_ii_R1.H1 := by
  intro n X _ hn hint
  exact OMA.Erdos910Comb.many_combs X hn hint
