import OMAReductions.R_ReedOmegaDeltaChi_reed_omega_delta_chi_conjecture_for_finite_graphs_R1
import Mathlib

-- Credit: @LordMike

namespace OMAGreedyAux

theorem greedy_aux {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) :
    ∃ c : V → ℕ, (∀ v ∈ s, c v ≤ G.maxDegree) ∧
      ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨c, hc1, hc2⟩ := ih
    have hsub : s.filter (G.Adj a) ⊆ G.neighborFinset a := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [SimpleGraph.mem_neighborFinset]
      exact hx.2
    have hex : ∃ k ∈ Finset.range (G.maxDegree + 1), ∀ v ∈ s, G.Adj a v → c v ≠ k := by
      by_contra hcon
      have hsub2 : Finset.range (G.maxDegree + 1) ⊆ (s.filter (G.Adj a)).image c := by
        intro k hk
        by_contra hkF
        apply hcon
        refine ⟨k, hk, fun v hv hadj hck => hkF (Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hadj⟩, hck⟩)⟩
      have h1 := Finset.card_le_card hsub2
      have h2 := Finset.card_image_le (s := s.filter (G.Adj a)) (f := c)
      have h3 := Finset.card_le_card hsub
      have h4 : (G.neighborFinset a).card ≤ G.maxDegree := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        exact G.degree_le_maxDegree a
      rw [Finset.card_range] at h1
      omega
    obtain ⟨k, hk, hkF⟩ := hex
    have hk' : k ≤ G.maxDegree := by
      have := Finset.mem_range.mp hk
      omega
    refine ⟨Function.update c a k, ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with hv | hv
      · subst hv
        simp [hk']
      · have hva : v ≠ a := fun h => ha (h ▸ hv)
        rw [Function.update_apply, if_neg hva]
        exact hc1 v hv
    · intro u hu v hv huv
      by_cases hua : u = a <;> by_cases hva : v = a
      · rw [hua, hva] at huv
        exact absurd huv G.irrefl
      · have hv' : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hva
        have hav : G.Adj a v := by
          rw [← hua]
          exact huv
        rw [Function.update_apply, Function.update_apply, if_pos hua, if_neg hva]
        exact fun h => hkF v hv' hav h.symm
      · have hu' : u ∈ s := (Finset.mem_insert.mp hu).resolve_left hua
        have hau : G.Adj a u := by
          rw [← hva]
          exact huv.symm
        rw [Function.update_apply, Function.update_apply, if_neg hua, if_pos hva]
        exact hkF u hu' hau
      · have hu' : u ∈ s := (Finset.mem_insert.mp hu).resolve_left hua
        have hv' : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hva
        rw [Function.update_apply, Function.update_apply, if_neg hua, if_neg hva]
        exact hc2 u hu' v hv' huv

theorem colorable_maxDegree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : G.Colorable (G.maxDegree + 1) := by
  obtain ⟨c, hc1, hc2⟩ := greedy_aux G Finset.univ
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => (⟨c v, by have := hc1 v (Finset.mem_univ v); omega⟩ : Fin (G.maxDegree + 1)))
    (fun {v w} hvw h => hc2 v (Finset.mem_univ v) w (Finset.mem_univ w) hvw (congrArg Fin.val h))⟩

theorem chi_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : G.chromaticNumber ≤ ((G.maxDegree + 1 : ℕ) : ℕ∞) :=
  (SimpleGraph.chromaticNumber_le_iff_colorable).mpr (colorable_maxDegree G)

end OMAGreedyAux

theorem OMA.solution : OMA.R_ReedOmegaDeltaChi_reed_omega_delta_chi_conjecture_for_finite_graphs_R1.H1 := by
  intro V _ _ G _ h
  have hχ := OMAGreedyAux.chi_le G
  calc 2 * G.chromaticNumber ≤ 2 * ((G.maxDegree + 1 : ℕ) : ℕ∞) := by gcongr
    _ = ((2 * G.maxDegree + 2 : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ ((G.cliqueNum + G.maxDegree + 2 : ℕ) : ℕ∞) := by
        exact_mod_cast (by omega : 2 * G.maxDegree + 2 ≤ G.cliqueNum + G.maxDegree + 2)
    _ = (G.cliqueNum : ℕ∞) + (G.maxDegree : ℕ∞) + 2 := by norm_cast
