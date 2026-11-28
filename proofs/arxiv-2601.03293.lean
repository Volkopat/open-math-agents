import OMAStatements.S_arxiv_2601_03293
namespace OMA.P_arxiv_2601_03293

open OMA.S_arxiv_2601_03293

private lemma indepPoly_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : indepPoly G = indepPoly H := by
  classical
  unfold indepPoly
  apply Finset.sum_bij (fun S _ => S.map e.toEquiv.toEmbedding)
  · intro S hS
    rw [Finset.mem_filter] at hS ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro u hu v hv hadj
    rcases Finset.mem_map.mp hu with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp hv with ⟨b, hb, rfl⟩
    exact hS.2 a ha b hb (e.map_rel_iff.mp hadj)
  · intro S₁ _ S₂ _ h
    ext a
    constructor
    · intro ha
      have : e a ∈ S₂.map e.toEquiv.toEmbedding := h ▸ Finset.mem_map.mpr ⟨a, ha, rfl⟩
      rcases Finset.mem_map.mp this with ⟨b, hb, hba⟩
      exact (e.injective hba) ▸ hb
    · intro ha
      have : e a ∈ S₁.map e.toEquiv.toEmbedding := h.symm ▸ Finset.mem_map.mpr ⟨a, ha, rfl⟩
      rcases Finset.mem_map.mp this with ⟨b, hb, hba⟩
      exact (e.injective hba) ▸ hb
  · intro T hT
    rw [Finset.mem_filter] at hT
    refine ⟨T.map e.symm.toEquiv.toEmbedding, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro a ha b hb hadj
      rcases Finset.mem_map.mp ha with ⟨u, hu, rfl⟩
      rcases Finset.mem_map.mp hb with ⟨v, hv, rfl⟩
      exact hT.2 u hu v hv (e.symm.map_rel_iff.mp hadj)
    · ext u
      simp only [Finset.mem_map, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨a, ⟨v, hv, rfl⟩, rfl⟩
        simpa using hv
      · intro hu
        exact ⟨e.symm u, ⟨u, hu, rfl⟩, e.apply_symm_apply u⟩
  · intro S _
    rw [Finset.card_map]

private def gp7Map : Fin 7 ⊕ Fin 7 → Fin 7 ⊕ Fin 7
  | Sum.inl i => Sum.inr ⟨(2 * i.val) % 7, Nat.mod_lt _ (by omega)⟩
  | Sum.inr i => Sum.inl ⟨(2 * i.val) % 7, Nat.mod_lt _ (by omega)⟩

private def gp7Inv : Fin 7 ⊕ Fin 7 → Fin 7 ⊕ Fin 7
  | Sum.inl i => Sum.inr ⟨(4 * i.val) % 7, Nat.mod_lt _ (by omega)⟩
  | Sum.inr i => Sum.inl ⟨(4 * i.val) % 7, Nat.mod_lt _ (by omega)⟩

private instance (n k : ℕ) (x y : Fin n ⊕ Fin n) : Decidable ((genPetersen n k).Adj x y) := by
  unfold genPetersen
  cases x <;> cases y <;> dsimp <;> infer_instance

/-- Explicit graph isomorphism `GP(7, 3) ≃g GP(7, 2)`:
swaps outer cycle `u_i` and inner star `v_i` via `i ↦ 2i (mod 7)` (since `2 * 3 ≡ -1 (mod 7)`). -/
private def iso_GP7_3_2 : genPetersen 7 3 ≃g genPetersen 7 2 where
  toFun := gp7Map
  invFun := gp7Inv
  left_inv := by decide
  right_inv := by decide
  map_rel_iff' := by decide

private lemma counterexample : ¬ (type_of% @OMA.S_arxiv_2601_03293.main) := by
  intro hmain
  have h2 : IsRealRooted (indepPoly (genPetersen 7 2)) :=
    (hmain 7 2 (by omega) (by omega) (by omega)).mpr ⟨1, rfl⟩
  have h3 : ¬ IsRealRooted (indepPoly (genPetersen 7 3)) := by
    intro hr
    have hev : Even (3 : ℕ) := (hmain 7 3 (by omega) (by omega) (by omega)).mp hr
    rcases hev with ⟨m, hm⟩
    omega
  rw [indepPoly_eq_of_iso iso_GP7_3_2] at h3
  exact h3 h2

end OMA.P_arxiv_2601_03293

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2601_03293.main) :=
  OMA.P_arxiv_2601_03293.counterexample
