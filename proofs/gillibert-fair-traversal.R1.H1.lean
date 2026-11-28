import OMAReductions.R_gillibert_fair_traversal_R1

/-!
# Fair traversal in the edge-transitive case

Problem source: Luc Gillibert, *Fair traversal conjecture*.
https://github.com/Gillibert/ConjecturesGillibert/blob/main/fair_traversal_conjecture.tex

Credit: @grp06
-/

open SimpleGraph

theorem OMA.solution : OMA.R_gillibert_fair_traversal_R1.H1 := by
  intro V _ _ G hcard htrans hpath
  classical
  obtain ⟨a, b, p, hp⟩ := hpath
  let A := G ≃g G
  letI : Finite A :=
    Finite.of_injective (fun α : A => (α : V → V))
      (fun _ _ h => RelIso.ext (congrFun h))
  letI : Fintype A := Fintype.ofFinite A
  let identity : A := RelIso.refl G.Adj
  let image (α : A) : G.Walk (α a) (α b) := p.map α.toHom
  let Uses (e : Sym2 V) (α : A) : Prop := e ∈ (image α).edges
  let count (e : Sym2 V) : ℕ := Fintype.card {α : A // Uses e α}
  have sameCount (e : Sym2 V) (he : e ∈ G.edgeSet)
      (e' : Sym2 V) (he' : e' ∈ G.edgeSet) : count e = count e' := by
    obtain ⟨φ, hφ⟩ := htrans e he e' he'
    let post : A ≃ A :=
      { toFun := fun α => α.trans φ
        invFun := fun α => α.trans φ.symm
        left_inv := fun α => RelIso.ext fun v => by
          change φ.symm (φ (α v)) = α v
          exact φ.symm_apply_apply (α v)
        right_inv := fun α => RelIso.ext fun v => by
          change φ (φ.symm (α v)) = α v
          exact φ.apply_symm_apply (α v) }
    have edgeComp (α : A) (d : Sym2 V) :
        Sym2.map (post α) d = Sym2.map φ (Sym2.map α d) :=
      (Sym2.map_map (f := (α : V → V)) (g := (φ : V → V)) d).symm
    have inj : Function.Injective (Sym2.map φ) :=
      Sym2.map.injective φ.toEquiv.injective
    have preserves (α : A) : Uses e α ↔ Uses e' (post α) := by
      change e ∈ (p.map α.toHom).edges ↔ e' ∈ (p.map (post α).toHom).edges
      simp only [Walk.edges_map]
      change e ∈ p.edges.map (Sym2.map α) ↔ e' ∈ p.edges.map (Sym2.map (post α))
      constructor
      · intro h
        obtain ⟨d, hd, hde⟩ := List.mem_map.mp h
        exact List.mem_map.mpr ⟨d, hd, by rw [edgeComp, hde, hφ]⟩
      · intro h
        obtain ⟨d, hd, hde⟩ := List.mem_map.mp h
        rw [edgeComp, ← hφ] at hde
        exact List.mem_map.mpr ⟨d, hd, inj hde⟩
    exact Fintype.card_congr (post.subtypeEquiv preserves)
  have hlen : 0 < p.edges.length := by
    rw [p.length_edges, hp.length_eq]
    omega
  let e₀ := p.edges[0]'hlen
  have he₀ : e₀ ∈ p.edges := List.getElem_mem hlen
  have he₀G : e₀ ∈ G.edgeSet := p.edges_subset_edgeSet he₀
  have hidentity : Uses e₀ identity := by
    change e₀ ∈ (p.map identity.toHom).edges
    rw [Walk.edges_map]
    change e₀ ∈ p.edges.map (Sym2.map id)
    simpa only [Sym2.map_id, List.map_id] using he₀
  have hr : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨identity⟩
  have hk : 0 < count e₀ := Fintype.card_pos_iff.mpr ⟨⟨identity, hidentity⟩⟩
  let index := (Fintype.equivFin A).symm
  refine ⟨Fintype.card A, count e₀, hr, hk, fun i => index i a, fun i => index i b,
    fun i => image (index i), ?_, ?_⟩
  · intro i
    exact Walk.IsHamiltonian.map (index i).toHom (index i).toEquiv.bijective hp
  · intro e he
    have hindex :
        Fintype.card {i : Fin (Fintype.card A) // Uses e (index i)} = count e :=
      Fintype.card_congr (index.subtypeEquiv fun _ => Iff.rfl)
    calc
      _ = Fintype.card {i : Fin (Fintype.card A) // Uses e (index i)} := by
        symm
        apply Fintype.card_of_subtype
        intro i
        rw [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩
      _ = count e := hindex
      _ = count e₀ := sameCount e he e₀ he₀G
