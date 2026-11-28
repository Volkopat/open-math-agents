import OMAStatements.S_mo_179145

-- Problem: When does a hypergraph represent maximal independent sets?
-- Upstream: formal-conjectures statements/mo-179145.lean:0 (declaration OMA.S_mo_179145.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_mo_179145 in
theorem OMA.solution : type_of% @OMA.S_mo_179145.main := by
  intro V H
  have csymm : ∀ x y, Cooccur H x y → Cooccur H y x := by
    rintro x y ⟨E, hE, hx, hy⟩; exact ⟨E, hE, hy, hx⟩
  constructor
  · rintro ⟨G, hG⟩
    refine ⟨?_, ?_⟩
    · intro E hE F hF hEF
      exact ((hG E).1 hE).2 F ((hG F).1 hF).1 hEF
    · intro S hS
      have hind : Independent G S := by
        intro x hx y hy hxy
        obtain ⟨E, hE, hxE, hyE⟩ := hS hx hy hxy
        exact ((hG E).1 hE).1 hxE hyE hxy
      have hz : ∀ c ⊆ {T | Independent G T}, IsChain (· ⊆ ·) c → c.Nonempty →
          ∃ ub ∈ {T | Independent G T}, ∀ s ∈ c, s ⊆ ub := by
        intro c hc hchain _
        refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
        intro x hx y hy hxy
        obtain ⟨a, ha, hxa⟩ := hx
        obtain ⟨b, hb, hyb⟩ := hy
        have hia : Independent G a := hc ha
        have hib : Independent G b := hc hb
        rcases hchain.total ha hb with h | h
        · exact hib (h hxa) hyb hxy
        · exact hia hxa (h hyb) hxy
      obtain ⟨m, hSm, hm⟩ := zorn_subset_nonempty {T | Independent G T} hz S hind
      refine ⟨m, (hG m).2 ⟨hm.1, ?_⟩, hSm⟩
      intro T hT hmT
      exact Set.Subset.antisymm hmT (hm.2 hT hmT)
  · rintro ⟨hinc, hconf⟩
    refine ⟨SimpleGraph.fromRel (fun x y => ¬ Cooccur H x y), ?_⟩
    have key : ∀ S : Set V,
        Independent (SimpleGraph.fromRel (fun x y => ¬ Cooccur H x y)) S ↔ Covered H S := by
      intro S
      constructor
      · intro h x hx y hy hxy
        have : ¬ (SimpleGraph.fromRel (fun x y => ¬ Cooccur H x y)).Adj x y := h hx hy hxy
        rw [SimpleGraph.fromRel_adj] at this
        by_contra hc
        exact this ⟨hxy, Or.inl hc⟩
      · intro h x hx y hy hxy hadj
        change (SimpleGraph.fromRel (fun x y => ¬ Cooccur H x y)).Adj x y at hadj
        rw [SimpleGraph.fromRel_adj] at hadj
        rcases hadj.2 with h1 | h1
        · exact h1 (h hx hy hxy)
        · exact h1 (csymm _ _ (h hx hy hxy))
    have cov : ∀ E ∈ H, Covered H E := fun E hE x hx y hy _ => ⟨E, hE, hx, hy⟩
    intro S
    constructor
    · intro hS
      refine ⟨(key S).2 (cov S hS), ?_⟩
      intro T hT hST
      obtain ⟨F, hF, hTF⟩ := hconf T ((key T).1 hT)
      have := hinc S hS F hF (hST.trans hTF)
      exact Set.Subset.antisymm hST (this ▸ hTF)
    · rintro ⟨hS, hmax⟩
      obtain ⟨E, hE, hSE⟩ := hconf S ((key S).1 hS)
      have := hmax E ((key E).2 (cov E hE)) hSE
      rw [this]; exact hE
