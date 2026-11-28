import OMAStatements.S_mo_459015

-- Problem: MathOverflow 459015, deficiency version of Hall's theorem (Ore / Koenig).
-- (=>) the matched part of S injects into N(S), and S minus the matched set has at most n - k elements.
-- (<=) add n - k dummy vertices on the Y side, joined to every x. The deficiency condition is Hall's
-- condition for this graph, so Hall's theorem gives an injection g of X into Y + dummies along edges.
-- At most n - k vertices go to dummies, so at least k go into Y: any k of them form the matching.

theorem OMA.solution : type_of% @OMA.S_mo_459015.main := by
  intro X Y _ _ _ _ E _ n k hX hY hk
  classical
  constructor
  · rintro ⟨S0, hS0, f, hinj, hE⟩ S
    have h1 : (S ∩ S0).card ≤ (Finset.univ.filter fun y => ∃ x ∈ S, E x y).card := by
      rw [← Finset.card_image_of_injOn (hinj.mono (by intro x hx; exact (Finset.mem_inter.mp hx).2))]
      apply Finset.card_le_card
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hx' := Finset.mem_inter.mp hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, hx'.1, hE x hx'.2⟩
    have h2 : (S \ S0).card ≤ n - k := by
      have : (S \ S0).card ≤ (Finset.univ \ S0).card :=
        Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ S) le_rfl)
      rw [Finset.card_univ_sdiff, hX, hS0] at this
      exact this
    have h3 := Finset.card_inter_add_card_sdiff S S0
    omega
  · intro hH
    let t : X → Finset (Y ⊕ Fin (n - k)) := fun x =>
      (Finset.univ.filter fun y => E x y).disjSum Finset.univ
    have hall : ∀ s : Finset X, s.card ≤ (s.biUnion t).card := by
      intro s
      rcases s.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
      · simp
      have hsub : (Finset.univ.filter fun y => ∃ x ∈ s, E x y).disjSum
          (Finset.univ : Finset (Fin (n - k))) ⊆ s.biUnion t := by
        intro z hz
        rw [Finset.mem_biUnion]
        rcases Finset.mem_disjSum.mp hz with ⟨y, hy, rfl⟩ | ⟨j, -, rfl⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          obtain ⟨x, hx, hxy⟩ := hy
          exact ⟨x, hx, by simp [t, hxy]⟩
        · exact ⟨x0, hx0, by simp [t]⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_disjSum, Finset.card_univ, Fintype.card_fin] at this
      exact (hH s).trans this
    obtain ⟨g, hg, hgt⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
    let S1 : Finset X := Finset.univ.filter fun x => (g x).isLeft
    have hS1 : k ≤ S1.card := by
      have hc : (Finset.univ.filter fun x => ¬ (g x).isLeft).card ≤ n - k := by
        have : (Finset.univ.filter fun x => ¬ (g x).isLeft).card
            ≤ ((Finset.univ : Finset (Fin (n - k))).map (Function.Embedding.inr (α := Y))).card := by
          apply Finset.card_le_card_of_injOn g
          · intro x hx
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Bool.not_eq_true,
              Sum.isLeft_eq_false] at hx
            obtain ⟨j, hj⟩ := Sum.isRight_iff.mp hx
            simp [hj]
          · exact hg.injOn
        simpa using this
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X))
        (fun x => (g x).isLeft = true)
      rw [Finset.card_univ, hX] at this
      show k ≤ (Finset.univ.filter fun x => (g x).isLeft = true).card
      have hnk : n - k + k = n := Nat.sub_add_cancel hk
      omega
    obtain ⟨S, hSS1, hSk⟩ := Finset.exists_subset_card_eq hS1
    have e : X ≃ Y := Fintype.equivOfCardEq (hX.trans hY.symm)
    refine ⟨S, hSk, fun x => Sum.elim id (fun _ => e x) (g x), ?_, ?_⟩
    · intro x hx x' hx' hxx
      have hl := (Finset.mem_filter.mp (hSS1 hx)).2
      have hl' := (Finset.mem_filter.mp (hSS1 hx')).2
      obtain ⟨y, hy⟩ := Sum.isLeft_iff.mp hl
      obtain ⟨y', hy'⟩ := Sum.isLeft_iff.mp hl'
      simp only [hy, hy', Sum.elim_inl, id] at hxx
      apply hg
      rw [hy, hy', hxx]
    · intro x hx
      have hl := (Finset.mem_filter.mp (hSS1 hx)).2
      obtain ⟨y, hy⟩ := Sum.isLeft_iff.mp hl
      have := hgt x
      rw [hy] at this
      simp only [t, Finset.inl_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and] at this
      simpa [hy] using this
