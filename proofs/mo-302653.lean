import OMAStatements.S_mo_302653

/-!
Shortens the existing counterexample by @treybeathard-jpg: transfer compactness through
the retained homeomorphism and use singleton subsingletonness for the final contradiction.

Counterexample to sobriety of compact subspaces of sober spaces:
equip Option Nat with the topology whose nonempty open sets contain none
and have finite complement in Option.some, and take S = Set.range Option.some.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_302653.main) := by
  intro h
  let t : TopologicalSpace (Option ℕ) :=
    { IsOpen := fun U => U.Nonempty → none ∈ U ∧ (Option.some ⁻¹' U)ᶜ.Finite
      isOpen_univ := fun _ => ⟨Set.mem_univ _, by simp⟩
      isOpen_inter := fun s t hs ht ⟨x, hxs, hxt⟩ =>
        ⟨⟨(hs ⟨x, hxs⟩).1, (ht ⟨x, hxt⟩).1⟩, by
          simpa [Set.preimage_inter, Set.compl_inter] using
            (hs ⟨x, hxs⟩).2.union (ht ⟨x, hxt⟩).2⟩
      isOpen_sUnion := fun S hS ⟨x, u, huS, hxu⟩ =>
        ⟨Set.mem_sUnion_of_mem (hS u huS ⟨x, hxu⟩).1 huS,
          (hS u huS ⟨x, hxu⟩).2.subset
            (Set.compl_subset_compl.mpr (Set.preimage_mono (Set.subset_sUnion_of_mem huS)))⟩ }
  let _ : TopologicalSpace (Option ℕ) := t
  have hisOpen_compl_some : ∀ n : ℕ, IsOpen ({Option.some n}ᶜ : Set (Option ℕ)) := by
    intro n _
    refine ⟨by simp, ?_⟩
    have hpre : (Option.some ⁻¹' ({Option.some n}ᶜ : Set (Option ℕ)))ᶜ = {n} := by
      ext k
      simp
    rw [hpre]
    exact Set.finite_singleton n
  have _ : T0Space (Option ℕ) := by
    rw [t0Space_iff_inseparable]
    intro x y hxy
    rw [inseparable_iff_forall_isOpen] at hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some n =>
        have hmem := (hxy ({Option.some n}ᶜ) (hisOpen_compl_some n)).1 (by simp)
        simp at hmem
    | some n =>
      cases y with
      | none =>
        have hmem := (hxy ({Option.some n}ᶜ) (hisOpen_compl_some n)).2 (by simp)
        simp at hmem
      | some m =>
        by_contra hne
        have hmem := (hxy ({Option.some n}ᶜ) (hisOpen_compl_some n)).2
          (by simp [Ne.symm hne])
        simp at hmem
  have _ : QuasiSober (Option ℕ) := by
    refine ⟨fun {F} hF hFc => ?_⟩
    by_cases hU : F = Set.univ
    · subst hU
      refine ⟨none, ?_⟩
      apply Set.eq_univ_iff_forall.mpr
      intro x
      by_contra hx
      have hopen : IsOpen ((closure ({none} : Set (Option ℕ)))ᶜ) := isClosed_closure.isOpen_compl
      have hne : ((closure ({none} : Set (Option ℕ)))ᶜ).Nonempty := ⟨x, hx⟩
      exact (hopen hne).1 (subset_closure rfl)
    · have hFc' : none ∉ F ∧ (Option.some ⁻¹' F).Finite := by
        have := hFc.isOpen_compl (Set.nonempty_iff_ne_empty.mpr (mt Set.compl_empty_iff.mp hU))
        simpa [Set.preimage_compl, compl_compl] using this
      obtain ⟨x, hxF⟩ := hF.nonempty
      cases x with
      | none => exact absurd hxF hFc'.1
      | some n =>
        have hcl1 : IsClosed ({Option.some n} : Set (Option ℕ)) :=
          ⟨by simpa using hisOpen_compl_some n⟩
        have hcl2 : IsClosed (F \ {Option.some n}) := by
          refine ⟨fun _ => ⟨fun hmem => hFc'.1 hmem.1, ?_⟩⟩
          have hsub : (Option.some ⁻¹' (F \ {Option.some n})ᶜ)ᶜ ⊆ Option.some ⁻¹' F := by
            intro k hk
            simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_sdiff, Set.mem_singleton_iff,
              not_not] at hk
            exact hk.1
          exact hFc'.2.subset hsub
        have hsub_union : F ⊆ {Option.some n} ∪ (F \ {Option.some n}) := by
          intro y hy
          by_cases hyn : y = Option.some n
          · exact Or.inl hyn
          · exact Or.inr ⟨hy, hyn⟩
        rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hF.isPreirreducible)
            {Option.some n} (F \ {Option.some n}) hcl1 hcl2 hsub_union with hsub1 | hsub2
        · refine ⟨Option.some n, ?_⟩
          rw [IsGenericPoint, hcl1.closure_eq]
          exact Set.Subset.antisymm (Set.singleton_subset_iff.mpr hxF) hsub1
        · exact False.elim ((hsub2 hxF).2 rfl)
  let S : Set (Option ℕ) := Set.range Option.some
  let f : CofiniteTopology ℕ → Option ℕ := fun n => Option.some (CofiniteTopology.of.symm n)
  have hf_cont : Continuous f := by
    rw [continuous_def]
    intro U hU
    rw [CofiniteTopology.isOpen_iff]
    intro hne
    obtain ⟨a, ha⟩ := hne
    have hfin := (hU ⟨Option.some (CofiniteTopology.of.symm a), ha⟩).2
    have hpre : (f ⁻¹' U)ᶜ = CofiniteTopology.of.symm ⁻¹' (Option.some ⁻¹' U)ᶜ := rfl
    rw [hpre]
    exact hfin.preimage CofiniteTopology.of.symm.injective.injOn
  let e : CofiniteTopology ℕ ≃ₜ S :=
    { toFun := fun n => ⟨f n, CofiniteTopology.of.symm n, rfl⟩
      invFun := fun x => CofiniteTopology.of (x.1.getD 0)
      left_inv := fun n => by simp [f]
      right_inv := fun ⟨x, n, hn⟩ => by
        subst hn
        simp [f]
      continuous_toFun := hf_cont.subtype_mk _
      continuous_invFun := by
        rw [continuous_def]
        intro V hV
        rw [isOpen_induced_iff]
        by_cases hVe : V = ∅
        · refine ⟨∅, isOpen_empty, ?_⟩
          subst hVe
          simp
        · have hVfin : Vᶜ.Finite := (CofiniteTopology.isOpen_iff.mp hV) (Set.nonempty_iff_ne_empty.mpr hVe)
          refine ⟨insert none (Option.some '' (CofiniteTopology.of ⁻¹' V)), ?_, ?_⟩
          · intro _
            refine ⟨Set.mem_insert _ _, ?_⟩
            have hpre : (Option.some ⁻¹' insert none (Option.some '' (CofiniteTopology.of ⁻¹' V)))ᶜ =
                CofiniteTopology.of ⁻¹' Vᶜ := by
              ext k
              simp
            rw [hpre]
            exact hVfin.preimage CofiniteTopology.of.injective.injOn
          · ext ⟨x, n, hn⟩
            subst hn
            simp }
  let : CompactSpace S := e.compactSpace
  have _ : QuasiSober S := (h (Option ℕ) S (isCompact_iff_compactSpace.mpr inferInstance)).2
  have _ : QuasiSober (CofiniteTopology ℕ) := e.isClosedEmbedding.quasiSober
  have hgen := genericPoint_closure (CofiniteTopology ℕ)
  rw [isClosed_singleton.closure_eq] at hgen
  have hsub : (Set.univ : Set (CofiniteTopology ℕ)).Subsingleton := by
    rw [← hgen]
    exact Set.subsingleton_singleton
  have h01 := hsub (Set.mem_univ (CofiniteTopology.of (0 : ℕ)))
    (Set.mem_univ (CofiniteTopology.of (1 : ℕ)))
  exact Nat.zero_ne_one (CofiniteTopology.of.injective h01)
