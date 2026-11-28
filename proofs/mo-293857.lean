import OMAStatements.S_mo_293857

open OMA.S_mo_293857 Set MeasureTheory
open scoped Topology

theorem OMA.solution : type_of% @OMA.S_mo_293857.main := by
  refine ⟨{p : BaireSequences × BaireSequences | eventuallyEqualAtAllIndices p.1 p.2},
    ?_, ?_, ?_, ?_⟩
  · have hP : {p : BaireSequences × BaireSequences | eventuallyEqualAtAllIndices p.1 p.2} =
        ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n),
          (fun p : BaireSequences × BaireSequences => (p.1 n, p.2 n)) ⁻¹'
            {q : ℕ × ℕ | q.1 = q.2} := by
      ext ⟨x, y⟩
      constructor
      · rintro ⟨N, hN⟩
        exact mem_iUnion.mpr ⟨N, mem_iInter.mpr fun n => mem_iInter.mpr fun hn => hN n hn⟩
      · intro h
        rcases mem_iUnion.mp h with ⟨N, hN⟩
        exact ⟨N, fun n hn => mem_iInter.mp (mem_iInter.mp hN n) hn⟩
    rw [hP]
    refine MeasurableSet.iUnion fun N =>
      MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => ?_
    exact MeasurableSet.of_discrete.preimage
      (((measurable_pi_apply n).comp measurable_fst).prodMk
        ((measurable_pi_apply n).comp measurable_snd))
  · intro x y ⟨N, hN⟩
    ext z
    constructor
    · rintro ⟨M, hM⟩
      refine ⟨max N M, fun n hn => ?_⟩
      exact (hN n (le_of_max_le_left hn)).symm.trans (hM n (le_of_max_le_right hn))
    · rintro ⟨M, hM⟩
      refine ⟨max N M, fun n hn => ?_⟩
      exact (hN n (le_of_max_le_left hn)).trans (hM n (le_of_max_le_right hn))
  · intro hall
    have h01 := hall (fun _ => 0) (fun _ => 1)
    have hmem : (fun _ : ℕ => 0) ∈ verticalSection
        {p : BaireSequences × BaireSequences | eventuallyEqualAtAllIndices p.1 p.2}
        (fun _ => 0) := ⟨0, fun _ _ => rfl⟩
    rw [h01] at hmem
    rcases hmem with ⟨N, hN⟩
    have hcontra := hN N le_rfl
    exact Nat.one_ne_zero hcontra
  · intro S hS
    have hcount : S.Countable := by
      rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
      · exact Set.countable_empty
      · have hsub : S ⊆ ⋃ N : ℕ, {y : BaireSequences | ∀ n, N ≤ n → x₀ n = y n} := by
          intro y hy
          have hmem : y ∈ verticalSection
              {p : BaireSequences × BaireSequences | eventuallyEqualAtAllIndices p.1 p.2} y :=
            ⟨0, fun _ _ => rfl⟩
          rw [hS y hy x₀ hx₀] at hmem
          rcases hmem with ⟨N, hN⟩
          exact Set.mem_iUnion.mpr ⟨N, hN⟩
        refine (Set.countable_iUnion fun N => ?_).mono hsub
        rw [← Set.countable_coe_iff]
        refine Function.Injective.countable
          (f := fun (y : {y : BaireSequences | ∀ n, N ≤ n → x₀ n = y n}) (i : Fin N) =>
            y.1 i.val) ?_
        intro y₁ y₂ heq
        apply Subtype.ext
        funext n
        by_cases hn : n < N
        · exact congrFun heq ⟨n, hn⟩
        · have hge : N ≤ n := Nat.le_of_not_lt hn
          rw [← y₁.2 n hge, ← y₂.2 n hge]
    constructor
    · have hS_eq : S = ⋃ x ∈ S, ({x} : Set BaireSequences) := by
        ext y
        constructor
        · intro hy
          exact Set.mem_biUnion hy rfl
        · intro hy
          rcases Set.mem_iUnion₂.mp hy with ⟨x, hx, hxy⟩
          rw [Set.mem_singleton_iff.mp hxy]
          exact hx
      rw [hS_eq]
      refine isMeagre_biUnion hcount fun x _ => ?_
      apply IsNowhereDense.isMeagre
      rw [IsNowhereDense, isClosed_singleton.closure_eq, Set.eq_empty_iff_forall_notMem]
      intro y hy
      have hyx : y = x := Set.mem_singleton_iff.mp (interior_subset hy)
      subst hyx
      rcases isOpen_pi_iff.mp isOpen_interior y hy with ⟨I, u, hu, hsub⟩
      let m : ℕ := I.sup id + 1
      have hm : m ∉ I := by
        intro hmI
        have hle : m ≤ I.sup id := Finset.le_sup (f := id) hmI
        exact Nat.not_succ_le_self (I.sup id) hle
      let z : BaireSequences := Function.update y m (y m + 1)
      have hz_mem : z ∈ (I : Set ℕ).pi u := by
        intro i hi
        have hne : i ≠ m := fun h => hm (h ▸ hi)
        simp only [z, Function.update_of_ne hne]
        exact (hu i hi).2
      have hzy : z = y := Set.mem_singleton_iff.mp (interior_subset (hsub hz_mem))
      have hzm : z m = y m := congrFun hzy m
      simp only [z, Function.update_self] at hzm
      exact Nat.succ_ne_self (y m) hzm
    · intro μ hμ
      have : NullSingletonClass μ := hμ
      exact hcount.measure_zero μ
