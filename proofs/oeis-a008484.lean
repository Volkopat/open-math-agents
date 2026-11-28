import OMAStatements.S_oeis_a008484

private lemma multiset_sum_sub_two_add {m : Multiset ℕ} (hm : ∀ i ∈ m, 2 ≤ i) :
    (m.map (· - 2)).sum + 2 * Multiset.card m = m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.mem_cons, forall_eq_or_imp] at hm
    have hih := ih hm.2
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    omega

private lemma multiset_sum_add_two {m : Multiset ℕ} :
    (m.map (· + 2)).sum = m.sum + 2 * Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a008484.main := by
  intro n
  refine Finset.card_bij
    (fun p hp =>
      { parts := p.parts.map (· - 2) + Multiset.replicate (2 * Multiset.card p.parts) 1
        parts_pos := by
          intro i hi
          rw [Multiset.mem_add] at hi
          rcases hi with hi | hi
          · rw [Multiset.mem_map] at hi
            rcases hi with ⟨j, hj, rfl⟩
            have hj4 : 4 ≤ j := (Finset.mem_filter.mp hp).2 j hj
            omega
          · rw [Multiset.mem_replicate] at hi
            omega
        parts_sum := by
          rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one]
          have h4 : ∀ j ∈ p.parts, 2 ≤ j := fun j hj => by
            have := (Finset.mem_filter.mp hp).2 j hj
            omega
          rw [multiset_sum_sub_two_add h4, p.parts_sum] })
    ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hnot : (p.parts.map (· - 2)).count 1 = 0 := by
      rw [Multiset.count_eq_zero, Multiset.mem_map]
      rintro ⟨j, hj, hj1⟩
      have hj4 : 4 ≤ j := (Finset.mem_filter.mp hp).2 j hj
      omega
    simp only [Multiset.count_add, hnot, zero_add, Multiset.count_replicate_self,
      Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
    omega
  · intro p₁ hp₁ p₂ hp₂ hEq
    have hparts := congrArg (fun p : Nat.Partition n => p.parts.filter (· ≠ 1)) hEq
    dsimp only at hparts
    have hfilt (p : Nat.Partition n) (hp : p ∈ Finset.univ.filter fun p : Nat.Partition n =>
        ∀ i ∈ p.parts, 4 ≤ i) :
        (p.parts.map (· - 2) + Multiset.replicate (2 * Multiset.card p.parts) 1).filter (· ≠ 1) =
          p.parts.map (· - 2) := by
      rw [Multiset.filter_add, Multiset.filter_eq_self.mpr, Multiset.filter_eq_nil.mpr, add_zero]
      · intro i hi
        rw [Multiset.mem_replicate] at hi
        omega
      · intro i hi
        rw [Multiset.mem_map] at hi
        rcases hi with ⟨j, hj, rfl⟩
        have hj4 : 4 ≤ j := (Finset.mem_filter.mp hp).2 j hj
        omega
    rw [hfilt p₁ hp₁, hfilt p₂ hp₂] at hparts
    have hmap := congrArg (Multiset.map (· + 2)) hparts
    have hback (p : Nat.Partition n) (hp : p ∈ Finset.univ.filter fun p : Nat.Partition n =>
        ∀ i ∈ p.parts, 4 ≤ i) :
        (p.parts.map (· - 2)).map (· + 2) = p.parts := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id' p.parts]
      apply Multiset.map_congr rfl
      intro j hj
      have hj4 : 4 ≤ j := (Finset.mem_filter.mp hp).2 j hj
      simp only [Function.comp_apply]
      omega
    rw [hback p₁ hp₁, hback p₂ hp₂] at hmap
    exact Nat.Partition.ext hmap
  · intro q hq
    have hq_cond : 3 * q.parts.count 1 = 2 * Multiset.card q.parts :=
      (Finset.mem_filter.mp hq).2
    have hsplit : q.parts.filter (· = 1) + q.parts.filter (· ≠ 1) = q.parts := by
      simpa using Multiset.filter_add_not (· = 1) q.parts
    have hcard_eq : q.parts.count 1 + Multiset.card (q.parts.filter (· ≠ 1)) =
        Multiset.card q.parts := by
      have hc := congrArg Multiset.card hsplit
      rw [Multiset.card_add, Multiset.filter_eq', Multiset.card_replicate] at hc
      exact hc
    have hcount_one : q.parts.count 1 = 2 * Multiset.card (q.parts.filter (· ≠ 1)) := by
      omega
    refine ⟨
      { parts := (q.parts.filter (· ≠ 1)).map (· + 2)
        parts_pos := by
          intro i hi
          rw [Multiset.mem_map] at hi
          rcases hi with ⟨j, _, rfl⟩
          omega
        parts_sum := by
          rw [multiset_sum_add_two, ← hcount_one]
          have hs := congrArg Multiset.sum hsplit
          rw [Multiset.sum_add, Multiset.filter_eq', Multiset.sum_replicate,
            smul_eq_mul, mul_one, q.parts_sum] at hs
          omega },
      ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro i hi
      rw [Multiset.mem_map] at hi
      rcases hi with ⟨j, hj, rfl⟩
      rw [Multiset.mem_filter] at hj
      have hjpos : 0 < j := q.parts_pos hj.1
      have hjne : j ≠ 1 := hj.2
      omega
    · apply Nat.Partition.ext
      simp only [Multiset.map_map, Multiset.card_map, ← hcount_one]
      have hid : ((q.parts.filter (· ≠ 1)).map ((· - 2) ∘ (· + 2))) = q.parts.filter (· ≠ 1) := by
        conv_rhs => rw [← Multiset.map_id' (q.parts.filter (· ≠ 1))]
        apply Multiset.map_congr rfl
        intro j _
        simp
      rw [hid, ← Multiset.filter_eq', add_comm]
      exact hsplit
