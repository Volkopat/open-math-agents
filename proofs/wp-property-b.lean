import OMAStatements.S_wp_property_b

open OMA.S_wp_property_b

private theorem obstruction (n : ℕ) : (noPropertyBSizes n).Nonempty := by
  classical
  let U : Finset (Fin (2 * n)) := Finset.univ
  let C : Finset (Set (Fin (2 * n))) :=
    Finset.image (fun A : Finset (Fin (2 * n)) => (A : Set (Fin (2 * n)))) (U.powersetCard n)
  refine ⟨C.card, 2 * n, C, rfl, ?_, ?_⟩
  · intro S hS
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hS
    rw [Set.ncard_coe_finset]
    exact (Finset.mem_powersetCard.mp hA).2
  · rintro ⟨Y, Z, hdisj, hcover, hC⟩
    let Y' := U.filter (· ∈ Y)
    let Z' := U.filter (· ∈ Z)
    have hYZ : Disjoint Y' Z' := Finset.disjoint_left.mpr fun x hxY hxZ =>
      Set.disjoint_left.mp hdisj (Finset.mem_filter.mp hxY).2 (Finset.mem_filter.mp hxZ).2
    have hu : Y' ∪ Z' = U := by
      ext x
      have hx : x ∈ Y ∨ x ∈ Z := by
        change x ∈ Y ∪ Z
        rw [hcover]
        exact Set.mem_univ x
      simp [Y', Z', U, hx]
    have hsum : Y'.card + Z'.card = 2 * n := by
      rw [← Finset.card_union_of_disjoint hYZ, hu]
      simp [U]
    have edge (A : Finset (Fin (2 * n))) (hA : A.card = n) :
        (A : Set (Fin (2 * n))) ∈ C :=
      Finset.mem_image.mpr
        ⟨A, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA⟩, rfl⟩
    by_cases hY : n ≤ Y'.card
    · obtain ⟨A, hAY, hA⟩ := Finset.exists_subset_card_eq hY
      obtain ⟨x, hxA, hxZ⟩ := (hC _ (edge A hA)).2
      exact Set.disjoint_left.mp hdisj (Finset.mem_filter.mp (hAY hxA)).2 hxZ
    · have hZ : n ≤ Z'.card := by omega
      obtain ⟨A, hAZ, hA⟩ := Finset.exists_subset_card_eq hZ
      obtain ⟨x, hxA, hxY⟩ := (hC _ (edge A hA)).1
      exact Set.disjoint_left.mp hdisj hxY (Finset.mem_filter.mp (hAZ hxA)).2

theorem OMA.solution : type_of% @OMA.S_wp_property_b.main := by
  intro n
  have hmin : m n ∈ noPropertyBSizes n := Nat.sInf_mem (obstruction n)
  refine ⟨hmin, ?_⟩
  intro k hk N C hCn hcard
  by_contra hC
  have hmem : k ∈ noPropertyBSizes n := ⟨N, C, hcard, hCn, hC⟩
  exact (not_lt_of_ge (Nat.sInf_le hmem)) hk