import OMAStatements.S_mo_453358

open OMA.S_mo_453358 Set Metric

private theorem half_cover_of_packing {X : Type} [MetricSpace X] {N : ℕ}
    (h : doublingByPacking X N) : coversByHalfBalls X N := by
  classical
  intro x r hr
  let valid (C : Finset X) : Prop :=
    (C : Set X) ⊆ ball x r ∧ distSeparated (r / 2) (C : Set X)
  let sizes (l : ℕ) : Prop := ∃ C : Finset X, C.card = l ∧ valid C
  have h0 : sizes 0 := ⟨∅, rfl, by simp [valid, distSeparated]⟩
  have bound {C : Finset X} (hc : valid C) : C.card ≤ N := by
    have hb := h.2 x r hr (C : Set X) hc.1 hc.2
    simpa [Set.encard_coe_eq_coe_finsetCard] using hb
  obtain ⟨C, hC, hc⟩ := Nat.findGreatest_spec (Nat.zero_le N) h0
  refine ⟨C, bound hc, ?_⟩
  intro y hy
  by_contra hmiss
  have hfar (c : X) (hcc : c ∈ C) : r / 2 ≤ dist y c := by
    by_contra! hclose
    exact hmiss (Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hcc, hclose⟩⟩)
  have hyC : y ∉ C := by
    intro hyC
    have hw := hfar y hyC
    rw [dist_self] at hw
    linarith
  have hnew : valid (insert y C) := by
    constructor
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hy
      · exact hc.1 hz
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hay | haC
      · subst a
        rcases Finset.mem_insert.mp hb with hby | hbC
        · exact (hab hby.symm).elim
        · exact hfar b hbC
      · rcases Finset.mem_insert.mp hb with hby | hbC
        · subst b
          rw [dist_comm]
          exact hfar a haC
        · exact hc.2 haC hbC hab
  have hmax : (insert y C).card ≤ Nat.findGreatest sizes N :=
    Nat.le_findGreatest (bound hnew) ⟨insert y C, rfl, hnew⟩
  rw [Finset.card_insert_of_notMem hyC, ← hC] at hmax
  omega

private theorem iterated_cover {X : Type} [MetricSpace X] {M : ℕ}
    (h : coversByHalfBalls X M) (k : ℕ) (x : X) (r : ℝ) (hr : 0 < r) :
    ∃ C : Finset X, C.card ≤ M ^ k ∧
      ∀ y ∈ ball x r, ∃ c ∈ C, y ∈ ball c (r / (2 : ℝ) ^ k) := by
  classical
  induction k generalizing x r with
  | zero =>
    exact ⟨{x}, by simp, fun y hy => ⟨x, by simp, by simpa using hy⟩⟩
  | succ k ih =>
    obtain ⟨C, hC, hcov⟩ := h x r hr
    choose D hD hd using fun c => ih c (r / 2) (by positivity)
    refine ⟨C.biUnion D, ?_, ?_⟩
    · calc
        _ ≤ C.card * M ^ k := Finset.card_biUnion_le_card_mul _ _ _ fun c _ => hD c
        _ ≤ M ^ (k + 1) := by rw [pow_succ']; exact Nat.mul_le_mul_right _ hC
    · intro y hy
      have hyCover := hcov hy
      simp only [Set.mem_iUnion] at hyCover
      obtain ⟨c, hc, hyc⟩ := hyCover
      obtain ⟨d, hdC, hyd⟩ := hd c y hyc
      exact ⟨d, Finset.mem_biUnion.mpr ⟨c, hc, hdC⟩, by simpa [pow_succ', div_div] using hyd⟩

theorem OMA.solution : type_of% @OMA.S_mo_453358.main := by
  classical
  intro X _
  constructor
  · intro M hM h
    refine ⟨Nat.pow_pos (by omega), ?_⟩
    intro x r hr S hS hsep
    obtain ⟨C, hC, hc⟩ := iterated_cover h 2 x r hr
    have he (y : S) : ∃ c ∈ C, (y : X) ∈ ball c (r / 4) := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hc y (hS y.property)
    choose f hfC hfBall using he
    let F : X → X := fun y => if hy : y ∈ S then f ⟨y, hy⟩ else x
    have hfMaps : Set.MapsTo F S (C : Set X) := by
      intro y hy
      simpa [F, hy] using hfC ⟨y, hy⟩
    have hfInj : Set.InjOn F S := by
      intro y hy z hz heq
      by_contra hne
      have hcent : f ⟨y, hy⟩ = f ⟨z, hz⟩ := by simpa [F, hy, hz] using heq
      have hy' : dist y (f ⟨y, hy⟩) < r / 4 := hfBall ⟨y, hy⟩
      have hz' : dist z (f ⟨y, hy⟩) < r / 4 := hcent.symm ▸ hfBall ⟨z, hz⟩
      have ht := dist_triangle_right y z (f ⟨y, hy⟩)
      linarith [hsep hy hz hne]
    apply (Set.encard_le_encard_of_injOn hfMaps hfInj).trans
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hC
  · intro N hN k hk x r hr S hS hsep
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    obtain ⟨C, hC, hcov⟩ := iterated_cover (half_cover_of_packing hN) l x r hr
    let T (c : X) := S ∩ ball c (r / (2 : ℝ) ^ l)
    have bound (c : X) : (T c).encard ≤ N := by
      apply hN.2 c _ (by positivity) (T c) Set.inter_subset_right
      intro u hu v hv huv
      simpa [pow_succ, div_div] using hsep hu.1 hv.1 huv
    have hfin (c : X) : (T c).Finite := (Set.encard_le_coe_iff.mp (bound c)).1
    let D (c : X) := (hfin c).toFinset
    have hD (c : X) : (D c : Set X) = T c := (hfin c).coe_toFinset
    have hDc (c : X) : (D c).card ≤ N := by
      have hb := bound c
      rw [← hD c, Set.encard_coe_eq_coe_finsetCard] at hb
      exact_mod_cast hb
    have hT : S ⊆ (C.biUnion D : Set X) := by
      intro y hy
      obtain ⟨c, hc, hyc⟩ := hcov y (hS hy)
      exact Finset.mem_biUnion.mpr ⟨c, hc, by
        change y ∈ (D c : Set X)
        rw [hD]
        exact ⟨hy, hyc⟩⟩
    have hcc : (C.biUnion D).card ≤ N ^ (l + 1) := by
      calc
        _ ≤ C.card * N := Finset.card_biUnion_le_card_mul _ _ _ fun c _ => hDc c
        _ ≤ N ^ (l + 1) := by rw [pow_succ]; exact Nat.mul_le_mul_right _ hC
    apply (Set.encard_le_encard hT).trans
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hcc