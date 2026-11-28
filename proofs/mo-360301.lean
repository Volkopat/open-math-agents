import OMAStatements.S_mo_360301

open Set Metric

private lemma family_Ioo_0_3 : OMA.S_mo_360301.Family (Ioo (0 : ℝ) 3) := by
  refine ⟨⟨1, by norm_num⟩, isBounded_Ioo 0 3, isOpen_Ioo, ?_, 0, 3, 0, 3, by simp⟩
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 3), interior_Icc]

private lemma closure_gap (r t : ℝ) (hr : 0 < r) (ht1 : 2 * r ≤ t) (ht2 : t ≤ 3 - 2 * r) :
    closure (Ioo 0 (t - r) ∪ Ioo (t + r) 3) = Icc 0 (t - r) ∪ Icc (t + r) 3 := by
  rw [closure_union, closure_Ioo (by linarith), closure_Ioo (by linarith)]

private lemma family_gap (r t : ℝ) (hr : 0 < r) (ht1 : 2 * r ≤ t) (ht2 : t ≤ 3 - 2 * r) :
    OMA.S_mo_360301.Family (Ioo 0 (t - r) ∪ Ioo (t + r) 3) := by
  refine ⟨⟨r / 2, Or.inl ⟨by linarith, by linarith⟩⟩, ?_, isOpen_Ioo.union isOpen_Ioo, ?_,
    0, t - r, t + r, 3, rfl⟩
  · exact (isBounded_Ioo 0 (t - r)).union (isBounded_Ioo (t + r) 3)
  · rw [closure_gap r t hr ht1 ht2]
    apply Subset.antisymm
    · intro x hx
      rw [mem_interior] at hx
      rcases hx with ⟨U, hUsub, hUopen, hxU⟩
      rcases hUsub hxU with hxL | hxR
      · left
        have hxlt : x < t + r := by linarith [hxL.2]
        have hsub : U ∩ Iio (t + r) ⊆ Icc 0 (t - r) := by
          intro y hy
          rcases hUsub hy.1 with hyL | hyR
          · exact hyL
          · exfalso; linarith [mem_Iio.mp hy.2, hyR.1]
        have hmem : x ∈ interior (Icc 0 (t - r)) :=
          mem_interior.mpr ⟨U ∩ Iio (t + r), hsub, hUopen.inter isOpen_Iio, ⟨hxU, hxlt⟩⟩
        rwa [interior_Icc] at hmem
      · right
        have hxgt : t - r < x := by linarith [hxR.1]
        have hsub : U ∩ Ioi (t - r) ⊆ Icc (t + r) 3 := by
          intro y hy
          rcases hUsub hy.1 with hyL | hyR
          · exfalso; linarith [mem_Ioi.mp hy.2, hyL.2]
          · exact hyR
        have hmem : x ∈ interior (Icc (t + r) 3) :=
          mem_interior.mpr ⟨U ∩ Ioi (t - r), hsub, hUopen.inter isOpen_Ioi, ⟨hxU, hxgt⟩⟩
        rwa [interior_Icc] at hmem
    · exact (isOpen_Ioo.union isOpen_Ioo).subset_interior_iff.mpr
        (union_subset_union Ioo_subset_Icc_self Ioo_subset_Icc_self)

private lemma hausdorffDist_Ioo_gap (r t : ℝ) (hr : 0 < r) (ht1 : 2 * r ≤ t)
    (ht2 : t ≤ 3 - 2 * r) :
    hausdorffDist (closure (Ioo (0 : ℝ) 3)) (closure (Ioo 0 (t - r) ∪ Ioo (t + r) 3)) ≤ r := by
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 3), closure_gap r t hr ht1 ht2]
  refine hausdorffDist_le_of_mem_dist hr.le ?_ ?_
  · intro x hx
    by_cases hx1 : x ≤ t - r
    · exact ⟨x, Or.inl ⟨hx.1, hx1⟩, by simp; exact hr.le⟩
    · by_cases hx2 : t + r ≤ x
      · exact ⟨x, Or.inr ⟨hx2, hx.2⟩, by simp; exact hr.le⟩
      · by_cases hx3 : x ≤ t
        · refine ⟨t - r, Or.inl ⟨by linarith, le_rfl⟩, ?_⟩
          rw [Real.dist_eq, abs_le]
          constructor <;> linarith
        · refine ⟨t + r, Or.inr ⟨le_rfl, by linarith⟩, ?_⟩
          rw [Real.dist_eq, abs_le]
          constructor <;> linarith
  · intro x hx
    rcases hx with hxL | hxR
    · exact ⟨x, ⟨hxL.1, by linarith [hxL.2]⟩, by simp; exact hr.le⟩
    · exact ⟨x, ⟨by linarith [hxR.1], hxR.2⟩, by simp; exact hr.le⟩

private lemma gap_mem_dist (r s1 s2 : ℝ) (hr : 0 < r) (hs2a : 2 * r ≤ s2) (hs2b : s2 ≤ 3 - 2 * r) :
    ∀ x ∈ Icc 0 (s1 - r) ∪ Icc (s1 + r) 3,
      ∃ y ∈ Icc 0 (s2 - r) ∪ Icc (s2 + r) 3, dist x y ≤ |s1 - s2| := by
  intro x hx
  rcases hx with hxL | hxR
  · by_cases hxs : x ≤ s2 - r
    · exact ⟨x, Or.inl ⟨hxL.1, hxs⟩, by simp⟩
    · refine ⟨s2 - r, Or.inl ⟨by linarith, le_rfl⟩, ?_⟩
      rw [Real.dist_eq, abs_le]
      have h2 : -(s1 - s2) ≤ |s1 - s2| := neg_le_abs _
      have h3 : s1 - s2 ≤ |s1 - s2| := le_abs_self _
      constructor <;> linarith [hxL.2]
  · by_cases hxs : s2 + r ≤ x
    · exact ⟨x, Or.inr ⟨hxs, hxR.2⟩, by simp⟩
    · refine ⟨s2 + r, Or.inr ⟨le_rfl, by linarith⟩, ?_⟩
      rw [Real.dist_eq, abs_le]
      have h4 : s2 - s1 ≤ |s1 - s2| := by rw [abs_sub_comm]; exact le_abs_self _
      constructor <;> linarith [hxR.1, abs_nonneg (s1 - s2)]

private lemma hausdorffDist_gap_gap (r t t' : ℝ) (hr : 0 < r) (ht1 : 2 * r ≤ t)
    (ht2 : t ≤ 3 - 2 * r) (ht1' : 2 * r ≤ t') (ht2' : t' ≤ 3 - 2 * r) :
    hausdorffDist (closure (Ioo 0 (t - r) ∪ Ioo (t + r) 3))
      (closure (Ioo 0 (t' - r) ∪ Ioo (t' + r) 3)) ≤ |t - t'| := by
  rw [closure_gap r t hr ht1 ht2, closure_gap r t' hr ht1' ht2']
  refine hausdorffDist_le_of_mem_dist (abs_nonneg _)
    (gap_mem_dist r t t' hr ht1' ht2') ?_
  simpa only [abs_sub_comm t' t] using gap_mem_dist r t' t hr ht1 ht2

theorem OMA.solution : type_of% @OMA.S_mo_360301.main := by
  intro s hs
  have h1 : ∃ G, OMA.S_mo_360301.Family G ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ H, OMA.S_mo_360301.Family H ∧ hausdorffDist (closure G) (closure H) < δ ∧
        ε ≤ dist (s G) (s H) := by
    by_contra hcont
    push Not at hcont
    have hcont' : ∀ G, OMA.S_mo_360301.Family G → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ H, OMA.S_mo_360301.Family H →
          hausdorffDist (closure G) (closure H) < δ → dist (s G) (s H) < ε := by
      intro G hG ε hε
      exact hcont G hG ε hε
    let G0 : Set ℝ := Ioo 0 3
    have hG0 : OMA.S_mo_360301.Family G0 := family_Ioo_0_3
    have hp : s G0 ∈ G0 := hs G0 hG0
    set p : ℝ := s G0
    have hp0 : 0 < p := hp.1
    have hp3 : p < 3 := hp.2
    let ε0 : ℝ := min p (3 - p) / 2
    have hε0 : 0 < ε0 := by positivity
    have hε0_p : 2 * ε0 ≤ p := by dsimp [ε0]; linarith [min_le_left p (3 - p)]
    have hε0_3p : 2 * ε0 ≤ 3 - p := by dsimp [ε0]; linarith [min_le_right p (3 - p)]
    rcases hcont' G0 hG0 ε0 hε0 with ⟨δ0, hδ0, hδ0_prop⟩
    let r : ℝ := min δ0 ε0 / 5
    have hr : 0 < r := by positivity
    have hr_δ0 : r < δ0 := by
      have : r ≤ δ0 / 5 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      linarith
    have hr_ε0 : 5 * r ≤ ε0 := by
      have : r ≤ ε0 / 5 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      linarith
    have hab : 2 * r ≤ 3 - 2 * r := by linarith
    let H : ℝ → Set ℝ := fun t => Ioo 0 (t - r) ∪ Ioo (t + r) 3
    let g : ℝ → ℝ := fun t => s (H t) - t
    have hg_cont : ContinuousOn g (Icc (2 * r) (3 - 2 * r)) := by
      refine ContinuousOn.sub ?_ continuousOn_id
      rw [Metric.continuousOn_iff]
      intro t ht ε hε
      have hHt : OMA.S_mo_360301.Family (H t) := family_gap r t hr ht.1 ht.2
      rcases hcont' (H t) hHt ε hε with ⟨δ, hδ, hδ_prop⟩
      refine ⟨δ, hδ, fun t' ht' htt' => ?_⟩
      have hHt' : OMA.S_mo_360301.Family (H t') := family_gap r t' hr ht'.1 ht'.2
      have hhd : hausdorffDist (closure (H t)) (closure (H t')) < δ := by
        calc hausdorffDist (closure (H t)) (closure (H t'))
            ≤ |t - t'| := hausdorffDist_gap_gap r t t' hr ht.1 ht.2 ht'.1 ht'.2
          _ = dist t' t := by rw [Real.dist_eq, abs_sub_comm]
          _ < δ := htt'
      rw [dist_comm]
      exact hδ_prop (H t') hHt' hhd
    have h_near : ∀ t ∈ Icc (2 * r) (3 - 2 * r), dist (s (H t)) p < ε0 := by
      intro t ht
      have hHt : OMA.S_mo_360301.Family (H t) := family_gap r t hr ht.1 ht.2
      have hhd : hausdorffDist (closure G0) (closure (H t)) < δ0 :=
        lt_of_le_of_lt (hausdorffDist_Ioo_gap r t hr ht.1 ht.2) hr_δ0
      rw [dist_comm]
      exact hδ0_prop (H t) hHt hhd
    have hg_left : 0 < g (2 * r) := by
      have hdist := h_near (2 * r) (left_mem_Icc.mpr hab)
      rw [Real.dist_eq, abs_lt] at hdist
      have : 2 * r < s (H (2 * r)) := by linarith
      dsimp [g]; linarith
    have hg_right : g (3 - 2 * r) < 0 := by
      have hdist := h_near (3 - 2 * r) (right_mem_Icc.mpr hab)
      rw [Real.dist_eq, abs_lt] at hdist
      have : s (H (3 - 2 * r)) < 3 - 2 * r := by linarith
      dsimp [g]; linarith
    have h0_mem : (0 : ℝ) ∈ Icc (g (3 - 2 * r)) (g (2 * r)) := ⟨hg_right.le, hg_left.le⟩
    rcases intermediate_value_Icc' hab hg_cont h0_mem with ⟨t, ht, hgt⟩
    have hst : s (H t) = t := by
      dsimp [g] at hgt
      linarith
    have hmem : s (H t) ∈ H t := hs (H t) (family_gap r t hr ht.1 ht.2)
    rw [hst] at hmem
    rcases hmem with ⟨_, hlt⟩ | ⟨hgt', _⟩ <;> linarith
  refine ⟨h1, ?_⟩
  intro C hC
  rcases h1 with ⟨G, hG, ε, hε, hδ⟩
  rcases hδ (ε / (C + 1)) (by positivity) with ⟨H, hH, hdist, hsep⟩
  refine ⟨G, H, hG, hH, ?_⟩
  have h1' : C * hausdorffDist (closure G) (closure H) ≤ C * (ε / (C + 1)) :=
    mul_le_mul_of_nonneg_left hdist.le hC
  have h2' : C * (ε / (C + 1)) < ε := by
    have hden : (0 : ℝ) < C + 1 := by linarith
    rw [mul_div_assoc', div_lt_iff₀ hden]
    nlinarith
  linarith
