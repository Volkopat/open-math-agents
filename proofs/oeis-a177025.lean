import OMAStatements.S_oeis_a177025

theorem OMA.solution : type_of% @OMA.S_oeis_a177025.main := by
  have hinv : ∀ d : ℕ, 0 < d → ((1 : PowerSeries ℚ) - PowerSeries.X ^ d)⁻¹ =
      PowerSeries.mk (fun i => if d ∣ i then (1 : ℚ) else 0) := by
    intro d hd
    rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp [hd.ne'])]
    ext i
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, PowerSeries.coeff_one]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [Nat.not_le.mpr hd]
    · by_cases h : d ∣ i
      · have h1 : d ≤ i := Nat.le_of_dvd hi h
        have h2 : d ∣ i - d := Nat.dvd_sub h dvd_rfl
        simp [h, h1, h2, hi.ne']
      · have h2 : ¬ (d ≤ i ∧ d ∣ i - d) := by
          rintro ⟨h1, h2⟩
          apply h
          have := Nat.dvd_add h2 (dvd_refl d)
          rwa [Nat.sub_add_cancel h1] at this
        by_cases h1 : d ≤ i
        · simp [h, h1, hi.ne', show ¬ d ∣ i - d from fun h3 => h2 ⟨h1, h3⟩]
        · simp [h, h1, hi.ne']
  have hT : ∀ m : ℕ, 2 ≤ m → 1 ≤ m * (m - 1) / 2 := by
    intro m hm
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : 1 ≤ m - 1 := by omega
    nlinarith
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_atTop_of_eventually_const (i₀ := n + 1)
  intro N hN
  have hterm : ∀ k ∈ Finset.Ico 2 N,
      PowerSeries.coeff n (PowerSeries.X *
        (PowerSeries.X ^ k * (1 - PowerSeries.X ^ (k * (k + 1) / 2))⁻¹ : PowerSeries ℚ)) =
      if k + 1 ≤ n ∧ k * (k + 1) / 2 ∣ n - (k + 1) then (1 : ℚ) else 0 := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hpos : 0 < k * (k + 1) / 2 := by
      have := hT (k + 1) (by omega)
      rw [Nat.add_sub_cancel, mul_comm] at this
      omega
    rw [← mul_assoc, ← pow_succ', hinv _ hpos, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_mk]
    by_cases h : k + 1 ≤ n <;> simp [h]
  rw [Finset.mul_sum, map_sum, Finset.sum_congr rfl hterm, Finset.sum_boole, PowerSeries.coeff_mk]
  split_ifs with h3
  · norm_cast
    have hB : (Finset.Ico 2 N).filter (fun k => k + 1 ≤ n ∧ k * (k + 1) / 2 ∣ n - (k + 1)) =
        (Finset.Ico 2 n).filter (fun k => k * (k + 1) / 2 ∣ n - (k + 1)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨h1, _⟩, h3, h4⟩
        exact ⟨⟨h1, by omega⟩, h4⟩
      · rintro ⟨⟨h1, h2⟩, h4⟩
        exact ⟨⟨h1, by omega⟩, by omega, h4⟩
    have hA : OMA.S_oeis_a177025.a n =
        ((Finset.Ico 1 (n - 1)).filter (fun k => k * (k + 1) / 2 ∣ n - (k + 1))).card := by
      rw [OMA.S_oeis_a177025.a]
      refine Finset.card_bij (fun p _ => p.2 - 1) ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
          OMA.S_oeis_a177025.polygonal] at hp
        obtain ⟨s, m⟩ := p
        obtain ⟨⟨⟨hs1, hs2⟩, hm1, hm2⟩, hP⟩ := hp
        have hm : 2 ≤ m := by
          by_contra hm
          have : m = 1 := by omega
          subst this
          simp at hP
          omega
        have ht := hT m hm
        obtain ⟨u, hu⟩ : ∃ u, u = (s - 2) * (m * (m - 1) / 2) := ⟨_, rfl⟩
        have hu1 : 1 ≤ u := by rw [hu]; nlinarith [show 1 ≤ s - 2 by omega]
        rw [← hu] at hP
        simp only [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [show m - 1 + 1 = m by omega, mul_comm (m - 1) m, show n - m = u by omega, hu]
        exact Dvd.intro_left _ rfl
      · intro p1 hp1 p2 hp2 h
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
          OMA.S_oeis_a177025.polygonal] at hp1 hp2
        obtain ⟨s1, m1⟩ := p1
        obtain ⟨s2, m2⟩ := p2
        simp only at hp1 hp2 h
        have hm : ∀ s m, 1 ≤ m → m + (s - 2) * (m * (m - 1) / 2) = n → 2 ≤ m := by
          intro s m hm1 hP
          by_contra hm
          have : m = 1 := by omega
          subst this
          simp at hP
          omega
        have h1 := hm s1 m1 hp1.1.2.1 hp1.2
        have h2 := hm s2 m2 hp2.1.2.1 hp2.2
        have hmm : m1 = m2 := by omega
        subst hmm
        have ht := hT m1 h1
        have := hp1.2.trans hp2.2.symm
        have h' : (s1 - 2) * (m1 * (m1 - 1) / 2) = (s2 - 2) * (m1 * (m1 - 1) / 2) := by omega
        have := Nat.eq_of_mul_eq_mul_right (by omega) h'
        exact Prod.ext (by simp only; omega) rfl
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_Ico] at hk
        obtain ⟨⟨hk1, hk2⟩, c, hc⟩ := hk
        have hT' : 1 ≤ k * (k + 1) / 2 := by
          have := hT (k + 1) (by omega)
          rwa [Nat.add_sub_cancel, mul_comm] at this
        have hc1 : 1 ≤ c := by
          rcases Nat.eq_zero_or_pos c with rfl | h
          · simp at hc; omega
          · exact h
        have hcle : c ≤ k * (k + 1) / 2 * c := Nat.le_mul_of_pos_left c hT'
        refine ⟨(c + 2, k + 1), ?_, by simp⟩
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
          OMA.S_oeis_a177025.polygonal]
        refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, ?_⟩
        rw [Nat.add_sub_cancel, Nat.add_sub_cancel, mul_comm (k + 1) k, mul_comm c, ← hc]
        omega
    have e1 : Finset.Ico 1 (n - 1) = insert 1 (Finset.Ico 2 (n - 1)) := by
      ext k; simp only [Finset.mem_insert, Finset.mem_Ico]; omega
    have e2 : Finset.Ico 2 n = insert (n - 1) (Finset.Ico 2 (n - 1)) := by
      ext k; simp only [Finset.mem_insert, Finset.mem_Ico]; omega
    rw [hB, hA, e1, e2, Finset.filter_insert, Finset.filter_insert,
      if_pos (by rw [show n - (n - 1 + 1) = 0 by omega]; exact dvd_zero _), if_pos (by norm_num),
      Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp)]
  · norm_cast
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k hk h
    simp only [Finset.mem_Ico] at hk
    omega
