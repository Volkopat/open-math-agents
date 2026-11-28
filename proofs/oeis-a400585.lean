import OMAStatements.S_oeis_a400585

open scoped BigOperators Topology

namespace OMA.S_oeis_a400585_proof

open OMA.S_oeis_a400585

private lemma sum_choose_two (M : ℕ) :
    ∑ m ∈ Finset.range (M + 1), m.choose 2 = (M + 1).choose 3 := by
  induction M with
  | zero => simp [Nat.choose_eq_zero_of_lt]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, add_comm, ← Nat.choose_succ_succ (M + 1) 2]

private lemma two_mul_choose_two (M : ℕ) : 2 * (M + 1).choose 2 = (M + 1) * M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.choose_succ_succ, mul_add, ih, Nat.choose_one_right]
    ring

private lemma six_mul_choose_three (M : ℕ) :
    6 * (M + 1).choose 3 = M * (M + 1) * (M - 1) := by
  induction M with
  | zero => simp [Nat.choose_eq_zero_of_lt]
  | succ M ih =>
    rw [Nat.choose_succ_succ, mul_add]
    have h2 : 6 * (M + 1).choose 2 = 3 * (2 * (M + 1).choose 2) := by ring
    rw [h2, two_mul_choose_two, ih]
    cases M with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      ring

private lemma choose_three_real (M : ℕ) :
    (((M + 1).choose 3 : ℕ) : ℝ) = (M : ℝ) * ((M : ℝ) + 1) * ((M : ℝ) - 1) / 6 := by
  have h6 : (6 : ℝ) * (((M + 1).choose 3 : ℕ) : ℝ) = (M : ℝ) * ((M : ℝ) + 1) * ((M : ℝ) - 1) := by
    cases M with
    | zero => simp [Nat.choose_eq_zero_of_lt]
    | succ k =>
      have hnat : 6 * (k + 2).choose 3 = (k + 1) * (k + 2) * k := by
        simpa only [Nat.add_sub_cancel] using six_mul_choose_three (k + 1)
      have h := congrArg (Nat.cast : ℕ → ℝ) hnat
      push_cast at h ⊢
      rw [h]
      ring
  linarith

private lemma choose_three_le_real (M : ℕ) :
    (((M + 1).choose 3 : ℕ) : ℝ) ≤ (M : ℝ) ^ 3 / 6 := by
  rw [choose_three_real]
  have hle : (M : ℝ) * ((M : ℝ) + 1) * ((M : ℝ) - 1) ≤ (M : ℝ) ^ 3 := by
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith [sq_nonneg (M : ℝ)]
  linarith

private lemma sum_a_eq (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), a k =
      ∑ j ∈ Finset.Icc 1 n, if Odd j then (n / j + 1).choose 3 else 0 := by
  let F : ℕ → ℕ → ℕ := fun k j => if Odd j ∧ j ∣ k then (k / j).choose 2 else 0
  have hinner : ∀ k ∈ Finset.range (n + 1), a k = ∑ j ∈ Finset.Icc 1 n, F k j := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rcases eq_or_ne k 0 with rfl | hk0
    · simp [a, F]
    · rw [a]
      have hsub : k.divisors ⊆ Finset.Icc 1 n := by
        intro j hj
        rw [Nat.mem_divisors] at hj
        rw [Finset.mem_Icc]
        exact ⟨Nat.pos_of_ne_zero (fun h0 => hk0 (by simpa [h0] using hj.1)),
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hj.1).trans hkn⟩
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl fun j hj => ?_
        have hjk : j ∣ k := (Nat.mem_divisors.mp hj).1
        by_cases hodd : Odd j
        · simp [F, hodd, hjk]
        · simp [F, hodd]
      · intro j _ hjn
        have hndvd : ¬ j ∣ k := fun hd => hjn (Nat.mem_divisors.mpr ⟨hd, hk0⟩)
        simp [F, hndvd]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  by_cases hodd : Odd j
  · simp only [F, hodd, true_and, ↓reduceIte]
    rw [← sum_choose_two]
    have hflt : ∑ k ∈ Finset.range (n + 1), (if j ∣ k then (k / j).choose 2 else 0) =
        ∑ k ∈ (Finset.range (n + 1)).filter (j ∣ ·), (k / j).choose 2 := by
      rw [Finset.sum_filter]
    rw [hflt]
    symm
    refine Finset.sum_bij (fun m _ => j * m) ?_ ?_ ?_ ?_
    · intro m hm
      have hmle : m ≤ n / j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le ?_, dvd_mul_right j m⟩
      exact (Nat.mul_le_mul_left j hmle).trans (Nat.mul_div_le n j)
    · intro m₁ _ m₂ _ h
      exact Nat.mul_left_cancel hj1 h
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rcases hk.2 with ⟨m, rfl⟩
      refine ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le ?_), rfl⟩
      exact (Nat.le_div_iff_mul_le hj1).mpr (by rw [mul_comm]; exact Nat.lt_succ_iff.mp hk.1)
    · intro m _
      rw [Nat.mul_div_right m hj1]
  · simp only [F, hodd, false_and, ↓reduceIte, Finset.sum_const_zero]

private noncomputable def term (n j : ℕ) : ℝ :=
  if Odd j then (((n / j + 1).choose 3 : ℕ) : ℝ) / (n : ℝ) ^ 3 else 0

private lemma ratio_eq_tsum_term (n : ℕ) (_hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n + 1), (a k : ℝ)) / (n : ℝ) ^ 3 = ∑' j : ℕ, term n j := by
  have ha_real : (∑ k ∈ Finset.range (n + 1), (a k : ℝ)) =
      ∑ j ∈ Finset.Icc 1 n, if Odd j then (((n / j + 1).choose 3 : ℕ) : ℝ) else 0 := by
    have h := congrArg (Nat.cast : ℕ → ℝ) (sum_a_eq n)
    push_cast at h
    exact h
  rw [ha_real, Finset.sum_div]
  have hterm_eq :
      (∑ j ∈ Finset.Icc 1 n, (if Odd j then (((n / j + 1).choose 3 : ℕ) : ℝ) else 0) / (n : ℝ) ^ 3) =
        ∑ j ∈ Finset.Icc 1 n, term n j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hodd : Odd j <;> simp [term, hodd]
  rw [hterm_eq]
  symm
  refine tsum_eq_sum fun j hj => ?_
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
  rcases hj with hj0 | hjn
  · have hjz : j = 0 := Nat.lt_one_iff.mp hj0
    subst hjz
    simp [term]
  · have hdiv0 : n / j = 0 := Nat.div_eq_of_lt hjn
    simp [term, hdiv0, Nat.choose_eq_zero_of_lt]

private lemma term_norm_le (n j : ℕ) (hn : 1 ≤ n) :
    ‖term n j‖ ≤ (1 / 6 : ℝ) * ((j : ℝ) ^ 3)⁻¹ := by
  by_cases hodd : Odd j
  · have hj0 : j ≠ 0 := by
      rintro rfl
      exact Nat.not_odd_zero hodd
    have hj_pos : (0 : ℝ) < j := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj0)
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have ht_nn : 0 ≤ term n j := by
      simp only [term, hodd, ↓reduceIte]
      positivity
    rw [Real.norm_of_nonneg ht_nn]
    simp only [term, hodd, ↓reduceIte]
    have hdiv_le : ((n / j : ℕ) : ℝ) ≤ (n : ℝ) / (j : ℝ) := by
      rw [le_div_iff₀ hj_pos]
      have hnat : (n / j) * j ≤ n := Nat.div_mul_le_self n j
      exact_mod_cast hnat
    have hpow_le : ((n / j : ℕ) : ℝ) ^ 3 ≤ ((n : ℝ) / (j : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv_le 3
    have hc3 := choose_three_le_real (n / j)
    calc
      (((n / j + 1).choose 3 : ℕ) : ℝ) / (n : ℝ) ^ 3
        ≤ (((n / j : ℕ) : ℝ) ^ 3 / 6) / (n : ℝ) ^ 3 :=
          div_le_div_of_nonneg_right hc3 (by positivity)
      _ ≤ (((n : ℝ) / (j : ℝ)) ^ 3 / 6) / (n : ℝ) ^ 3 :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hpow_le (by positivity))
            (by positivity)
      _ = (1 / 6 : ℝ) * ((j : ℝ) ^ 3)⁻¹ := by
          have hn3 : (n : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hn_pos.ne'
          field_simp [hn3]
  · simp only [term, hodd, ↓reduceIte, norm_zero]
    positivity

private lemma term_tendsto (j : ℕ) :
    Filter.Tendsto (fun n => term n j) Filter.atTop
      (nhds (if Odd j then (1 / 6 : ℝ) * ((j : ℝ) ^ 3)⁻¹ else 0)) := by
  by_cases hodd : Odd j
  · simp only [hodd, ↓reduceIte]
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact Nat.not_odd_zero hodd
    have hj_pos : (0 : ℝ) < j := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj0)
    have hinv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hr_tend : Filter.Tendsto (fun n : ℕ => ((n / j : ℕ) : ℝ) / (n : ℝ)) Filter.atTop
        (nhds ((j : ℝ)⁻¹)) := by
      have hlow : Filter.Tendsto (fun n : ℕ => (j : ℝ)⁻¹ - (n : ℝ)⁻¹) Filter.atTop
          (nhds ((j : ℝ)⁻¹)) := by
        simpa using tendsto_const_nhds.sub hinv
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
        have hdm : j * (n / j) + n % j = n := Nat.div_add_mod n j
        have hmod : n % j < j := Nat.mod_lt n (Nat.pos_of_ne_zero hj0)
        have hdm_real : (j : ℝ) * ((n / j : ℕ) : ℝ) + ((n % j : ℕ) : ℝ) = (n : ℝ) := by
          exact_mod_cast hdm
        have hmod_real : ((n % j : ℕ) : ℝ) < (j : ℝ) := Nat.cast_lt.mpr hmod
        have hmul : (n : ℝ) < (j : ℝ) * ((n / j : ℕ) : ℝ) + (j : ℝ) := by linarith
        have hdiv := div_lt_div_of_pos_right hmul (mul_pos hn_pos hj_pos)
        have heq1 : (n : ℝ) / ((n : ℝ) * (j : ℝ)) = (j : ℝ)⁻¹ := by
          field_simp [hn_pos.ne', hj_pos.ne']
        have heq2 : ((j : ℝ) * ((n / j : ℕ) : ℝ) + (j : ℝ)) / ((n : ℝ) * (j : ℝ)) =
            ((n / j : ℕ) : ℝ) / (n : ℝ) + (n : ℝ)⁻¹ := by
          field_simp [hn_pos.ne', hj_pos.ne']
        rw [heq1, heq2] at hdiv
        linarith
      · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
        rw [div_le_iff₀ hn_pos]
        have hnat : (n / j) * j ≤ n := Nat.div_mul_le_self n j
        have hreal : ((n / j : ℕ) : ℝ) * (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnat
        calc
          ((n / j : ℕ) : ℝ) = ((n / j : ℕ) : ℝ) * (j : ℝ) * (j : ℝ)⁻¹ := by
            field_simp [hj_pos.ne']
          _ ≤ (n : ℝ) * (j : ℝ)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hreal (by positivity)
          _ = (j : ℝ)⁻¹ * (n : ℝ) := mul_comm _ _
    have hlim : Filter.Tendsto
        (fun n : ℕ => (1 / 6 : ℝ) * (((n / j : ℕ) : ℝ) / (n : ℝ)) *
          ((((n / j : ℕ) : ℝ) / (n : ℝ)) + (n : ℝ)⁻¹) *
          ((((n / j : ℕ) : ℝ) / (n : ℝ)) - (n : ℝ)⁻¹))
        Filter.atTop (nhds ((1 / 6 : ℝ) * ((j : ℝ) ^ 3)⁻¹)) := by
      have hgoal : (1 / 6 : ℝ) * (j : ℝ)⁻¹ * ((j : ℝ)⁻¹ + 0) * ((j : ℝ)⁻¹ - 0) =
          (1 / 6 : ℝ) * ((j : ℝ) ^ 3)⁻¹ := by ring
      rw [← hgoal]
      exact (((tendsto_const_nhds.mul hr_tend).mul (hr_tend.add hinv)).mul (hr_tend.sub hinv))
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    simp only [term, hodd, ↓reduceIte, choose_three_real]
    field_simp [hn_pos.ne']
  · simp only [term, hodd, ↓reduceIte]
    exact tendsto_const_nhds

private lemma tsum_odd_inv_cube :
    (∑' j : ℕ, if Odd j then ((j : ℝ) ^ 3)⁻¹ else 0) = (7 / 8 : ℝ) * zetaThree := by
  let f : ℕ → ℝ := fun j => ((j : ℝ) ^ 3)⁻¹
  let g : ℕ → ℝ := fun j => if Odd j then ((j : ℝ) ^ 3)⁻¹ else 0
  have hf : Summable f := Real.summable_nat_pow_inv.mpr (by norm_num)
  have hfe : Summable (fun k : ℕ => f (2 * k)) :=
    hf.comp_injective fun a b h => by omega
  have hfo : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hf.comp_injective fun a b h => by omega
  have hz : ∀ k : ℕ, g (2 * k) = 0 := fun k => by simp [g]
  have hge : Summable (fun k : ℕ => g (2 * k)) := by
    simp_rw [hz]
    exact summable_zero
  have hgo : Summable (fun k : ℕ => g (2 * k + 1)) := by
    have heq : (fun k : ℕ => g (2 * k + 1)) = fun k : ℕ => f (2 * k + 1) := by
      ext k
      simp [g, f]
    rw [heq]
    exact hfo
  have hg_sum : ∑' j : ℕ, g j = ∑' k : ℕ, f (2 * k + 1) := by
    rw [← tsum_even_add_odd hge hgo]
    have hz1 : ∑' k : ℕ, g (2 * k) = 0 := by simp_rw [hz, tsum_zero]
    have heq : (fun k : ℕ => g (2 * k + 1)) = fun k : ℕ => f (2 * k + 1) := by
      ext k
      simp [g, f]
    rw [hz1, zero_add, heq]
  have hf_sum : ∑' k : ℕ, f (2 * k) + ∑' k : ℕ, f (2 * k + 1) = zetaThree :=
    tsum_even_add_odd hfe hfo
  have heven : ∑' k : ℕ, f (2 * k) = (1 / 8 : ℝ) * zetaThree := by
    have heq : (fun k : ℕ => f (2 * k)) = fun k : ℕ => (1 / 8 : ℝ) * f k := by
      ext k
      simp only [f, Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [heq, tsum_mul_left]
    rfl
  change ∑' j : ℕ, g j = (7 / 8 : ℝ) * zetaThree
  linarith [hg_sum, hf_sum, heven]

end OMA.S_oeis_a400585_proof

open OMA.S_oeis_a400585 OMA.S_oeis_a400585_proof

theorem OMA.solution : type_of% @OMA.S_oeis_a400585.main := by
  have hbound_sum : Summable (fun j : ℕ => (1 / 6 : ℝ) * ((j : ℝ) ^ 3)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num)).mul_left (1 / 6 : ℝ)
  have hconv : Filter.Tendsto (fun n : ℕ => ∑' j : ℕ, term n j) Filter.atTop
      (nhds (∑' j : ℕ, if Odd j then (1 / 6 : ℝ) * ((j : ℝ) ^ 3)⁻¹ else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hbound_sum term_tendsto ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn j
    exact term_norm_le n j hn
  have hlim_eq : (∑' j : ℕ, if Odd j then (1 / 6 : ℝ) * ((j : ℝ) ^ 3)⁻¹ else 0) =
      7 * zetaThree / 48 := by
    have hpull : (fun j : ℕ => if Odd j then (1 / 6 : ℝ) * ((j : ℝ) ^ 3)⁻¹ else 0) =
        fun j : ℕ => (1 / 6 : ℝ) * (if Odd j then ((j : ℝ) ^ 3)⁻¹ else 0) := by
      ext j
      split_ifs <;> ring
    rw [hpull, tsum_mul_left, tsum_odd_inv_cube]
    ring
  rw [hlim_eq] at hconv
  refine hconv.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (ratio_eq_tsum_term n hn).symm
