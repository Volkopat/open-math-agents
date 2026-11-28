import OMAReductions.R_Erdos615_erdos_615_variants_fox_loh_zhao_R1

-- Step Erdos615.erdos_615.variants.fox_loh_zhao.R1.H3: hypothesis H3 of reduction Erdos615.erdos_615.variants.fox_loh_zhao.R1
-- Credit: @luciusacarr

namespace OMA.E615H3

open Real

/-- The parameter choice for one fixed large `n`. -/
theorem core (C δ B fn L : ℝ) (n h m : ℕ) (hC : 0 < C) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hB1 : 1 ≤ B) (hCB : C / δ ≤ B) (hL : L = Real.log n) (hL4 : 4 ≤ L)
    (hLL1 : 1 ≤ Real.log L) (hLLB : 4 * Real.log B ≤ Real.log L)
    (h32 : 64 ≤ √L) (hTη : 2 * (Real.log 4 / (δ / 12)) ^ 2 ≤ √L)
    (hf0 : 0 ≤ fn) (hf : fn ≤ δ / 12 * √(L / Real.log L))
    (hh : h = ⌊L / Real.log L⌋₊) (hm : m = 2 * (n / 2)) :
    16 ≤ h ∧ Even m ∧ m ≤ n ∧ (C * √(h : ℝ) / δ) ^ h ≤ (m : ℝ) ∧
      2 * m * Real.exp (-δ * √(h : ℝ) / 4) + ((n : ℝ) - m) ≤ n * Real.exp (-fn) := by
  set LL := Real.log L with hLL_def
  set t := L / LL with ht_def
  have hLpos : 0 < L := by linarith
  have hLLpos : 0 < LL := by linarith
  have hsqL : √L * √L = L := Real.mul_self_sqrt hLpos.le
  have hsqLpos : 0 < √L := by linarith
  have hLLle : LL ≤ 2 * √L := by
    have h1 := Real.log_le_sub_one_of_pos hsqLpos
    rw [Real.log_sqrt hLpos.le] at h1
    linarith
  have ht_ge : √L / 2 ≤ t := by
    rw [ht_def, le_div_iff₀ hLLpos]
    nlinarith
  have ht_le : t ≤ L := div_le_self hLpos.le hLL1
  have ht0 : 0 ≤ t := by linarith
  have hh_le : (h : ℝ) ≤ t := by rw [hh]; exact Nat.floor_le ht0
  have hh_ge : t - 1 < (h : ℝ) := by rw [hh]; exact Nat.sub_one_lt_floor t
  have hh16 : 16 ≤ h := by
    have : (15 : ℝ) < h := by linarith
    exact_mod_cast this
  have hhpos : (0 : ℝ) < h := by linarith
  -- n is large
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero] at hL
      linarith
    · exact_mod_cast h0
  have hnexp : Real.exp L = n := by rw [hL, Real.exp_log hnpos]
  have hn2 : (2 : ℝ) ≤ n := by
    have := Real.add_one_le_exp L
    linarith
  have hmn : m ≤ n := by rw [hm]; exact Nat.mul_div_le n 2
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hm1 : (n : ℝ) ≤ m + 1 := by
    have : n ≤ m + 1 := by omega
    exact_mod_cast this
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  refine ⟨hh16, by rw [hm]; exact even_two_mul _, hmn, ?_, ?_⟩
  · -- the size condition
    have hlB : 0 ≤ Real.log B := Real.log_nonneg hB1
    have hBpos : 0 < B := by linarith
    have hsqh : 0 < √(h : ℝ) := Real.sqrt_pos.2 hhpos
    have hBh : C * √(h : ℝ) / δ ≤ B * √(h : ℝ) := by
      rw [show C * √(h : ℝ) / δ = C / δ * √(h : ℝ) by ring]
      exact mul_le_mul_of_nonneg_right hCB hsqh.le
    have hC0 : 0 ≤ C * √(h : ℝ) / δ := by positivity
    have hlogh : Real.log h ≤ LL := Real.log_le_log hhpos (by linarith)
    have hlogBh : Real.log (B * √(h : ℝ)) ≤ Real.log B + LL / 2 := by
      rw [Real.log_mul hBpos.ne' hsqh.ne', Real.log_sqrt hhpos.le]
      linarith
    have htLL : LL * t = L := by rw [ht_def]; field_simp
    have hkey : Real.log (B * √(h : ℝ)) * h ≤ L - Real.log 2 := by
      have hq : 0 ≤ Real.log B + LL / 2 := by linarith
      have e1 : Real.log (B * √(h : ℝ)) * h ≤ (Real.log B + LL / 2) * h :=
        mul_le_mul_of_nonneg_right hlogBh hhpos.le
      have e2 : (Real.log B + LL / 2) * h ≤ (Real.log B + LL / 2) * t :=
        mul_le_mul_of_nonneg_left hh_le hq
      have e3 : 4 * Real.log B * t ≤ LL * t := mul_le_mul_of_nonneg_right hLLB ht0
      nlinarith
    calc (C * √(h : ℝ) / δ) ^ h ≤ (B * √(h : ℝ)) ^ h := pow_le_pow_left₀ hC0 hBh h
      _ = Real.exp (Real.log (B * √(h : ℝ)) * h) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
      _ ≤ Real.exp (L - Real.log 2) := Real.exp_le_exp.2 hkey
      _ = n / 2 := by rw [Real.exp_sub, hnexp, Real.exp_log two_pos]
      _ ≤ m := by linarith
  · -- the exponential condition
    set s := √t with hs_def
    have hs2 : s ^ 2 = t := Real.sq_sqrt ht0
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hsh : 2 / 3 * s ≤ √(h : ℝ) := by
      have : (2 / 3 * s) ^ 2 ≤ (h : ℝ) := by nlinarith
      calc 2 / 3 * s = √((2 / 3 * s) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ √(h : ℝ) := Real.sqrt_le_sqrt this
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hη : 0 < δ / 12 := by positivity
    have hsl : Real.log 4 / (δ / 12) ≤ s := by
      have : (Real.log 4 / (δ / 12)) ^ 2 ≤ t := by nlinarith
      calc Real.log 4 / (δ / 12) = √((Real.log 4 / (δ / 12)) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ s := Real.sqrt_le_sqrt this
    have hsl' : Real.log 4 ≤ δ / 12 * s := by
      rw [div_le_iff₀ hη] at hsl; linarith
    have hsL : s ≤ L / 2 := by
      have : s ≤ √L := Real.sqrt_le_sqrt ht_le
      have h2L : 2 * √L ≤ √L * √L := mul_le_mul_of_nonneg_right (by linarith) hsqLpos.le
      linarith
    have ha : fn + Real.log 4 ≤ δ * √(h : ℝ) / 4 := by
      have h1 := mul_le_mul_of_nonneg_left hsh hδ.le
      have h2 : δ * (2 / 3 * s) = 8 * (δ / 12 * s) := by ring
      have h3 : δ * √(h : ℝ) / 4 = (δ * √(h : ℝ)) / 4 := rfl
      linarith
    have hfL : fn ≤ L - Real.log 2 := by
      have : δ / 12 * s ≤ s := mul_le_of_le_one_left hs0 (by linarith)
      linarith
    have hE : Real.exp (-δ * √(h : ℝ) / 4) ≤ Real.exp (-fn) / 4 := by
      calc Real.exp (-δ * √(h : ℝ) / 4) ≤ Real.exp (-(fn + Real.log 4)) := by
            apply Real.exp_le_exp.2
            rw [neg_mul, neg_div]
            exact neg_le_neg ha
        _ = Real.exp (-fn) / 4 := by
            rw [neg_add, Real.exp_add, Real.exp_neg (Real.log 4),
              Real.exp_log (by norm_num)]
            ring
    have hF : 2 ≤ n * Real.exp (-fn) := by
      have : Real.exp (-(L - Real.log 2)) ≤ Real.exp (-fn) := Real.exp_le_exp.2 (by linarith)
      rw [neg_sub, Real.exp_sub, Real.exp_log two_pos, hnexp] at this
      rw [div_le_iff₀ hnpos] at this
      linarith
    have hE0 : 0 ≤ Real.exp (-δ * √(h : ℝ) / 4) := (Real.exp_pos _).le
    have k1 := mul_le_mul_of_nonneg_right hmn' hE0
    have k2 := mul_le_mul_of_nonneg_left hE hnpos.le
    have k3 : (n : ℝ) * (Real.exp (-fn) / 4) = n * Real.exp (-fn) / 4 := by ring
    linarith

/-- The quadratic edge-count condition. -/
theorem quad (ε δ n m : ℝ) (hε : 0 < ε) (hδ : δ = min ε (1 / 2) / 4)
    (hn1 : 1 ≤ n) (hm1 : n - 1 ≤ m) (hn : 1 ≤ 12 * δ * n) :
    (1 / 8 - ε) * n ^ 2 ≤ (1 / 4 - 2 * δ) * m ^ 2 / 2 := by
  have hδε : δ ≤ ε / 4 := by rw [hδ]; have := min_le_left ε (1 / 2); linarith
  have hδ8 : δ ≤ 1 / 8 := by rw [hδ]; have := min_le_right ε (1 / 2); linarith
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hsq : (n - 1) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by linarith) hm1 2
  have hR : (1 / 8 - δ) * (n - 1) ^ 2 ≤ (1 / 4 - 2 * δ) * m ^ 2 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 1 / 8 - δ by linarith)]
  by_cases hb : 1 / 8 - ε ≤ 0
  · have : (1 / 8 - ε) * n ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb (sq_nonneg n)
    have : 0 ≤ (1 / 8 - δ) * (n - 1) ^ 2 := by
      apply mul_nonneg <;> nlinarith
    linarith
  · have h1 : (1 / 8 - ε) * n ^ 2 ≤ (1 / 8 - 4 * δ) * n ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg n)
    have h2 : (1 / 8 - 4 * δ) * n ^ 2 ≤ (1 / 8 - δ) * (n - 1) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hn (show 0 ≤ n by linarith)]
    linarith

end OMA.E615H3

open Filter in
theorem OMA.solution : OMA.R_Erdos615_erdos_615_variants_fox_loh_zhao_R1.H3 := by
  intro C hC f hf0 hf ε hε
  set δ : ℝ := min ε (1 / 2) / 4 with hδ_def
  have hδ0 : 0 < δ := by positivity
  have hδ8 : δ ≤ 1 / 8 := by have := min_le_right ε (1 / 2); linarith
  refine ⟨δ, hδ0, by linarith, ?_⟩
  set B : ℝ := max 1 (C / δ) with hB_def
  set T : ℝ := max 64 (2 * (Real.log 4 / (δ / 12)) ^ 2) with hT_def
  set L0 : ℝ := max (max 4 (Real.exp (max 1 (4 * Real.log B)))) (T ^ 2) with hL0_def
  have e1 : ∀ᶠ n : ℕ in atTop, L0 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop L0
  have e2 : ∀ᶠ n : ℕ in atTop,
      f n / Real.sqrt (Real.log n / Real.log (Real.log n)) < δ / 12 :=
    hf.eventually (gt_mem_nhds (by positivity))
  have e3 : ∀ᶠ n : ℕ in atTop, 1 / (12 * δ) + 1 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [e1, e2, e3] with n h1 h2 h3
  set L := Real.log n with hL_def
  have hL4 : 4 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
  have hLexp : Real.exp (max 1 (4 * Real.log B)) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h1
  have hLT : T ^ 2 ≤ L := le_trans (le_max_right _ _) h1
  have hLL : max 1 (4 * Real.log B) ≤ Real.log L :=
    (Real.le_log_iff_exp_le (by linarith)).2 hLexp
  have hTs : T ≤ √L := by
    calc T = √(T ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ √L := Real.sqrt_le_sqrt hLT
  have hLLpos : 0 < Real.log L := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hLL)
  have hspos : 0 < √(L / Real.log L) := Real.sqrt_pos.2 (div_pos (by linarith) hLLpos)
  have hfle : f n ≤ δ / 12 * √(L / Real.log L) := by
    rw [div_lt_iff₀ hspos] at h2; linarith
  obtain ⟨c1, c2, c3, c4, c5⟩ := OMA.E615H3.core C δ B (f n) L n ⌊L / Real.log L⌋₊ (2 * (n / 2))
    hC hδ0 hδ8 (le_max_left _ _) (le_max_right _ _) rfl hL4 (le_trans (le_max_left _ _) hLL)
    (le_trans (le_max_right _ _) hLL) (le_trans (le_max_left _ _) hTs)
    (le_trans (le_max_right _ _) hTs) (hf0 n) hfle rfl rfl
  refine ⟨_, _, c1, c2, c3, c4, c5, ?_⟩
  have hn1 : (n : ℝ) ≤ ((2 * (n / 2) : ℕ) : ℝ) + 1 := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    exact_mod_cast this
  have hn12 : 1 ≤ 12 * δ * n := by
    have := (div_le_iff₀ (show 0 < 12 * δ by positivity)).1
      (show 1 / (12 * δ) ≤ n by linarith)
    linarith
  exact OMA.E615H3.quad ε δ n _ hε hδ_def (by
    have : 0 ≤ 1 / (12 * δ) := by positivity
    linarith) (by linarith) hn12
