import OMAStatements.S_oeis_a286337

namespace OMA.S_oeis_a286337

open Filter Topology





/-! ### Thue-Morse -/

lemma tm_even (m : ℕ) : tm (2 * m) = tm m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  · unfold tm
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp

lemma tm_odd (m : ℕ) : tm (2 * m + 1) = 1 - tm m := by
  unfold tm
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [h1, h2, List.count_cons_self]
  omega

lemma tm_le (n : ℕ) : tm n ≤ 1 := by
  unfold tm
  omega

/-! ### Letter changes and the factor 01 -/

/-- The number of j < n with t(j) ≠ t(j+1). -/
def ch (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, if tm j ≠ tm (j + 1) then 1 else 0

lemma ch_succ (n : ℕ) : ch (n + 1) = ch n + if tm n ≠ tm (n + 1) then 1 else 0 :=
  Finset.sum_range_succ _ _

lemma ch_le (n : ℕ) : ch n ≤ n := by
  induction n with
  | zero => simp [ch]
  | succ n ih => rw [ch_succ]; split_ifs <;> omega

lemma ch_two_mul (m : ℕ) : (ch (2 * m) : ℤ) = 2 * m - ch m := by
  induction m with
  | zero => simp [ch]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, ch_succ, ch_succ, ch_succ m]
    have e1 : tm (2 * m + 1) = 1 - tm m := tm_odd m
    have e2 : tm (2 * m + 1 + 1) = tm (m + 1) := by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, tm_even]
    have e0 : tm (2 * m) = tm m := tm_even m
    rw [e0, e1, e2]
    have := tm_le m
    have := tm_le (m + 1)
    push_cast
    split_ifs <;> omega

lemma ch_two_mul_add_one (m : ℕ) : (ch (2 * m + 1) : ℤ) = 2 * m + 1 - ch m := by
  rw [ch_succ, tm_even, tm_odd]
  have := tm_le m
  push_cast
  rw [ch_two_mul]
  split_ifs <;> omega

/-- E(n) = 3 ch(n) - 2n. -/
def E (n : ℕ) : ℤ := 3 * (ch n : ℤ) - 2 * n

lemma E_bound (n : ℕ) : |E n| ≤ Nat.log 2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · simp [E, ch]
      · simp [E, ch, tm]
    · obtain ⟨m, hm | hm⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
      · have hm1 : 1 ≤ m := by omega
        have hlog : Nat.log 2 n = Nat.log 2 m + 1 := by
          rw [Nat.log_of_one_lt_of_le (by norm_num) h, show n / 2 = m by omega]
        have hE : E n = -E m := by
          unfold E
          rw [hm, ch_two_mul]
          push_cast
          ring
        rw [hE, abs_neg, hlog]
        have := ih m (by omega)
        push_cast
        linarith
      · have hlog : Nat.log 2 n = Nat.log 2 m + 1 := by
          rw [Nat.log_of_one_lt_of_le (by norm_num) h, show n / 2 = m by omega]
        have hE : E n = 1 - E m := by
          unfold E
          rw [hm, ch_two_mul_add_one]
          push_cast
          ring
        rw [hE, hlog]
        have := ih m (by omega)
        push_cast
        have := abs_sub (1 : ℤ) (E m)
        have : |(1 : ℤ)| = 1 := by norm_num
        linarith

/-- The number of j < n with t(j) t(j+1) = 01. -/
def c01 (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, if tm j = 0 ∧ tm (j + 1) = 1 then 1 else 0

lemma c01_succ (n : ℕ) : c01 (n + 1) = c01 n + if tm n = 0 ∧ tm (n + 1) = 1 then 1 else 0 :=
  Finset.sum_range_succ _ _

lemma two_c01 (n : ℕ) : 2 * c01 n = ch n + tm n := by
  induction n with
  | zero => simp [c01, ch, tm]
  | succ n ih =>
    rw [c01_succ, ch_succ]
    have := tm_le n
    have := tm_le (n + 1)
    split_ifs <;> omega

/-- |6 c01(m) - 2m| <= log2 m + 4. -/
lemma c01_bound (m : ℕ) : |6 * (c01 m : ℤ) - 2 * m| ≤ Nat.log 2 m + 4 := by
  have h2 := two_c01 m
  have hE := E_bound m
  have := tm_le m
  unfold E at hE
  rw [abs_le] at hE ⊢
  push_cast at h2
  constructor <;> omega

/-! ### Generic limit lemma -/

lemma tendsto_log_div (C : ℝ) : Tendsto (fun n : ℕ => (Real.logb 2 (8 * n + 8) + C) / (n : ℝ))
    atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) :=
    hlog.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : ∀ᶠ n : ℕ in atTop, (Real.logb 2 (8 * n + 8) + C) / (n : ℝ) =
      (1 / Real.log 2) * (Real.log (n : ℝ) / n) + (Real.log 8 / Real.log 2 + C) * (1 / n) +
      (Real.log (1 + 1 / (n : ℝ)) / Real.log 2) * (1 / n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hsplit : Real.log (8 * n + 8) = Real.log 8 + Real.log n + Real.log (1 + 1 / n) := by
      rw [← Real.log_mul (by norm_num) (by linarith), ← Real.log_mul (by positivity)
        (by positivity)]
      congr 1
      field_simp
    unfold Real.logb
    rw [hsplit]
    field_simp
    ring
  have h3 : Tendsto (fun n : ℕ => Real.log (1 + 1 / (n : ℝ)) / Real.log 2) atTop
      (𝓝 (Real.log (1 + 0) / Real.log 2)) := by
    apply Tendsto.div_const
    apply Tendsto.log _ (by norm_num)
    exact tendsto_const_nhds.add h2
  have hlim : Tendsto (fun n : ℕ => (1 / Real.log 2) * (Real.log (n : ℝ) / n) +
      (Real.log 8 / Real.log 2 + C) * (1 / n) +
      (Real.log (1 + 1 / (n : ℝ)) / Real.log 2) * (1 / n)) atTop (𝓝 0) := by
    have := ((h1.const_mul (1 / Real.log 2)).add (h2.const_mul (Real.log 8 / Real.log 2 + C))).add
      (h3.mul h2)
    simpa using this
  exact hlim.congr' (hb.mono fun n h => h.symm)

lemma lim_of_bound {f : ℕ → ℕ} {p q C : ℝ} (hq : 0 < q)
    (h : ∀ n : ℕ, 1 ≤ n → |q * (f n : ℝ) - p * n| ≤ Real.logb 2 (8 * n + 8) + C) :
    Tendsto (fun n : ℕ => (f n : ℝ) / n) atTop (𝓝 (p / q)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ᶠ n : ℕ in atTop, ‖(f n : ℝ) / n - p / q‖ ≤
      (1 / q) * ((Real.logb 2 (8 * n + 8) + C) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, show (f n : ℝ) / n - p / q = (q * f n - p * n) / (q * n) by
      field_simp, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * n),
      div_le_iff₀ (by positivity)]
    have := h n hn
    calc |q * (f n : ℝ) - p * n| ≤ Real.logb 2 (8 * n + 8) + C := this
      _ = 1 / q * ((Real.logb 2 (8 * n + 8) + C) / n) * (q * n) := by field_simp
  have hlim := (tendsto_log_div C).const_mul (1 / q)
  rw [mul_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hb hlim

/-! ### The scan of 1101 -> 0 -/

/-- The number of j < n with x_j x_{j+1} x_{j+2} = 011. -/
def occ (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if tm j = 0 ∧ tm (j + 1) = 1 ∧ tm (j + 2) = 1 then 1 else 0

lemma occ_succ (n : ℕ) :
    occ (n + 1) = occ n + if tm n = 0 ∧ tm (n + 1) = 1 ∧ tm (n + 2) = 1 then 1 else 0 :=
  Finset.sum_range_succ _ _

lemma occ_two_mul (m : ℕ) : occ (2 * m) = c01 m := by
  induction m with
  | zero => simp [occ, c01]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, occ_succ, occ_succ, ih, c01_succ]
    have e0 : tm (2 * m) = tm m := tm_even m
    have e1 : tm (2 * m + 1) = 1 - tm m := tm_odd m
    have e2 : tm (2 * m + 1 + 1) = tm (m + 1) := by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, tm_even]
    have e2' : tm (2 * m + 2) = tm (m + 1) := by
      rw [show 2 * m + 2 = 2 * (m + 1) by ring, tm_even]
    have e3 : tm (2 * m + 1 + 2) = 1 - tm (m + 1) := by
      rw [show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring, tm_odd]
    simp only [e0, e1, e2, e2', e3]
    have := tm_le m
    have := tm_le (m + 1)
    split_ifs <;> omega

lemma occ_two_mul_add_one (m : ℕ) : occ (2 * m + 1) = c01 (m + 1) := by
  rw [occ_succ, occ_two_mul, c01_succ, tm_even, tm_odd, show 2 * m + 2 = 2 * (m + 1) by ring,
    tm_even]
  have := tm_le m
  have := tm_le (m + 1)
  split_ifs <;> omega

/-- |6 occ(i) - i| <= log2 i + 6 and 4 occ(i) <= i + 4. -/
lemma occ_bound (i : ℕ) : |6 * (occ i : ℤ) - i| ≤ Nat.log 2 i + 6 ∧ 4 * occ i ≤ i + 4 := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, i = 2 * m ∨ i = 2 * m + 1 := ⟨i / 2, by omega⟩
  · rw [occ_two_mul]
    have hb := c01_bound m
    have h2 := two_c01 m
    have := ch_le m
    have := tm_le m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [c01]
    · have hlog : Nat.log 2 m ≤ Nat.log 2 (2 * m) := Nat.log_mono_right (by omega)
      rw [abs_le] at hb ⊢
      push_cast
      refine ⟨⟨by omega, by omega⟩, by omega⟩
  · rw [occ_two_mul_add_one]
    have hb := c01_bound (m + 1)
    have h2 := two_c01 (m + 1)
    have := ch_le (m + 1)
    have := tm_le (m + 1)
    have hlog : Nat.log 2 (m + 1) ≤ Nat.log 2 (2 * m + 1) := Nat.log_mono_right (by omega)
    rw [abs_le] at hb ⊢
    push_cast at hb ⊢
    refine ⟨⟨by omega, by omega⟩, by omega⟩

lemma match_odd (i : ℕ) :
    (tm (2 * i + 1) = 1 ∧ tm (2 * i + 1 + 1) = 1 ∧ tm (2 * i + 1 + 2) = 0 ∧
      tm (2 * i + 1 + 3) = 1) ↔ (tm i = 0 ∧ tm (i + 1) = 1 ∧ tm (i + 2) = 1) := by
  rw [tm_odd, show 2 * i + 1 + 1 = 2 * (i + 1) by ring, tm_even,
    show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring, tm_odd,
    show 2 * i + 1 + 3 = 2 * (i + 2) by ring, tm_even]
  have := tm_le i
  have := tm_le (i + 1)
  have := tm_le (i + 2)
  omega

lemma no_match_even (i : ℕ) :
    ¬ (tm (2 * i) = 1 ∧ tm (2 * i + 1) = 1 ∧ tm (2 * i + 2) = 0 ∧ tm (2 * i + 3) = 1) := by
  rw [tm_even, tm_odd]
  have := tm_le i
  omega

lemma pos_succ (k : ℕ) : pos (k + 1) =
    if tm (pos k) = 1 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 ∧ tm (pos k + 3) = 1
      then pos k + 4 else pos k + 1 := rfl

/-- Z(k): the number of zeros among the first k output letters. -/
noncomputable def Z (k : ℕ) : ℕ := Nat.count (fun j => w j = 0) k

lemma Z_succ (k : ℕ) : Z (k + 1) = Z k + if w k = 0 then 1 else 0 := by
  unfold Z
  rw [Nat.count_succ]

/-- The scan invariant. -/
lemma inv (k : ℕ) : ∃ i,
    (pos k = 2 * i ∧ (k : ℤ) = 2 * i - 3 * occ i ∧ (Z k : ℤ) = i) ∨
    (pos k = 2 * i + 1 ∧ (k : ℤ) = 2 * i + 1 - 3 * occ i ∧ (Z k : ℤ) = i + 1 - tm i) := by
  induction k with
  | zero => exact ⟨0, Or.inl ⟨rfl, by simp [occ], by simp [Z]⟩⟩
  | succ k ih =>
    obtain ⟨i, ⟨hp, hk, hz⟩ | ⟨hp, hk, hz⟩⟩ := ih
    · have hm : ¬ (tm (pos k) = 1 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 ∧
          tm (pos k + 3) = 1) := by rw [hp]; exact no_match_even i
      refine ⟨i, Or.inr ⟨?_, ?_, ?_⟩⟩
      · rw [pos_succ, if_neg hm, hp]
      · push_cast; linarith
      · have hw : w k = tm i := by unfold w; rw [if_neg hm, hp, tm_even]
        rw [Z_succ, hw]
        have := tm_le i
        split_ifs with h
        · rw [h]; push_cast; linarith
        · have : tm i = 1 := by omega
          rw [this]; push_cast; linarith
    · by_cases hP : tm i = 0 ∧ tm (i + 1) = 1 ∧ tm (i + 2) = 1
      · have hm : tm (pos k) = 1 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 ∧
            tm (pos k + 3) = 1 := by rw [hp]; exact (match_odd i).mpr hP
        have hc : occ (i + 2) = occ i + 1 := by
          rw [occ_succ, occ_succ, if_pos hP, if_neg (by omega)]
        refine ⟨i + 2, Or.inr ⟨?_, ?_, ?_⟩⟩
        · rw [pos_succ, if_pos hm, hp]; ring
        · rw [hc]; push_cast; linarith
        · have hw : w k = 0 := by unfold w; rw [if_pos hm]
          rw [Z_succ, if_pos hw, hP.2.2]
          rw [hP.1] at hz
          push_cast at hz ⊢
          linarith
      · have hm : ¬ (tm (pos k) = 1 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 ∧
            tm (pos k + 3) = 1) := by rw [hp]; exact fun h => hP ((match_odd i).mp h)
        have hc : occ (i + 1) = occ i := by rw [occ_succ, if_neg hP, add_zero]
        refine ⟨i + 1, Or.inl ⟨?_, ?_, ?_⟩⟩
        · rw [pos_succ, if_neg hm, hp]; ring
        · rw [hc]; push_cast; linarith
        · have hw : w k = 1 - tm i := by unfold w; rw [if_neg hm, hp, tm_odd]
          rw [Z_succ, hw]
          have := tm_le i
          split_ifs with h
          · have : tm i = 1 := by omega
            rw [this] at hz; push_cast at hz ⊢; linarith
          · have : tm i = 0 := by omega
            rw [this] at hz; push_cast at hz ⊢; linarith

/-- |3 Z(k) - 2k| <= log2(2k + 8) + 8 and k <= 2 Z(k) + 1. -/
lemma Z_bound (k : ℕ) :
    |3 * (Z k : ℤ) - 2 * k| ≤ Nat.log 2 (2 * k + 8) + 8 ∧ k ≤ 2 * Z k + 1 := by
  obtain ⟨i, ⟨hp, hk, hz⟩ | ⟨hp, hk, hz⟩⟩ := inv k
  all_goals
    obtain ⟨hb, h4⟩ := occ_bound i
    have htm := tm_le i
    have hi : i ≤ 2 * k + 8 := by omega
    have hlog : Nat.log 2 i ≤ Nat.log 2 (2 * k + 8) := Nat.log_mono_right hi
    rw [abs_le] at hb ⊢
    push_cast at hlog ⊢
  · refine ⟨⟨by omega, by omega⟩, by omega⟩
  · refine ⟨⟨by omega, by omega⟩, by omega⟩

lemma zeros_infinite : (setOf (fun k => w k = 0)).Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := hfin.bddAbove
  have hcount : ∀ k, Z k ≤ B + 1 := by
    intro k
    unfold Z
    rw [Nat.count_eq_card_filter_range]
    calc ((Finset.range k).filter (fun j => w j = 0)).card
        ≤ (Finset.range (B + 1)).card := by
          apply Finset.card_le_card
          intro j hj
          rw [Finset.mem_filter] at hj
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hB hj.2))
      _ = B + 1 := Finset.card_range _
  have := (Z_bound (2 * B + 4)).2
  have := hcount (2 * B + 4)
  omega

lemma a_bound {n : ℕ} (hn : 1 ≤ n) :
    |2 * (a n : ℝ) - 3 * n| ≤ Real.logb 2 (8 * n + 8) + 10 := by
  set k := Nat.nth (fun k => w k = 0) (n - 1) with hk
  have hZ : Z k = n - 1 := Nat.count_nth_of_infinite zeros_infinite (n - 1)
  obtain ⟨h1, h2⟩ := Z_bound k
  rw [hZ] at h1 h2
  have ha : a n = k + 1 := rfl
  have hk2 : k ≤ 2 * n - 1 := by omega
  have hlog : (Nat.log 2 (2 * k + 8) : ℝ) ≤ Real.logb 2 (8 * n + 8) := by
    calc (Nat.log 2 (2 * k + 8) : ℝ) ≤ Real.logb 2 ((2 * k + 8 : ℕ) : ℝ) :=
          Real.natLog_le_logb _ _
      _ ≤ Real.logb 2 (8 * n + 8) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
        have : (2 * k + 8 : ℕ) ≤ 8 * n + 8 := by omega
        exact_mod_cast this
  rw [abs_le] at h1
  have hn1 : ((n - 1 : ℕ) : ℤ) = n - 1 := by omega
  rw [hn1] at h1
  rw [abs_le, ha]
  push_cast
  have h1a : (3 * ((n : ℤ) - 1) - 2 * k : ℝ) ≥ -(Nat.log 2 (2 * k + 8) + 8 : ℝ) := by
    exact_mod_cast h1.1
  have h1b : (3 * ((n : ℤ) - 1) - 2 * k : ℝ) ≤ (Nat.log 2 (2 * k + 8) + 8 : ℝ) := by
    exact_mod_cast h1.2
  push_cast at h1a h1b
  constructor <;> linarith

/-- Kimberling's conjecture: a(n)/n -> 3/2. -/
theorem conjecture : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (3 / 2)) :=
  lim_of_bound (by norm_num) fun n hn => a_bound hn

end OMA.S_oeis_a286337

theorem OMA.solution : type_of% @OMA.S_oeis_a286337.main :=
  OMA.S_oeis_a286337.conjecture
