import OMAStatements.S_oeis_a285970

namespace OMA.S_oeis_a285970

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

/-! ### The scan of 0110 -> 0 reads t in tokens -/

lemma match_even (i : ℕ) :
    (tm (2 * i) = 0 ∧ tm (2 * i + 1) = 1 ∧ tm (2 * i + 2) = 1 ∧ tm (2 * i + 3) = 0) ↔
      (tm i = 0 ∧ tm (i + 1) = 1) := by
  rw [tm_even, tm_odd, show 2 * i + 2 = 2 * (i + 1) by ring, tm_even,
    show 2 * i + 3 = 2 * (i + 1) + 1 by ring, tm_odd]
  have := tm_le i
  have := tm_le (i + 1)
  omega

lemma no_match_odd (i : ℕ) :
    ¬ (tm (2 * i + 1) = 0 ∧ tm (2 * i + 1 + 1) = 1 ∧ tm (2 * i + 1 + 2) = 1 ∧
      tm (2 * i + 1 + 3) = 0) := by
  rw [tm_odd, show 2 * i + 1 + 1 = 2 * (i + 1) by ring, tm_even,
    show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring, tm_odd]
  have := tm_le i
  have := tm_le (i + 1)
  omega

lemma pos_succ (k : ℕ) : pos (k + 1) =
    if tm (pos k) = 0 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 1 ∧ tm (pos k + 3) = 0
      then pos k + 4 else pos k + 1 := rfl

/-- Z(k): the number of zeros among the first k output letters. -/
noncomputable def Z (k : ℕ) : ℕ := Nat.count (fun j => w j = 0) k

lemma Z_succ (k : ℕ) : Z (k + 1) = Z k + if w k = 0 then 1 else 0 := by
  unfold Z
  rw [Nat.count_succ]

/-- The token invariant. -/
lemma inv (k : ℕ) : ∃ i,
    (pos k = 2 * i ∧ (k : ℤ) = 2 * i - 3 * c01 i ∧ (Z k : ℤ) = i - c01 i) ∨
    (pos k = 2 * i + 1 ∧ ¬ (tm i = 0 ∧ tm (i + 1) = 1) ∧ (k : ℤ) = 2 * i - 3 * c01 i + 1 ∧
      (Z k : ℤ) = i - c01 i + (1 - tm i)) := by
  induction k with
  | zero => exact ⟨0, Or.inl ⟨rfl, by simp [c01], by simp [Z, c01]⟩⟩
  | succ k ih =>
    obtain ⟨i, ⟨hp, hk, hz⟩ | ⟨hp, hno, hk, hz⟩⟩ := ih
    · by_cases h01 : tm i = 0 ∧ tm (i + 1) = 1
      · have hm : tm (pos k) = 0 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 1 ∧
            tm (pos k + 3) = 0 := by rw [hp]; exact (match_even i).mpr h01
        refine ⟨i + 2, Or.inl ⟨?_, ?_, ?_⟩⟩
        · rw [pos_succ, if_pos hm, hp]; ring
        · have hc : c01 (i + 2) = c01 i + 1 := by
            rw [c01_succ, c01_succ, if_pos h01, if_neg (by omega)]
          push_cast
          rw [hc]
          push_cast
          linarith
        · have hc : c01 (i + 2) = c01 i + 1 := by
            rw [c01_succ, c01_succ, if_pos h01, if_neg (by omega)]
          have hw : w k = 0 := by unfold w; rw [if_pos hm]
          rw [Z_succ, if_pos hw, hc]
          push_cast
          linarith
      · have hm : ¬ (tm (pos k) = 0 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 1 ∧
            tm (pos k + 3) = 0) := by rw [hp]; exact fun h => h01 ((match_even i).mp h)
        refine ⟨i, Or.inr ⟨?_, h01, ?_, ?_⟩⟩
        · rw [pos_succ, if_neg hm, hp]
        · push_cast
          linarith
        · have hw : w k = tm i := by unfold w; rw [if_neg hm, hp, tm_even]
          rw [Z_succ, hw]
          have := tm_le i
          split_ifs with h
          · push_cast; rw [h]; push_cast; linarith
          · have : tm i = 1 := by omega
            push_cast; rw [this]; push_cast; linarith
    · have hm : ¬ (tm (pos k) = 0 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 1 ∧
          tm (pos k + 3) = 0) := by rw [hp]; exact no_match_odd i
      refine ⟨i + 1, Or.inl ⟨?_, ?_, ?_⟩⟩
      · rw [pos_succ, if_neg hm, hp]; ring
      · have hc : c01 (i + 1) = c01 i := by rw [c01_succ, if_neg hno, add_zero]
        rw [hc]
        push_cast
        linarith
      · have hc : c01 (i + 1) = c01 i := by rw [c01_succ, if_neg hno, add_zero]
        have hw : w k = 1 - tm i := by unfold w; rw [if_neg hm, hp, tm_odd]
        rw [Z_succ, hw, hc]
        have := tm_le i
        split_ifs with h
        · have : tm i = 1 := by omega
          push_cast; rw [this] at hz; push_cast at hz ⊢; linarith
        · have : tm i = 0 := by omega
          push_cast; rw [this] at hz; push_cast at hz ⊢; linarith

/-- |6 Z(k) - 4k| <= log2(2k + 3) + 4, and k <= 2 Z(k) + 1. -/
lemma Z_bound (k : ℕ) :
    |6 * (Z k : ℤ) - 4 * k| ≤ Nat.log 2 (2 * k + 3) + 4 ∧ k ≤ 2 * Z k + 1 := by
  obtain ⟨i, ⟨hp, hk, hz⟩ | ⟨hp, hno, hk, hz⟩⟩ := inv k
  all_goals
    have h2c := two_c01 i
    have hE := E_bound i
    have hch := ch_le i
    have htm := tm_le i
    have hi : i ≤ 2 * k + 3 := by
      have : (i : ℤ) ≤ 2 * k + 3 := by push_cast at h2c; omega
      omega
    have hlog : Nat.log 2 i ≤ Nat.log 2 (2 * k + 3) := Nat.log_mono_right hi
    unfold E at hE
    rw [abs_le] at hE ⊢
    push_cast at h2c hlog ⊢
  · refine ⟨⟨by omega, by omega⟩, by omega⟩
  · refine ⟨⟨by omega, by omega⟩, by omega⟩

/-! ### From the counting bound to the limit -/

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
    |4 * (a n : ℝ) - 6 * n| ≤ Real.logb 2 (4 * n + 3) + 6 ∧ (a n : ℝ) ≤ 2 * n := by
  set k := Nat.nth (fun k => w k = 0) (n - 1) with hk
  have hZ : Z k = n - 1 := Nat.count_nth_of_infinite zeros_infinite (n - 1)
  obtain ⟨h1, h2⟩ := Z_bound k
  rw [hZ] at h1 h2
  have ha : a n = k + 1 := rfl
  have hk2 : k ≤ 2 * n - 1 := by omega
  have hlog : (Nat.log 2 (2 * k + 3) : ℝ) ≤ Real.logb 2 (4 * n + 3) := by
    calc (Nat.log 2 (2 * k + 3) : ℝ) ≤ Real.logb 2 ((2 * k + 3 : ℕ) : ℝ) := Real.natLog_le_logb _ _
      _ ≤ Real.logb 2 (4 * n + 3) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
        have : (2 * k + 3 : ℕ) ≤ 4 * n + 3 := by omega
        exact_mod_cast this
  rw [abs_le] at h1
  have hn1 : ((n - 1 : ℕ) : ℤ) = n - 1 := by omega
  rw [hn1] at h1
  constructor
  · rw [abs_le, ha]
    push_cast
    have h1a : (6 * ((n : ℤ) - 1) - 4 * k : ℝ) ≥ -(Nat.log 2 (2 * k + 3) + 4 : ℝ) := by
      exact_mod_cast h1.1
    have h1b : (6 * ((n : ℤ) - 1) - 4 * k : ℝ) ≤ (Nat.log 2 (2 * k + 3) + 4 : ℝ) := by
      exact_mod_cast h1.2
    push_cast at h1a h1b
    constructor <;> linarith
  · rw [ha]
    have : (k + 1 : ℕ) ≤ 2 * n := by omega
    exact_mod_cast this

lemma tendsto_log_div : Tendsto (fun n : ℕ => (Real.logb 2 (4 * n + 3) + 6) / (n : ℝ))
    atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) :=
    hlog.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  -- logb 2 (4n+3) <= (log n + log 7) / log 2 for n >= 1
  have hb : ∀ᶠ n : ℕ in atTop, 0 ≤ (Real.logb 2 (4 * n + 3) + 6) / (n : ℝ) ∧
      (Real.logb 2 (4 * n + 3) + 6) / (n : ℝ) ≤
        (1 / Real.log 2) * (Real.log (n : ℝ) / n) + (Real.log 7 / Real.log 2 + 6) * (1 / n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpos : 0 ≤ Real.logb 2 (4 * n + 3) := Real.logb_nonneg (by norm_num) (by linarith)
    constructor
    · positivity
    · have h7 : Real.log (4 * n + 3) ≤ Real.log 7 + Real.log n := by
        rw [← Real.log_mul (by norm_num) (by linarith)]
        exact Real.log_le_log (by linarith) (by nlinarith)
      have hdiv : Real.logb 2 (4 * n + 3) ≤ (Real.log 7 + Real.log n) / Real.log 2 := by
        unfold Real.logb
        exact div_le_div_of_nonneg_right h7 hl2.le
      have hnpos : (0 : ℝ) < n := by linarith
      rw [div_le_iff₀ hnpos]
      have : (1 / Real.log 2) * (Real.log n / n) * n + (Real.log 7 / Real.log 2 + 6) * (1 / n) * n
          = (Real.log 7 + Real.log n) / Real.log 2 + 6 := by
        field_simp
        ring
      rw [add_mul, this]
      linarith
  have hlim : Tendsto (fun n : ℕ => (1 / Real.log 2) * (Real.log (n : ℝ) / n) +
      (Real.log 7 / Real.log 2 + 6) * (1 / n)) atTop (𝓝 0) := by
    have := (h1.const_mul (1 / Real.log 2)).add (h2.const_mul (Real.log 7 / Real.log 2 + 6))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (hb.mono fun n h => h.1) (hb.mono fun n h => h.2)

/-- Kimberling's conjecture: a(n)/n -> 3/2. -/
theorem conjecture : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (3 / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ᶠ n : ℕ in atTop, ‖(a n : ℝ) / n - 3 / 2‖ ≤
      (Real.logb 2 (4 * n + 3) + 6) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨h1, -⟩ := a_bound hn
    rw [Real.norm_eq_abs, show (a n : ℝ) / n - 3 / 2 = (4 * a n - 6 * n) / (4 * n) by
      field_simp; ring, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * n),
      div_le_div_iff₀ (by positivity) hnpos]
    have hlpos : 0 ≤ Real.logb 2 (4 * n + 3) := Real.logb_nonneg (by norm_num) (by linarith)
    nlinarith
  exact squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hb tendsto_log_div

end OMA.S_oeis_a285970

theorem OMA.solution : type_of% @OMA.S_oeis_a285970.main :=
  OMA.S_oeis_a285970.conjecture
