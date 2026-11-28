import OMAStatements.S_oeis_a286057

namespace OMA.S_oeis_a286057

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

lemma no_three (i : ℕ) : ¬ (tm i = tm (i + 1) ∧ tm (i + 1) = tm (i + 2)) := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, i = 2 * m ∨ i = 2 * m + 1 := ⟨i / 2, by omega⟩
  · rw [tm_even m, tm_odd m]
    have := tm_le m
    omega
  · rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, tm_even (m + 1),
      show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring, tm_odd (m + 1)]
    have := tm_le (m + 1)
    omega

/-! ### Letter changes -/

/-- The number of j < n with t(j) ≠ t(j+1). -/
def ch (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, if tm j ≠ tm (j + 1) then 1 else 0

lemma ch_succ (n : ℕ) : ch (n + 1) = ch n + if tm n ≠ tm (n + 1) then 1 else 0 :=
  Finset.sum_range_succ _ _

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
      · have hlog : Nat.log 2 n = Nat.log 2 m + 1 := by
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

/-! ### Generic limit lemma -/

lemma tendsto_log_div (K C : ℝ) :
    Tendsto (fun n : ℕ => (K * Real.logb 2 (8 * n + 8) + C) / (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) :=
    hlog.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : ∀ᶠ n : ℕ in atTop, (K * Real.logb 2 (8 * n + 8) + C) / (n : ℝ) =
      (K / Real.log 2) * (Real.log (n : ℝ) / n) + (K * Real.log 8 / Real.log 2 + C) * (1 / n) +
      (K * Real.log (1 + 1 / (n : ℝ)) / Real.log 2) * (1 / n) := by
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
  have h3 : Tendsto (fun n : ℕ => K * Real.log (1 + 1 / (n : ℝ)) / Real.log 2) atTop
      (𝓝 (K * Real.log (1 + 0) / Real.log 2)) := by
    apply Tendsto.div_const
    apply Tendsto.const_mul
    apply Tendsto.log _ (by norm_num)
    exact tendsto_const_nhds.add h2
  have hlim : Tendsto (fun n : ℕ => (K / Real.log 2) * (Real.log (n : ℝ) / n) +
      (K * Real.log 8 / Real.log 2 + C) * (1 / n) +
      (K * Real.log (1 + 1 / (n : ℝ)) / Real.log 2) * (1 / n)) atTop (𝓝 0) := by
    have := ((h1.const_mul (K / Real.log 2)).add
      (h2.const_mul (K * Real.log 8 / Real.log 2 + C))).add (h3.mul h2)
    simpa using this
  exact hlim.congr' (hb.mono fun n h => h.symm)

lemma lim_of_bound {f : ℕ → ℕ} {p q K C : ℝ} (hq : 0 < q)
    (h : ∀ n : ℕ, 1 ≤ n → |q * (f n : ℝ) - p * n| ≤ K * Real.logb 2 (8 * n + 8) + C) :
    Tendsto (fun n : ℕ => (f n : ℝ) / n) atTop (𝓝 (p / q)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ᶠ n : ℕ in atTop, ‖(f n : ℝ) / n - p / q‖ ≤
      (1 / q) * ((K * Real.logb 2 (8 * n + 8) + C) / (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, show (f n : ℝ) / n - p / q = (q * f n - p * n) / (q * n) by
      field_simp, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * n),
      div_le_iff₀ (by positivity)]
    have := h n hn
    calc |q * (f n : ℝ) - p * n| ≤ K * Real.logb 2 (8 * n + 8) + C := this
      _ = 1 / q * ((K * Real.logb 2 (8 * n + 8) + C) / n) * (q * n) := by field_simp
  have hlim := (tendsto_log_div K C).const_mul (1 / q)
  rw [mul_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hb hlim

/-! ### Occurrences of 010 and letters 1 in t -/

/-- The number of j < n at which 010 starts in t. -/
def occ (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if tm j = 0 ∧ tm (j + 1) = 1 ∧ tm (j + 2) = 0 then 1 else 0

lemma occ_succ (n : ℕ) :
    occ (n + 1) = occ n + if tm n = 0 ∧ tm (n + 1) = 1 ∧ tm (n + 2) = 0 then 1 else 0 :=
  Finset.sum_range_succ _ _

/-- The number of letters 1 of t below n. -/
def ones (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, if tm j = 1 then 1 else 0

lemma ones_succ (n : ℕ) : ones (n + 1) = ones n + if tm n = 1 then 1 else 0 :=
  Finset.sum_range_succ _ _

lemma ones_two_mul (m : ℕ) : ones (2 * m) = m := by
  induction m with
  | zero => simp [ones]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, ones_succ, ones_succ, ih, tm_even, tm_odd]
    have := tm_le m
    split_ifs <;> omega

lemma ones_bound (N : ℕ) : N ≤ 2 * ones N + 1 ∧ 2 * ones N ≤ N + 1 := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, N = 2 * m ∨ N = 2 * m + 1 := ⟨N / 2, by omega⟩
  · rw [ones_two_mul]; omega
  · rw [ones_succ, ones_two_mul]; split_ifs <;> omega

/-- 010 starts at 2j exactly when x_j x_{j+1} = 00 and at 2j+1 exactly when x_j x_{j+1} = 11,
so occ(2m) counts the j < m with x_j = x_{j+1}. -/
lemma occ_two_mul (m : ℕ) : occ (2 * m) + ch m = m := by
  induction m with
  | zero => simp [occ, ch]
  | succ m ih =>
    have h1 := occ_succ (2 * m)
    have h2 := occ_succ (2 * m + 1)
    have h3 := ch_succ m
    have e0 : tm (2 * m) = tm m := tm_even m
    have e1 : tm (2 * m + 1) = 1 - tm m := tm_odd m
    have e2 : tm (2 * m + 2) = tm (m + 1) := by
      rw [show 2 * m + 2 = 2 * (m + 1) by ring, tm_even]
    have e3 : tm (2 * m + 1 + 1) = tm (m + 1) := e2
    have e4 : tm (2 * m + 1 + 2) = 1 - tm (m + 1) := by
      rw [show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring, tm_odd]
    have e5 : occ (2 * (m + 1)) = occ (2 * m + 1 + 1) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    have := tm_le m
    have := tm_le (m + 1)
    rw [e5]
    split_ifs at h1 h2 h3 <;> omega

/-- 010 does not overlap itself in t: 01010 would put three equal letters in a row in x. -/
lemma no_overlap (p : ℕ) (h : tm p = 0 ∧ tm (p + 1) = 1 ∧ tm (p + 2) = 0) :
    ¬ (tm (p + 2) = 0 ∧ tm (p + 3) = 1 ∧ tm (p + 4) = 0) := by
  obtain ⟨i, rfl | rfl⟩ : ∃ i, p = 2 * i ∨ p = 2 * i + 1 := ⟨p / 2, by omega⟩
  · have e0 : tm (2 * i) = tm i := tm_even i
    have e2 : tm (2 * i + 2) = tm (i + 1) := by
      rw [show 2 * i + 2 = 2 * (i + 1) by ring, tm_even]
    have e4 : tm (2 * i + 4) = tm (i + 2) := by
      rw [show 2 * i + 4 = 2 * (i + 2) by ring, tm_even]
    have h3 := no_three i
    omega
  · have e1 : tm (2 * i + 1) = 1 - tm i := tm_odd i
    have e3 : tm (2 * i + 1 + 2) = 1 - tm (i + 1) := by
      rw [show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring, tm_odd]
    have e5 : tm (2 * i + 1 + 4) = 1 - tm (i + 2) := by
      rw [show 2 * i + 1 + 4 = 2 * (i + 2) + 1 by ring, tm_odd]
    have h3 := no_three i
    have := tm_le i
    have := tm_le (i + 1)
    have := tm_le (i + 2)
    omega

lemma occ_add_three (p : ℕ) (h : tm p = 0 ∧ tm (p + 1) = 1 ∧ tm (p + 2) = 0) :
    occ (p + 3) = occ p + 1 := by
  have hno := no_overlap p h
  have h1 := occ_succ p
  have h2 := occ_succ (p + 1)
  have h3 := occ_succ (p + 2)
  have e1 : occ (p + 1 + 1) = occ (p + 2) := rfl
  have e2 : occ (p + 2 + 1) = occ (p + 3) := rfl
  have t1 : tm (p + 1 + 1) = tm (p + 2) := rfl
  have t2 : tm (p + 1 + 2) = tm (p + 3) := rfl
  have t3 : tm (p + 2 + 1) = tm (p + 3) := rfl
  have t4 : tm (p + 2 + 2) = tm (p + 4) := rfl
  split_ifs at h1 h2 h3 <;> omega

lemma ones_add_three (p : ℕ) (h : tm p = 0 ∧ tm (p + 1) = 1 ∧ tm (p + 2) = 0) :
    ones (p + 3) = ones p + 1 := by
  have h1 := ones_succ p
  have h2 := ones_succ (p + 1)
  have h3 := ones_succ (p + 2)
  have e1 : ones (p + 1 + 1) = ones (p + 2) := rfl
  have e2 : ones (p + 2 + 1) = ones (p + 3) := rfl
  split_ifs at h1 h2 h3 <;> omega

/-! ### The scan -/

lemma pos_succ (k : ℕ) : pos (k + 1) =
    if tm (pos k) = 0 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0 then pos k + 3 else pos k + 1 :=
  rfl

/-- Z(k): the number of letters 1 among the first k output letters. -/
noncomputable def Z (k : ℕ) : ℕ := Nat.count (fun j => w j = 1) k

lemma Z_succ (k : ℕ) : Z (k + 1) = Z k + if w k = 1 then 1 else 0 := by
  unfold Z
  rw [Nat.count_succ]

/-- The scan invariant: the first k output letters contain as many letters 1 as t below pos k,
and every 010 below pos k was replaced. -/
lemma inv (k : ℕ) : Z k = ones (pos k) ∧ k + 2 * occ (pos k) = pos k := by
  induction k with
  | zero => simp [Z, ones, occ, pos]
  | succ k ih =>
    obtain ⟨hz, hk⟩ := ih
    by_cases hm : tm (pos k) = 0 ∧ tm (pos k + 1) = 1 ∧ tm (pos k + 2) = 0
    · have hp : pos (k + 1) = pos k + 3 := by rw [pos_succ, if_pos hm]
      have hw : w k = 1 := by unfold w; rw [if_pos hm]
      rw [hp, Z_succ, hw, occ_add_three _ hm, ones_add_three _ hm]
      split_ifs <;> omega
    · have hp : pos (k + 1) = pos k + 1 := by rw [pos_succ, if_neg hm]
      have hw : w k = tm (pos k) := by unfold w; rw [if_neg hm]
      rw [hp, Z_succ, hw, occ_succ, if_neg hm, ones_succ]
      split_ifs <;> omega

lemma ones_infinite : (setOf (fun k => w k = 1)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hconst : ∀ j, Z (B + 1 + j) = Z (B + 1) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have hno : ¬ w (B + 1 + j) = 1 := fun h => by
        have := hB h
        omega
      rw [show B + 1 + (j + 1) = B + 1 + j + 1 by ring, Z_succ, if_neg hno, ih, add_zero]
  have hZ := hconst (2 * Z (B + 1) + 3)
  obtain ⟨hz, hk⟩ := inv (B + 1 + (2 * Z (B + 1) + 3))
  have hb := ones_bound (pos (B + 1 + (2 * Z (B + 1) + 3)))
  omega

/-- |3 a(n) - 4 n| <= 2 log2(8n + 8) + 10. -/
lemma a_bound {n : ℕ} (hn : 1 ≤ n) :
    |3 * (a n : ℝ) - 4 * n| ≤ 2 * Real.logb 2 (8 * n + 8) + 10 := by
  set k := Nat.nth (fun k => w k = 1) (n - 1) with hk
  have hZ : Z k = n - 1 := Nat.count_nth_of_infinite ones_infinite (n - 1)
  obtain ⟨hz, hkk⟩ := inv k
  have ha : a n = k + 1 := rfl
  have hpk : pos k ≤ 2 * n := by
    have := ones_bound (pos k)
    omega
  have hint : |3 * ((k : ℤ) + 1) - 4 * n| ≤ 2 * Nat.log 2 (8 * n + 8) + 10 := by
    have h1 := occ_two_mul (pos k / 2)
    have hE := E_bound (pos k / 2)
    have hlog : Nat.log 2 (pos k / 2) ≤ Nat.log 2 (8 * n + 8) := Nat.log_mono_right (by omega)
    unfold E at hE
    rw [abs_le] at hE ⊢
    obtain ⟨m, hm | hm⟩ : ∃ m, pos k = 2 * m ∨ pos k = 2 * m + 1 := ⟨pos k / 2, by omega⟩
    · rw [hm, ones_two_mul] at hz
      rw [hm] at hkk h1 hE hlog
      rw [show 2 * m / 2 = m by omega] at h1 hE hlog
      constructor <;> omega
    · rw [hm, ones_succ, ones_two_mul] at hz
      rw [hm, occ_succ] at hkk
      rw [hm, show (2 * m + 1) / 2 = m by omega] at h1 hE hlog
      split_ifs at hz hkk <;> constructor <;> omega
  have hlog : (Nat.log 2 (8 * n + 8) : ℝ) ≤ Real.logb 2 (8 * n + 8) := by
    calc (Nat.log 2 (8 * n + 8) : ℝ) ≤ Real.logb 2 ((8 * n + 8 : ℕ) : ℝ) :=
          Real.natLog_le_logb _ _
      _ = Real.logb 2 (8 * n + 8) := by push_cast; ring
  rw [abs_le] at hint
  have h1a : -(2 * (Nat.log 2 (8 * n + 8) : ℝ) + 10) ≤ 3 * ((k : ℝ) + 1) - 4 * (n : ℝ) := by
    exact_mod_cast hint.1
  have h1b : 3 * ((k : ℝ) + 1) - 4 * (n : ℝ) ≤ 2 * (Nat.log 2 (8 * n + 8) : ℝ) + 10 := by
    exact_mod_cast hint.2
  rw [abs_le, ha]
  push_cast
  constructor <;> linarith

/-- Kimberling's conjecture: a(n)/n -> 4/3. -/
theorem conjecture : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (4 / 3)) :=
  lim_of_bound (f := a) (p := 4) (q := 3) (K := 2) (C := 10) (by norm_num) fun n hn => a_bound hn

end OMA.S_oeis_a286057

theorem OMA.solution : type_of% @OMA.S_oeis_a286057.main :=
  OMA.S_oeis_a286057.conjecture
