import OMAStatements.S_oeis_a286401

namespace OMA.S_oeis_a286401

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

/-! ### Letter changes and factors of length 2 -/

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

/-- The number of j < n with t(j) t(j+1) = 01. -/
def c01 (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, if tm j = 0 ∧ tm (j + 1) = 1 then 1 else 0

lemma c01_succ (n : ℕ) : c01 (n + 1) = c01 n + if tm n = 0 ∧ tm (n + 1) = 1 then 1 else 0 :=
  Finset.sum_range_succ _ _

/-- The number of j < n with t(j) t(j+1) = 10. -/
def c10 (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, if tm j = 1 ∧ tm (j + 1) = 0 then 1 else 0

lemma c10_succ (n : ℕ) : c10 (n + 1) = c10 n + if tm n = 1 ∧ tm (n + 1) = 0 then 1 else 0 :=
  Finset.sum_range_succ _ _

lemma two_c01 (n : ℕ) : 2 * c01 n = ch n + tm n := by
  induction n with
  | zero => simp [c01, ch, tm]
  | succ n ih =>
    rw [c01_succ, ch_succ]
    have := tm_le n
    have := tm_le (n + 1)
    split_ifs <;> omega

lemma c01_add_c10 (n : ℕ) : c01 n + c10 n = ch n := by
  induction n with
  | zero => simp [c01, c10, ch]
  | succ n ih =>
    rw [c01_succ, c10_succ, ch_succ]
    have := tm_le n
    have := tm_le (n + 1)
    split_ifs <;> omega

lemma c01_bound (m : ℕ) : |6 * (c01 m : ℤ) - 2 * m| ≤ Nat.log 2 m + 4 := by
  have h2 := two_c01 m
  have hE := E_bound m
  have := tm_le m
  unfold E at hE
  rw [abs_le] at hE ⊢
  push_cast at h2
  constructor <;> omega

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

/-! ### Occurrences of 11 in x -/

/-- The number of j < n with x_j x_{j+1} = 11. -/
def occ (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, if tm j = 1 ∧ tm (j + 1) = 1 then 1 else 0

lemma occ_succ (n : ℕ) :
    occ (n + 1) = occ n + if tm n = 1 ∧ tm (n + 1) = 1 then 1 else 0 :=
  Finset.sum_range_succ _ _

/-- The number of zeros of x below n. -/
def zx (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, if tm j = 0 then 1 else 0

lemma zx_succ (n : ℕ) : zx (n + 1) = zx n + if tm n = 0 then 1 else 0 :=
  Finset.sum_range_succ _ _

lemma zx_two_mul (m : ℕ) : zx (2 * m) = m := by
  induction m with
  | zero => simp [zx]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, zx_succ, zx_succ, ih, tm_even, tm_odd]
    have := tm_le m
    split_ifs <;> omega

lemma zx_bound (n : ℕ) : n ≤ 2 * zx n + 1 ∧ 2 * zx n ≤ n + 1 := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
  · rw [zx_two_mul]; omega
  · rw [zx_succ, zx_two_mul]; split_ifs <;> omega

lemma occ_rel (n : ℕ) : occ n + c10 n + zx n = n := by
  induction n with
  | zero => simp [occ, c10, zx]
  | succ n ih =>
    rw [occ_succ, c10_succ, zx_succ]
    have := tm_le n
    have := tm_le (n + 1)
    split_ifs <;> omega

/-- |6 occ(i) - i| <= 3 log2 i + 12 and 2 occ(i) <= i + 2. -/
lemma occ_bound (i : ℕ) : |6 * (occ i : ℤ) - i| ≤ 3 * Nat.log 2 i + 12 ∧ 2 * occ i ≤ i + 2 := by
  have h1 := c01_bound i
  have h2 := c01_add_c10 i
  have h3 := occ_rel i
  have h4 := zx_bound i
  have hE := E_bound i
  have := ch_le i
  unfold E at hE
  rw [abs_le] at hE h1 ⊢
  push_cast at h2 h3
  refine ⟨⟨by omega, by omega⟩, by omega⟩

/-! ### The scan -/

lemma no_three (i : ℕ) : ¬ (tm i = tm (i + 1) ∧ tm (i + 1) = tm (i + 2)) := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, i = 2 * m ∨ i = 2 * m + 1 := ⟨i / 2, by omega⟩
  · rw [tm_even m, tm_odd m]
    have := tm_le m
    omega
  · rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, tm_even (m + 1),
      show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring, tm_odd (m + 1)]
    have := tm_le (m + 1)
    omega

lemma match_even (i : ℕ) :
    (tm (2 * i) = 1 ∧ tm (2 * i + 1) = 0 ∧ tm (2 * i + 2) = 1 ∧
      tm (2 * i + 3) = 0) ↔ (tm i = 1 ∧ tm (i + 1) = 1) := by
  rw [tm_even, tm_odd, show 2 * i + 2 = 2 * (i + 1) by ring, tm_even,
    show 2 * i + 3 = 2 * (i + 1) + 1 by ring, tm_odd]
  have := tm_le i
  have := tm_le (i + 1)
  omega

lemma no_match_odd (i : ℕ) :
    ¬ (tm (2 * i + 1) = 1 ∧ tm (2 * i + 1 + 1) = 0 ∧ tm (2 * i + 1 + 2) = 1 ∧
      tm (2 * i + 1 + 3) = 0) := by
  have h3 := no_three i
  rw [tm_odd, show 2 * i + 1 + 1 = 2 * (i + 1) by ring, tm_even,
    show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring, tm_odd,
    show 2 * i + 1 + 3 = 2 * (i + 2) by ring, tm_even]
  have := tm_le i
  have := tm_le (i + 1)
  have := tm_le (i + 2)
  omega

lemma pos_succ (k : ℕ) : pos (k + 1) =
    if tm (pos k) = 1 ∧ tm (pos k + 1) = 0 ∧ tm (pos k + 2) = 1 ∧ tm (pos k + 3) = 0
      then pos k + 4 else pos k + 1 := rfl

lemma no_double (i : ℕ) (hQ : tm i = 1 ∧ tm (i + 1) = 1) :
    ¬ (tm (i + 1) = 1 ∧ tm (i + 1 + 1) = 1) := by
  have h3 := no_three i
  rw [show i + 1 + 1 = i + 2 by ring]
  omega

/-- Z(k): the number of letters 0 among the first k output letters. -/
noncomputable def Z (k : ℕ) : ℕ := Nat.count (fun j => w j = 0) k

lemma Z_succ (k : ℕ) : Z (k + 1) = Z k + if w k = 0 then 1 else 0 := by
  unfold Z
  rw [Nat.count_succ]

lemma ind_le (n : ℕ) : (if tm n = 0 then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega

/-- The scan invariant. -/
lemma inv (k : ℕ) : ∃ i,
    (pos k = 2 * i ∧ (k : ℤ) = 2 * i - 3 * occ i ∧ (Z k : ℤ) = i - 2 * occ i) ∨
    (pos k = 2 * i + 1 ∧ ¬ (tm i = 1 ∧ tm (i + 1) = 1) ∧
      (k : ℤ) = 2 * i + 1 - 3 * occ i ∧
      (Z k : ℤ) = i + ((if tm i = 0 then 1 else 0 : ℕ) : ℤ) - 2 * occ i) := by
  induction k with
  | zero => exact ⟨0, Or.inl ⟨rfl, by simp [occ], by simp [Z, occ]⟩⟩
  | succ k ih =>
    obtain ⟨i, ⟨hp, hk, hz⟩ | ⟨hp, hno, hk, hz⟩⟩ := ih
    · by_cases hQ : tm i = 1 ∧ tm (i + 1) = 1
      · have hm : tm (pos k) = 1 ∧ tm (pos k + 1) = 0 ∧ tm (pos k + 2) = 1 ∧ tm (pos k + 3) = 0 := by rw [hp]; exact (match_even i).mpr hQ
        have hc : occ (i + 2) = occ i + 1 := by
          rw [occ_succ, occ_succ, if_pos hQ, if_neg (no_double i hQ)]
        refine ⟨i + 2, Or.inl ⟨?_, ?_, ?_⟩⟩
        · rw [pos_succ, if_pos hm, hp]; ring
        · rw [hc]; push_cast; linarith
        · have hw : w k = 1 := by unfold w; rw [if_pos hm]
          rw [Z_succ, hw, hc]
          norm_num <;> linarith
      · have hm : ¬ (tm (pos k) = 1 ∧ tm (pos k + 1) = 0 ∧ tm (pos k + 2) = 1 ∧ tm (pos k + 3) = 0) := by rw [hp]; exact fun h => hQ ((match_even i).mp h)
        refine ⟨i, Or.inr ⟨?_, hQ, ?_, ?_⟩⟩
        · rw [pos_succ, if_neg hm, hp]
        · push_cast; linarith
        · have hw : w k = tm i := by unfold w; rw [if_neg hm, hp, tm_even]
          rw [Z_succ, hw]
          push_cast
          linarith
    · have hm : ¬ (tm (pos k) = 1 ∧ tm (pos k + 1) = 0 ∧ tm (pos k + 2) = 1 ∧ tm (pos k + 3) = 0) := by rw [hp]; exact no_match_odd i
      have hc : occ (i + 1) = occ i := by rw [occ_succ, if_neg hno, add_zero]
      refine ⟨i + 1, Or.inl ⟨?_, ?_, ?_⟩⟩
      · rw [pos_succ, if_neg hm, hp]; ring
      · rw [hc]; push_cast; linarith
      · have hw : w k = 1 - tm i := by unfold w; rw [if_neg hm, hp, tm_odd]
        rw [Z_succ, hw, hc]
        have := tm_le i
        rcases (show tm i = 0 ∨ tm i = 1 by omega) with h | h <;> rw [h] at hz ⊢ <;>
          norm_num at hz ⊢ <;> linarith

/-- |9 Z(k) - 4 k| <= 9 log2(2k + 8) + 45. -/
lemma Z_bound (k : ℕ) : |9 * (Z k : ℤ) - 4 * k| ≤ 9 * Nat.log 2 (2 * k + 8) + 45 := by
  obtain ⟨i, ⟨hp, hk, hz⟩ | ⟨hp, hno, hk, hz⟩⟩ := inv k
  · obtain ⟨hb, h2⟩ := occ_bound i
    have hi : i ≤ 2 * k + 8 := by omega
    have hlog : Nat.log 2 i ≤ Nat.log 2 (2 * k + 8) := Nat.log_mono_right hi
    rw [abs_le] at hb ⊢
    constructor <;> omega
  · obtain ⟨hb, h2⟩ := occ_bound i
    have hi : i ≤ 2 * k + 8 := by omega
    have hlog : Nat.log 2 i ≤ Nat.log 2 (2 * k + 8) := Nat.log_mono_right hi
    have hind := ind_le i
    generalize (if tm i = 0 then 1 else 0 : ℕ) = e at hz hind
    rw [abs_le] at hb ⊢
    constructor <;> omega

/-! ### Gaps: a finite check over the factors of t -/

/-- The factor t[p, p+L). -/
def fac (p L : ℕ) : List ℕ := (List.range L).map (fun i => tm (p + i))

lemma fac_succ (p L : ℕ) : fac p (L + 1) = fac p L ++ [tm (p + L)] := by
  simp [fac, List.range_succ]

lemma fac_take (p L m : ℕ) (h : m ≤ L) : (fac p L).take m = fac p m := by
  apply List.ext_getElem
  · simp [fac, h]
  · intro j h1 h2
    simp [fac]

lemma fac_drop (p L m : ℕ) : (fac p L).drop m = fac (p + m) (L - m) := by
  apply List.ext_getElem
  · simp [fac]
  · intro j h1 h2
    simp [fac]
    ring_nf

/-- The Thue-Morse morphism applied to a word: x -> x(1-x). -/
def mu (g : List ℕ) : List ℕ := g.flatMap fun x => [x, 1 - x]

lemma mu_fac (q m : ℕ) : mu (fac q m) = fac (2 * q) (2 * m) := by
  induction m with
  | zero => simp [mu, fac]
  | succ m ih =>
    rw [fac_succ, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, fac_succ, fac_succ]
    unfold mu at ih ⊢
    rw [List.flatMap_append, ih]
    have e : tm (2 * q + 2 * m) = tm (q + m) := by
      rw [show 2 * q + 2 * m = 2 * (q + m) by ring, tm_even]
    have e' : tm (2 * q + (2 * m + 1)) = 1 - tm (q + m) := by
      rw [show 2 * q + (2 * m + 1) = 2 * (q + m) + 1 by ring, tm_odd]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
      List.singleton_append, e, e']

/-- A list containing every factor of length L of t (built from the factors of length
L/2 + 1 through the morphism). -/
def facts : ℕ → List (List ℕ)
  | 0 => [[]]
  | 1 => [[0], [1]]
  | 2 => [[0, 0], [0, 1], [1, 0], [1, 1]]
  | L + 3 => (facts ((L + 3) / 2 + 1)).flatMap
      fun g => [(mu g).take (L + 3), ((mu g).drop 1).take (L + 3)]
termination_by L => L
decreasing_by omega

lemma fac_mem : ∀ L p, fac p L ∈ facts L := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro p
    match L, ih with
    | 0, _ => simp [fac, facts]
    | 1, _ =>
      have := tm_le p
      simp [fac, facts]
      omega
    | 2, _ =>
      have h1 := tm_le p
      have h2 := tm_le (p + 1)
      have e : fac p 2 = [tm p, tm (p + 1)] := by simp [fac, List.range_succ]
      rw [e]
      simp only [facts]
      rcases (show tm p = 0 ∨ tm p = 1 by omega) with h | h <;>
        rcases (show tm (p + 1) = 0 ∨ tm (p + 1) = 1 by omega) with h' | h' <;> simp [h, h']
    | L + 3, ih =>
      rw [facts, List.mem_flatMap]
      refine ⟨fac (p / 2) ((L + 3) / 2 + 1), ih _ (by omega) _, ?_⟩
      rw [mu_fac]
      rcases Nat.mod_two_eq_zero_or_one p with hp | hp
      · have : p = 2 * (p / 2) := by omega
        rw [List.mem_cons]
        left
        rw [fac_take _ _ _ (by omega), ← this]
      · have : p = 2 * (p / 2) + 1 := by omega
        rw [List.mem_cons, List.mem_singleton]
        right
        rw [fac_drop, fac_take _ _ _ (by omega), ← this]

/-- The scan on a finite word, producing r output letters. -/
def run : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | r + 1, l => if l.take 4 = [1, 0, 1, 0] then 1 :: run r (l.drop 4)
      else l.headD 0 :: run r l.tail

lemma match_iff (p : ℕ) :
    (tm p = 1 ∧ tm (p + 1) = 0 ∧ tm (p + 2) = 1 ∧ tm (p + 3) = 0) ↔
      fac p 4 = [1, 0, 1, 0] := by
  simp [fac, List.range_succ]

lemma run_eq : ∀ r k L, 4 * r ≤ L →
    run r (fac (pos k) L) = (List.range r).map (fun j => w (k + j)) := by
  intro r
  induction r with
  | zero => intro k L _; rfl
  | succ r ih =>
    intro k L hL
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, run]
    have htake : (fac (pos k) L).take 4 = fac (pos k) 4 := fac_take _ _ _ (by omega)
    rw [htake]
    by_cases hm : tm (pos k) = 1 ∧ tm (pos k + 1) = 0 ∧ tm (pos k + 2) = 1 ∧ tm (pos k + 3) = 0
    · rw [if_pos ((match_iff _).mp hm)]
      have hw : w k = 1 := by unfold w; rw [if_pos hm]
      have hp : pos (k + 1) = pos k + 4 := by rw [pos_succ, if_pos hm]
      rw [add_zero, hw, fac_drop, ← hp, ih (k + 1) (L - 4) (by omega)]
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp, Nat.succ_eq_add_one]
      congr 1
      ring
    · rw [if_neg (fun h => hm ((match_iff _).mpr h))]
      have hw : w k = tm (pos k) := by unfold w; rw [if_neg hm]
      have hp : pos (k + 1) = pos k + 1 := by rw [pos_succ, if_neg hm]
      have hhead : (fac (pos k) L).headD 0 = tm (pos k) := by
        obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
        simp [fac, List.range_succ_eq_map]
      have htail : (fac (pos k) L).tail = fac (pos k + 1) (L - 1) := by
        rw [← List.drop_one, fac_drop]
      rw [add_zero, hw, hhead, htail, ← hp, ih (k + 1) (L - 1) (by omega)]
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp, Nat.succ_eq_add_one]
      congr 1
      ring

lemma gap_check : ∀ f ∈ facts 16, (run 4 f).getD 0 9 = 0 →
    ((run 4 f).getD 1 9 = 0 ∨ (run 4 f).getD 2 9 = 0 ∨ (run 4 f).getD 3 9 = 0) := by
  decide +kernel

lemma gap (k : ℕ) (hk : w k = 0) : ∃ d, 1 ≤ d ∧ d ≤ 3 ∧ w (k + d) = 0 := by
  have h := gap_check (fac (pos k) 16) (fac_mem 16 (pos k))
  rw [run_eq 4 k 16 (by norm_num)] at h
  simp at h
  rcases h hk with h | h | h
  · exact ⟨1, by norm_num, by norm_num, h⟩
  · exact ⟨2, by norm_num, by norm_num, h⟩
  · exact ⟨3, by norm_num, by norm_num, h⟩

lemma first_letter : w 0 = 0 := by decide

lemma zeros_infinite : (setOf (fun k => w k = 0)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hall : ∀ m, ∃ k, m ≤ k ∧ w k = 0 := by
    intro m
    induction m with
    | zero => exact ⟨0, by norm_num, first_letter⟩
    | succ m ih =>
      obtain ⟨k, hk1, hk2⟩ := ih
      obtain ⟨d, hd1, -, hd⟩ := gap k hk2
      exact ⟨k + d, by omega, hd⟩
  obtain ⟨k, hk1, hk2⟩ := hall (B + 1)
  have := hB hk2
  omega

lemma next_lt (k1 : ℕ) (hp1 : w k1 = 0) {m : ℕ}
    (hc1 : Nat.count (fun k => w k = 0) k1 = m) :
    Nat.nth (fun k => w k = 0) (m + 1) < k1 + 4 := by
  obtain ⟨d, hd1, hd2, hpd⟩ := gap k1 hp1
  apply Nat.nth_lt_of_lt_count
  have e1 : Nat.count (fun k => w k = 0) (k1 + 1) = m + 1 := by
    rw [Nat.count_succ, hc1, if_pos hp1]
  have e2 : Nat.count (fun k => w k = 0) (k1 + d + 1) =
      Nat.count (fun k => w k = 0) (k1 + d) + 1 := by
    rw [Nat.count_succ, if_pos hpd]
  have e3 := Nat.count_monotone (fun k => w k = 0) (show k1 + 1 ≤ k1 + d by omega)
  have e4 := Nat.count_monotone (fun k => w k = 0) (show k1 + d + 1 ≤ k1 + 4 by omega)
  omega

lemma nth_le (m : ℕ) : Nat.nth (fun k => w k = 0) m ≤ 0 + 3 * m := by
  induction m with
  | zero =>
    rw [Nat.nth_zero]
    exact Nat.sInf_le first_letter
  | succ m ih =>
    have hp1 := Nat.nth_mem_of_infinite zeros_infinite m
    have hc1 := Nat.count_nth_of_infinite zeros_infinite m
    have := next_lt _ hp1 hc1
    omega

lemma a_bound {n : ℕ} (hn : 1 ≤ n) :
    |4 * (a n : ℝ) - 9 * n| ≤ 9 * Real.logb 2 (8 * n + 8) + 63 := by
  set k := Nat.nth (fun k => w k = 0) (n - 1) with hk
  have hZ : Z k = n - 1 := Nat.count_nth_of_infinite zeros_infinite (n - 1)
  have h1 := Z_bound k
  rw [hZ] at h1
  have ha : a n = k + 1 := rfl
  have hk2 : k ≤ 6 * n := by have := nth_le (n - 1); omega
  have hlog : (Nat.log 2 (2 * k + 8) : ℝ) ≤ Real.logb 2 (8 * n + 8) + 1 := by
    calc (Nat.log 2 (2 * k + 8) : ℝ) ≤ Real.logb 2 ((2 * k + 8 : ℕ) : ℝ) :=
          Real.natLog_le_logb _ _
      _ ≤ Real.logb 2 (2 * (8 * n + 8)) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
        have : (2 * k + 8 : ℕ) ≤ 2 * (8 * n + 8) := by omega
        exact_mod_cast this
      _ = Real.logb 2 (8 * n + 8) + 1 := by
        rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
        ring
  rw [abs_le] at h1
  have hn1 : ((n - 1 : ℕ) : ℤ) = n - 1 := by omega
  rw [hn1] at h1
  rw [abs_le, ha]
  push_cast
  have h1a : (9 * ((n : ℤ) - 1) - 4 * k : ℝ) ≥ -(9 * Nat.log 2 (2 * k + 8) + 45 : ℝ) := by
    exact_mod_cast h1.1
  have h1b : (9 * ((n : ℤ) - 1) - 4 * k : ℝ) ≤ (9 * Nat.log 2 (2 * k + 8) + 45 : ℝ) := by
    exact_mod_cast h1.2
  push_cast at h1a h1b
  constructor <;> linarith

/-- Kimberling's statements: the gaps and the limit. -/
theorem conjecture : (∀ n : ℕ, 2 ≤ n → a n - a (n - 1) = 1 ∨ a n - a (n - 1) = 2 ∨ a n - a (n - 1) = 3) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (9 / 4)) := by
  refine ⟨fun n hn => ?_, ?_⟩
  · classical
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    set p := fun k => w k = 0 with hpdef
    have hinf := zeros_infinite
    set k1 := Nat.nth p m with hk1
    set k2 := Nat.nth p (m + 1) with hk2def
    have hp1 : p k1 := Nat.nth_mem_of_infinite hinf m
    have hc1 : Nat.count p k1 = m := Nat.count_nth_of_infinite hinf m
    have hlt : k1 < k2 := Nat.nth_strictMono hinf (by omega)
    have ha1 : a (m + 2 - 1) = k1 + 1 := by
      show Nat.nth p (m + 2 - 1 - 1) + 1 = k1 + 1
      rw [show m + 2 - 1 - 1 = m by omega]
    have ha2 : a (m + 2) = k2 + 1 := by
      show Nat.nth p (m + 2 - 1) + 1 = k2 + 1
      rw [show m + 2 - 1 = m + 1 by omega]
    have hk2lt : k2 < k1 + 4 := next_lt k1 hp1 (m := m) hc1
    rw [ha1, ha2]
    omega
  · have := lim_of_bound (f := a) (p := 9) (q := 4) (K := 9) (C := 63) (by norm_num)
      fun n hn => a_bound hn
    rw [show ((9 : ℝ) / 4) = (9 / 4) by norm_num] at this
    exact this

end OMA.S_oeis_a286401

theorem OMA.solution : type_of% @OMA.S_oeis_a286401.main :=
  OMA.S_oeis_a286401.conjecture
