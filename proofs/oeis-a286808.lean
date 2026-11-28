import OMAStatements.S_oeis_a286808

namespace OMA.S_oeis_a286808

open Filter Topology





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

/-! ### The iterates -/

/-- alt(m) = (10)^m 1. -/
def alt : ℕ → List ℕ
  | 0 => [1]
  | m + 1 => 1 :: 0 :: alt m

lemma alt_head (m : ℕ) : ∃ r, alt m = 1 :: r := by
  cases m with
  | zero => exact ⟨[], rfl⟩
  | succ m => exact ⟨0 :: alt m, rfl⟩

lemma step_alt (m : ℕ) (v : List ℕ) : step (alt m ++ v) = alt (2 * m + 1) ++ step v := by
  induction m with
  | zero => rfl
  | succ m ih =>
    obtain ⟨r, hr⟩ := alt_head m
    have h1 : alt (m + 1) ++ v = 1 :: 0 :: 1 :: (r ++ v) := by
      rw [show alt (m + 1) = 1 :: 0 :: alt m from rfl, hr]
      rfl
    have h2 : step (1 :: 0 :: 1 :: (r ++ v)) = 1 :: 0 :: 1 :: 0 :: step (1 :: (r ++ v)) := rfl
    have h3 : alt m ++ v = 1 :: (r ++ v) := by rw [hr]; rfl
    rw [h1, h2, ← h3, ih, show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring]
    rfl

/-- The blocks alt(2^k - 1), alt(2^(k+1) - 1), ..., n of them, concatenated. -/
def C (k : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => alt (2 ^ k - 1) ++ C (k + 1) n

lemma step_C (k n : ℕ) : step (C k n) = C (k + 1) n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [show C k (n + 1) = alt (2 ^ k - 1) ++ C (k + 1) n from rfl, step_alt, ih,
      show C (k + 1) (n + 1) = alt (2 ^ (k + 1) - 1) ++ C (k + 1 + 1) n from rfl]
    have := Nat.one_le_two_pow (n := k)
    have h : 2 * (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by
      rw [pow_succ]
      omega
    rw [h]

lemma iter_eq (n : ℕ) : iter n = [0, 0] ++ C 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show iter (n + 1) = step (iter n) from rfl, ih]
    show 0 :: 0 :: 1 :: step (C 0 n) = [0, 0] ++ C 0 (n + 1)
    rw [step_C]
    rfl

lemma alt_length (m : ℕ) : (alt m).length = 2 * m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show alt (m + 1) = 1 :: 0 :: alt m from rfl, List.length_cons, List.length_cons, ih]
    ring

lemma C_length (k n : ℕ) : (C k n).length + n + 2 ^ (k + 1) = 2 ^ (k + n + 1) := by
  induction n generalizing k with
  | zero => simp [C]
  | succ n ih =>
    have h := ih (k + 1)
    have h1 : (C k (n + 1)).length = 2 * (2 ^ k - 1) + 1 + (C (k + 1) n).length := by
      rw [show C k (n + 1) = alt (2 ^ k - 1) ++ C (k + 1) n from rfl, List.length_append,
        alt_length]
    have h2 := Nat.one_le_two_pow (n := k)
    have e1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have e2 : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by ring
    have e3 : 2 ^ (k + (n + 1) + 1) = 2 ^ (k + 1 + n + 1) := by ring_nf
    omega

lemma iter_length (n : ℕ) : (iter n).length + n = 2 ^ (n + 1) := by
  have h := C_length 0 n
  rw [iter_eq, List.length_append]
  simp only [List.length_cons, List.length_nil, zero_add] at h ⊢
  omega

lemma lt_iter_length (i : ℕ) : i < (iter (i + 1)).length := by
  have h1 := iter_length (i + 1)
  have h2 : i < 2 ^ i := Nat.lt_two_pow_self
  have h3 : 2 ^ (i + 1 + 1) = 4 * 2 ^ i := by ring
  omega

lemma C_prefix (k n : ℕ) : C k n <+: C k (n + 1) := by
  induction n generalizing k with
  | zero => exact List.nil_prefix
  | succ n ih =>
    show alt (2 ^ k - 1) ++ C (k + 1) n <+: alt (2 ^ k - 1) ++ C (k + 1) (n + 1)
    exact (List.prefix_append_right_inj _).mpr (ih (k + 1))

/-- Each iterate is a prefix of the later ones. -/
lemma iter_prefix {m n : ℕ} (h : m ≤ n) : iter m <+: iter n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih =>
    refine ih.trans ?_
    rw [iter_eq, iter_eq]
    exact (List.prefix_append_right_inj _).mpr (C_prefix 0 n)

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

lemma W_eq (n i : ℕ) (hi : i < (iter n).length) : W i = (iter n).getD i 0 := by
  unfold W
  rcases le_total (i + 1) n with h | h
  · exact getD_prefix (iter_prefix h) (lt_iter_length i)
  · exact (getD_prefix (iter_prefix h) hi).symm

/-! ### Counting letters 0 -/

/-- Z(N): the number of letters 0 among the first N letters of W. -/
noncomputable def Z (N : ℕ) : ℕ := Nat.count (fun i => W i = 0) N

lemma Z_succ (N : ℕ) : Z (N + 1) = Z N + if W N = 0 then 1 else 0 := Nat.count_succ _ _

lemma Z_eq (n N : ℕ) (hN : N ≤ (iter n).length) : Z N = ((iter n).take N).count 0 := by
  induction N with
  | zero => simp [Z]
  | succ N ih =>
    have hN' : N < (iter n).length := by omega
    have hW : W N = (iter n)[N] := by rw [W_eq n N hN', List.getD_eq_getElem _ _ hN']
    rw [Z_succ, ih (by omega), List.take_add_one, List.getElem?_eq_getElem hN', List.count_append,
      hW]
    simp [List.count_singleton]

/-- The excess of the length of L over twice its number of letters 0. -/
def dl (L : List ℕ) : ℤ := (L.length : ℤ) - 2 * (L.count 0 : ℤ)

lemma dl_append (l₁ l₂ : List ℕ) : dl (l₁ ++ l₂) = dl l₁ + dl l₂ := by
  simp only [dl, List.length_append, List.count_append]
  push_cast
  ring

lemma dl_cons_one (l : List ℕ) : dl (1 :: l) = dl l + 1 := by
  rw [show 1 :: l = [1] ++ l from rfl, dl_append]
  norm_num [dl]
  ring

lemma dl_cons_zero (l : List ℕ) : dl (0 :: l) = dl l - 1 := by
  rw [show 0 :: l = [0] ++ l from rfl, dl_append]
  norm_num [dl]
  ring

lemma alt_dl (m : ℕ) : dl (alt m) = 1 := by
  induction m with
  | zero => norm_num [dl, alt]
  | succ m ih =>
    rw [show alt (m + 1) = 1 :: 0 :: alt m from rfl, dl_cons_one, dl_cons_zero, ih]
    ring

lemma alt_take (m t : ℕ) (ht : t ≤ 2 * m + 1) :
    0 ≤ dl ((alt m).take t) ∧ dl ((alt m).take t) ≤ 1 := by
  induction m generalizing t with
  | zero =>
    interval_cases t <;> norm_num [dl, alt]
  | succ m ih =>
    rcases t with _ | _ | t
    · norm_num [dl]
    · norm_num [dl, alt]
    · have h := ih t (by omega)
      have e : (alt (m + 1)).take (t + 1 + 1) = 1 :: 0 :: (alt m).take t := rfl
      rw [e, dl_cons_one, dl_cons_zero]
      constructor <;> linarith [h.1, h.2]

lemma C_take (k n t : ℕ) (ht : t ≤ (C k n).length) :
    0 ≤ dl ((C k n).take t) ∧ dl ((C k n).take t) ≤ n := by
  induction n generalizing k t with
  | zero => simp [C, dl]
  | succ n ih =>
    have e : C k (n + 1) = alt (2 ^ k - 1) ++ C (k + 1) n := rfl
    rw [e, List.length_append] at ht
    rw [e, List.take_append, dl_append]
    rcases le_or_gt t (alt (2 ^ k - 1)).length with h | h
    · rw [Nat.sub_eq_zero_of_le h, List.take_zero]
      have := alt_take (2 ^ k - 1) t (by rw [alt_length] at h; exact h)
      have h0 : dl [] = 0 := by simp [dl]
      rw [h0]
      push_cast
      constructor <;> linarith [this.1, this.2]
    · rw [List.take_of_length_le h.le, alt_dl]
      have := ih (k + 1) (t - (alt (2 ^ k - 1)).length) (by omega)
      push_cast
      constructor <;> linarith [this.1, this.2]

/-- Over the first N letters of W, with N at most the length of iterate n. -/
lemma Z_bound_gen (n N : ℕ) (hN : N ≤ (iter n).length) :
    -2 ≤ (N : ℤ) - 2 * Z N ∧ (N : ℤ) - 2 * Z N ≤ n := by
  have hd : (N : ℤ) - 2 * Z N = dl ((iter n).take N) := by
    rw [dl, Z_eq n N hN, List.length_take, min_eq_left hN]
  have hlen : N - [0, 0].length ≤ (C 0 n).length := by
    rw [iter_eq, List.length_append] at hN
    omega
  rw [hd, iter_eq, List.take_append, dl_append]
  have hC := C_take 0 n _ hlen
  have h00 : -2 ≤ dl (List.take N [0, 0]) ∧ dl (List.take N [0, 0]) ≤ 0 := by
    rcases (show N = 0 ∨ N = 1 ∨ 2 ≤ N by omega) with h | h | h
    · subst h
      norm_num [dl]
    · subst h
      norm_num [dl]
    · rw [List.take_of_length_le (by simpa using h)]
      norm_num [dl]
  constructor <;> linarith [hC.1, hC.2, h00.1, h00.2]

lemma Z_bound (N : ℕ) : -2 ≤ (N : ℤ) - 2 * Z N ∧ (N : ℤ) - 2 * Z N ≤ Nat.log 2 N + 1 := by
  have hlen : N ≤ (iter (Nat.log 2 N + 1)).length := by
    have h1 := iter_length (Nat.log 2 N + 1)
    have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
    have h3 : 2 ^ (Nat.log 2 N + 1 + 1) = 2 * 2 ^ (Nat.log 2 N).succ := by
      rw [Nat.succ_eq_add_one]
      ring
    have h4 : Nat.log 2 N < 2 ^ Nat.log 2 N := Nat.lt_two_pow_self
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · omega
    · have h5 := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
      omega
  have h := Z_bound_gen (Nat.log 2 N + 1) N hlen
  push_cast at h
  exact h

lemma zeros_infinite : (setOf (fun i => W i = 0)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hconst : ∀ j, Z (B + 1 + j) = Z (B + 1) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have hno : ¬ W (B + 1 + j) = 0 := fun h => by
        have := hB h
        omega
      rw [show B + 1 + (j + 1) = B + 1 + j + 1 by ring, Z_succ, if_neg hno, ih, add_zero]
  set m := 2 * Z (B + 1) + B + 3 with hm
  have h1 := iter_length (m + 1)
  have h2 : m < 2 ^ m := Nat.lt_two_pow_self
  have h3 : 2 ^ (m + 1 + 1) = 4 * 2 ^ m := by ring
  have hb := Z_bound_gen (m + 1) (iter (m + 1)).length le_rfl
  have hc := hconst ((iter (m + 1)).length - (B + 1))
  rw [show B + 1 + ((iter (m + 1)).length - (B + 1)) = (iter (m + 1)).length by omega] at hc
  rw [hc] at hb
  push_cast at hb
  omega

/-! ### The bounds -/

lemma pow_bound (n : ℕ) (h : 5 ≤ n) : 3 * n - 1 < 2 ^ (n - 1) := by
  induction n, h using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show n + 1 - 1 = n - 1 + 1 by omega, pow_succ]
    omega

lemma a_lt (n : ℕ) (hn : 1 ≤ n) : a n < 3 * n := by
  have key : n ≤ Z (3 * n - 1) := by
    rcases (show n ≤ 4 ∨ 5 ≤ n by omega) with h | h
    · have hl : 3 * n - 1 ≤ (iter 4).length := by
        have := iter_length 4
        norm_num at this
        omega
      rw [Z_eq 4 _ hl]
      interval_cases n <;> decide
    · have hb := (Z_bound (3 * n - 1)).2
      have hlog : Nat.log 2 (3 * n - 1) < n - 1 :=
        Nat.log_lt_of_lt_pow (by omega) (pow_bound n h)
      omega
  have hlt : Nat.nth (fun i => W i = 0) (n - 1) < 3 * n - 1 :=
    Nat.nth_lt_of_lt_count (by unfold Z at key; omega)
  unfold a
  omega

/-- |a(n) - 2n| <= log2(8n + 8) + 2. -/
lemma a_bound {n : ℕ} (hn : 1 ≤ n) :
    |1 * (a n : ℝ) - 2 * n| ≤ 1 * Real.logb 2 (8 * n + 8) + 2 := by
  set p := Nat.nth (fun i => W i = 0) (n - 1) with hp
  have hZp : Z p = n - 1 := Nat.count_nth_of_infinite zeros_infinite (n - 1)
  have hWp : W p = 0 := Nat.nth_mem_of_infinite zeros_infinite (n - 1)
  have hZ1 : Z (p + 1) = n := by
    rw [Z_succ, if_pos hWp, hZp]
    omega
  have ha : a n = p + 1 := rfl
  have hlt := a_lt n hn
  have hb := Z_bound (p + 1)
  rw [hZ1] at hb
  have hlog : Nat.log 2 (p + 1) ≤ Nat.log 2 (8 * n + 8) := Nat.log_mono_right (by omega)
  have hint : |((p + 1 : ℕ) : ℤ) - 2 * n| ≤ Nat.log 2 (8 * n + 8) + 2 := by
    rw [abs_le]
    push_cast at hb ⊢
    constructor <;> omega
  have hlogR : (Nat.log 2 (8 * n + 8) : ℝ) ≤ Real.logb 2 (8 * n + 8) := by
    calc (Nat.log 2 (8 * n + 8) : ℝ) ≤ Real.logb 2 ((8 * n + 8 : ℕ) : ℝ) :=
          Real.natLog_le_logb _ _
      _ = Real.logb 2 (8 * n + 8) := by push_cast; ring
  rw [abs_le] at hint
  have h1a : -((Nat.log 2 (8 * n + 8) : ℝ) + 2) ≤ ((p : ℝ) + 1) - 2 * (n : ℝ) := by
    exact_mod_cast hint.1
  have h1b : ((p : ℝ) + 1) - 2 * (n : ℝ) ≤ (Nat.log 2 (8 * n + 8) : ℝ) + 2 := by
    exact_mod_cast hint.2
  rw [abs_le, ha]
  push_cast
  constructor <;> linarith

/-- Kimberling's conjecture: a(n)/n -> 2, and -1 < 2 - a(n)/n < 2 for n >= 1. -/
theorem conjecture : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 2) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < 2 - (a n : ℝ) / n ∧ 2 - (a n : ℝ) / n < 2 := by
  refine ⟨?_, fun n hn => ?_⟩
  · have := lim_of_bound (f := a) (p := 2) (q := 1) (K := 1) (C := 2) (by norm_num)
      fun n hn => a_bound hn
    rw [div_one] at this
    exact this
  · have hlt := a_lt n hn
    have hpos : 1 ≤ a n := by unfold a; omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hlt' : (a n : ℝ) < 3 * n := by exact_mod_cast hlt
    have hpos' : (1 : ℝ) ≤ a n := by exact_mod_cast hpos
    have h3 : (a n : ℝ) / n < 3 := by
      rw [div_lt_iff₀ hn']
      linarith
    have h0 : 0 < (a n : ℝ) / n := by positivity
    constructor <;> linarith

end OMA.S_oeis_a286808

theorem OMA.solution : type_of% @OMA.S_oeis_a286808.main :=
  OMA.S_oeis_a286808.conjecture
