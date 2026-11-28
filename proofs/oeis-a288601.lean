import OMAStatements.S_oeis_a288601

namespace OMA.S_oeis_a288601

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

/-! ### One pass -/

/-- Induction along the cases of `step`. -/
theorem step_rec {P : List ℕ → Prop} (h0 : P []) (hz : P [0]) (ho : P [1])
    (h00 : ∀ l, P l → P (0 :: 0 :: l)) (h10 : ∀ l, P l → P (1 :: 0 :: l))
    (h0y : ∀ y l, P ((y + 1) :: l) → P (0 :: (y + 1) :: l))
    (h1y : ∀ y l, P ((y + 1) :: l) → P (1 :: (y + 1) :: l))
    (hx : ∀ x l, P l → P ((x + 2) :: l)) : ∀ u, P u := by
  have key : ∀ n, ∀ u : List ℕ, u.length ≤ n → P u := by
    intro n
    induction n with
    | zero =>
      intro u hu
      cases u with
      | nil => exact h0
      | cons x l => simp at hu
    | succ n ih =>
      intro u hu
      rcases u with _ | ⟨x, l⟩
      · exact h0
      · simp only [List.length_cons] at hu
        rcases x with _ | _ | x
        · rcases l with _ | ⟨y, l⟩
          · exact hz
          · rcases y with _ | y
            · exact h00 l (ih l (by simp at hu; omega))
            · exact h0y y l (ih _ (by simpa using hu))
        · rcases l with _ | ⟨y, l⟩
          · exact ho
          · rcases y with _ | y
            · exact h10 l (ih l (by simp at hu; omega))
            · exact h1y y l (ih _ (by simpa using hu))
        · exact hx x l (ih l (by omega))
  exact fun u => key u.length u le_rfl

/-- A letter 1 is a cut point: no rule reads a 1 as its second letter. -/
lemma step_cut (u : List ℕ) : ∀ v, step (u ++ 1 :: v) = step u ++ step (1 :: v) := by
  refine step_rec (P := fun u => ∀ v, step (u ++ 1 :: v) = step u ++ step (1 :: v))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro v
    rfl
  · intro v
    rfl
  · intro v
    rfl
  · intro l ih v
    show 0 :: 1 :: 0 :: 1 :: step (l ++ 1 :: v) = 0 :: 1 :: 0 :: 1 :: step l ++ step (1 :: v)
    rw [ih]
    rfl
  · intro l ih v
    show 1 :: 0 :: 0 :: 1 :: step (l ++ 1 :: v) = 1 :: 0 :: 0 :: 1 :: step l ++ step (1 :: v)
    rw [ih]
    rfl
  · intro y l ih v
    show 0 :: step ((y + 1) :: l ++ 1 :: v) = 0 :: step ((y + 1) :: l) ++ step (1 :: v)
    rw [ih]
    rfl
  · intro y l ih v
    show 1 :: step ((y + 1) :: l ++ 1 :: v) = 1 :: step ((y + 1) :: l) ++ step (1 :: v)
    rw [ih]
    rfl
  · intro x l ih v
    show (x + 2) :: step (l ++ 1 :: v) = (x + 2) :: step l ++ step (1 :: v)
    rw [ih]
    rfl

lemma step_snoc_one (u : List ℕ) : step (u ++ [1]) = step u ++ [1] := by
  rw [step_cut u []]
  rfl

/-! ### The iterates without their last letter -/

/-- J n is iterate n + 1 without its final 1: J 0 = 010 and J (n+1) is the pass over J n. -/
def J : ℕ → List ℕ
  | 0 => [0, 1, 0]
  | n + 1 => step (J n)

/-- J n = 010 R n. -/
def R : ℕ → List ℕ
  | 0 => []
  | n + 1 => 0 :: 1 :: step (R n)

lemma iter_succ_eq (n : ℕ) : iter (n + 1) = J n ++ [1] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show iter (n + 1 + 1) = step (iter (n + 1)) from rfl, ih, step_snoc_one]
    rfl

lemma J_eq (n : ℕ) : J n = 0 :: 1 :: 0 :: R n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show J (n + 1) = step (J n) from rfl, ih]
    rfl

lemma J_struct (n : ℕ) :
    (∃ P, J (n + 1) = P ++ [1]) ∧ J (n + 2) = J (n + 1) ++ (0 :: R n ++ [1]) := by
  induction n with
  | zero => exact ⟨⟨[0, 1, 0, 0], rfl⟩, rfl⟩
  | succ n ih =>
    obtain ⟨⟨P, hP⟩, hC⟩ := ih
    show (∃ Q, J (n + 2) = Q ++ [1]) ∧ J (n + 3) = J (n + 2) ++ (0 :: R (n + 1) ++ [1])
    refine ⟨⟨J (n + 1) ++ 0 :: R n, by rw [hC, List.append_assoc]⟩, ?_⟩
    have hJ2 : J (n + 2) = step P ++ [1] := by
      rw [show J (n + 2) = step (J (n + 1)) from rfl, hP, step_snoc_one]
    have hsplit : J (n + 2) = P ++ 1 :: (0 :: R n ++ [1]) := by
      rw [hC, hP, List.append_assoc]
      rfl
    have e1 : step (J (n + 2)) = step P ++ step (1 :: (0 :: R n ++ [1])) := by
      rw [hsplit, step_cut]
    have e2 : step (1 :: (0 :: R n ++ [1])) = 1 :: 0 :: 0 :: 1 :: (step (R n) ++ [1]) := by
      show 1 :: 0 :: 0 :: 1 :: step (R n ++ [1]) = _
      rw [step_snoc_one]
    show step (J (n + 2)) = J (n + 2) ++ (0 :: R (n + 1) ++ [1])
    rw [e1, e2, hJ2]
    simp [R]

lemma R_struct (n : ℕ) : R (n + 2) = R (n + 1) ++ (0 :: R n ++ [1]) := by
  have h := (J_struct n).2
  rw [J_eq (n + 2), J_eq (n + 1)] at h
  simpa using h

lemma J_prefix_succ (n : ℕ) : J n <+: J (n + 1) := by
  cases n with
  | zero => exact ⟨[0, 1], rfl⟩
  | succ n => exact ⟨_, (J_struct n).2.symm⟩

/-- Each J n is a prefix of the later ones. -/
lemma J_prefix {m n : ℕ} (h : m ≤ n) : J m <+: J n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (J_prefix_succ n)

/-- Iterate n without its last letter is a prefix of iterate n + 1. -/
lemma iter_dropLast_prefix (n : ℕ) : (iter n).dropLast <+: iter (n + 1) := by
  cases n with
  | zero => exact ⟨[1, 0, 1], rfl⟩
  | succ n =>
    rw [iter_succ_eq n, iter_succ_eq (n + 1), List.dropLast_concat]
    exact (J_prefix_succ n).trans (List.prefix_append _ _)

lemma R_length (n : ℕ) : (R (n + 2)).length + 1 = (R (n + 1)).length + (R n).length + 3 := by
  rw [R_struct]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

lemma J_length_ge (n : ℕ) : n + 3 ≤ (J n).length := by
  have key : ∀ n, n ≤ (R n).length ∧ n + 1 ≤ (R (n + 1)).length := by
    intro n
    induction n with
    | zero => exact ⟨by simp, by simp [R]⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      show n + 2 ≤ (R (n + 2)).length
      have := R_length n
      have := ih.2
      omega
  rw [J_eq]
  simp only [List.length_cons]
  have := (key n).1
  omega

lemma J_length_pow (k : ℕ) : 2 ^ (k + 1) ≤ (R (2 * k)).length + 2 := by
  have mono : ∀ n, (R n).length ≤ (R (n + 1)).length := by
    intro n
    cases n with
    | zero =>
      show 0 ≤ (R 1).length
      exact Nat.zero_le _
    | succ n =>
      show (R (n + 1)).length ≤ (R (n + 2)).length
      have := R_length n
      omega
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := R_length (2 * k)
    have h2 := mono (2 * k)
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_succ]
    omega

/-! ### Counting letters 0 -/

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

lemma R_dl (n : ℕ) : dl (R n) = 0 ∧ dl (R (n + 1)) = 0 := by
  induction n with
  | zero => exact ⟨by simp [dl, R], by norm_num [dl, R, step]⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [R_struct, dl_append, dl_append, dl_cons_zero, ih.1, ih.2]
    norm_num [dl]

/-- Over every prefix of R n, the length minus twice the number of 0s lies in [-n, 0]. -/
lemma R_take (n : ℕ) : ∀ t, t ≤ (R n).length →
    -(n : ℤ) ≤ dl ((R n).take t) ∧ dl ((R n).take t) ≤ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t ht
    rcases n with _ | _ | n
    · simp [R] at ht
      subst ht
      simp [dl]
    · have hR : R 1 = [0, 1] := rfl
      rw [hR] at ht ⊢
      simp only [List.length_cons, List.length_nil] at ht
      interval_cases t <;> norm_num [dl]
    · rw [R_struct] at ht ⊢
      rw [List.take_append, dl_append]
      rcases le_or_gt t (R (n + 1)).length with h | h
      · rw [Nat.sub_eq_zero_of_le h, List.take_zero]
        have := ih (n + 1) (by omega) t h
        have h0 : dl [] = 0 := by simp [dl]
        rw [h0]
        push_cast at this ⊢
        constructor <;> linarith [this.1, this.2]
      · rw [List.take_of_length_le h.le, (R_dl (n + 1)).1]
        simp only [List.length_append, List.length_cons, List.length_nil] at ht
        obtain ⟨s, hs⟩ : ∃ s, t - (R (n + 1)).length = s + 1 := ⟨t - (R (n + 1)).length - 1,
          by omega⟩
        rw [hs]
        change -((n + 2 : ℕ) : ℤ) ≤ 0 + dl (0 :: ((R n ++ [1]).take s)) ∧
          0 + dl (0 :: ((R n ++ [1]).take s)) ≤ 0
        rw [dl_cons_zero]
        rcases le_or_gt s (R n).length with h2 | h2
        · rw [List.take_append_of_le_length h2]
          have := ih n (by omega) s h2
          push_cast
          constructor <;> linarith [this.1, this.2]
        · rw [List.take_of_length_le (by simp; omega), dl_append, (R_dl n).1]
          norm_num [dl]

lemma J_take (n t : ℕ) (ht : t ≤ (J n).length) :
    -((n : ℤ) + 1) ≤ dl ((J n).take t) ∧ dl ((J n).take t) ≤ 0 := by
  rw [J_eq] at ht ⊢
  rw [show 0 :: 1 :: 0 :: R n = [0, 1, 0] ++ R n from rfl, List.take_append, dl_append]
  simp only [List.length_cons] at ht
  have hR := R_take n (t - 3) (by omega)
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ 3 ≤ t by omega) with h | h | h | h
  · subst h
    norm_num [dl]
  · subst h
    norm_num [dl]
  · subst h
    norm_num [dl]
  · rw [List.take_of_length_le (by simpa using h), show t - [0, 1, 0].length = t - 3 from rfl]
    have h3 : dl [0, 1, 0] = -1 := by norm_num [dl]
    rw [h3]
    constructor <;> linarith [hR.1, hR.2]

/-! ### The fixed point -/

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

lemma W_eq (m i : ℕ) (hi : i < (J m).length) : W i = (J m).getD i 0 := by
  have hi' : i < (J (i + 1)).length := by have := J_length_ge (i + 1); omega
  have hW : W i = (J (i + 1)).getD i 0 := by
    unfold W
    rw [iter_succ_eq (i + 1), List.getD_append _ _ _ _ hi']
  rw [hW]
  rcases le_total (i + 1) m with h | h
  · exact getD_prefix (J_prefix h) hi'
  · exact (getD_prefix (J_prefix h) hi).symm

/-- Letter i is the same in every iterate with more than i + 1 letters. -/
lemma iter_stable (m i : ℕ) (hi : i + 1 < (iter m).length) : (iter m).getD i 0 = W i := by
  cases m with
  | zero =>
    have : i = 0 := by simp [iter] at hi; omega
    subst this
    rfl
  | succ m =>
    rw [iter_succ_eq m] at hi ⊢
    simp only [List.length_append, List.length_cons, List.length_nil] at hi
    rw [List.getD_append _ _ _ _ (by omega), W_eq m i (by omega)]

/-- Z(N): the number of letters 0 among the first N letters of W. -/
noncomputable def Z (N : ℕ) : ℕ := Nat.count (fun i => W i = 0) N

lemma Z_succ (N : ℕ) : Z (N + 1) = Z N + if W N = 0 then 1 else 0 := Nat.count_succ _ _

lemma Z_eq (m N : ℕ) (hN : N ≤ (J m).length) : Z N = ((J m).take N).count 0 := by
  induction N with
  | zero => simp [Z]
  | succ N ih =>
    have hN' : N < (J m).length := by omega
    have hW : W N = (J m)[N] := by rw [W_eq m N hN', List.getD_eq_getElem _ _ hN']
    rw [Z_succ, ih (by omega), List.take_add_one, List.getElem?_eq_getElem hN',
      List.count_append, hW]
    simp [List.count_singleton]

lemma Z_bound (N : ℕ) : -(2 * (Nat.log 2 N : ℤ) + 1) ≤ (N : ℤ) - 2 * Z N ∧
    (N : ℤ) - 2 * Z N ≤ 0 := by
  have hlen : N ≤ (J (2 * Nat.log 2 N)).length := by
    have h1 := J_length_pow (Nat.log 2 N)
    have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
    rw [J_eq]
    simp only [List.length_cons]
    rw [Nat.succ_eq_add_one] at h2
    omega
  have hd : (N : ℤ) - 2 * Z N = dl ((J (2 * Nat.log 2 N)).take N) := by
    rw [dl, Z_eq _ N hlen, List.length_take, min_eq_left hlen]
  rw [hd]
  have := J_take (2 * Nat.log 2 N) N hlen
  push_cast at this
  exact this

lemma W_zero : W 0 = 0 := by decide

lemma W_one : W 1 = 1 := by decide

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
  have h1 := (Z_bound (B + 1 + (2 * Z (B + 1) + 2))).2
  rw [hconst] at h1
  push_cast at h1
  omega

lemma a_le (n : ℕ) (hn : 1 ≤ n) : a n ≤ 2 * n := by
  have key : n ≤ Z (2 * n) := by
    have := (Z_bound (2 * n)).2
    push_cast at this
    omega
  have hlt : Nat.nth (fun i => W i = 0) (n - 1) < 2 * n :=
    Nat.nth_lt_of_lt_count (by unfold Z at key; omega)
  unfold a
  omega

lemma Z_two : Z 2 = 1 := by
  have h1 : Z 1 = 1 := by
    have h := Z_succ 0
    rw [if_pos W_zero] at h
    simpa [Z] using h
  have h := Z_succ 1
  rw [if_neg (by rw [W_one]; decide)] at h
  simpa [h1] using h

lemma Z_le (j : ℕ) : Z (2 + j) ≤ 1 + j := by
  induction j with
  | zero => simp [Z_two]
  | succ j ih =>
    rw [show 2 + (j + 1) = 2 + j + 1 by ring, Z_succ]
    split_ifs <;> omega

lemma a_gt (n : ℕ) (hn : 2 ≤ n) : n < a n := by
  have hinf := zeros_infinite
  have hc : Z (Nat.nth (fun i => W i = 0) (n - 1)) = n - 1 :=
    Nat.count_nth_of_infinite hinf (n - 1)
  have hW : W (Nat.nth (fun i => W i = 0) (n - 1)) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have hc1 : Z (Nat.nth (fun i => W i = 0) (n - 1) + 1) = n := by
    rw [Z_succ, if_pos hW, hc]
    omega
  unfold a
  by_contra hle
  have hp : Nat.nth (fun i => W i = 0) (n - 1) + 1 ≤ n := by omega
  have hp2 : 2 ≤ Nat.nth (fun i => W i = 0) (n - 1) + 1 := by
    by_contra h
    have h0 : Nat.nth (fun i => W i = 0) (n - 1) = 0 := by omega
    rw [h0] at hc1
    have : Z (0 + 1) ≤ 0 + 1 := Nat.count_le _
    omega
  obtain ⟨j, hj⟩ : ∃ j, Nat.nth (fun i => W i = 0) (n - 1) + 1 = 2 + j :=
    ⟨Nat.nth (fun i => W i = 0) (n - 1) - 1, by omega⟩
  have := Z_le j
  rw [← hj, hc1] at this
  omega

/-- |a(n) - 2n| <= 2 log2(8n + 8) + 1. -/
lemma a_bound {n : ℕ} (hn : 1 ≤ n) :
    |1 * (a n : ℝ) - 2 * n| ≤ 2 * Real.logb 2 (8 * n + 8) + 1 := by
  set p := Nat.nth (fun i => W i = 0) (n - 1) with hp
  have hinf := zeros_infinite
  have hZp : Z p = n - 1 := Nat.count_nth_of_infinite hinf (n - 1)
  have hWp : W p = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have hZ1 : Z (p + 1) = n := by
    rw [Z_succ, if_pos hWp, hZp]
    omega
  have ha : a n = p + 1 := rfl
  have hle := a_le n hn
  have hb := Z_bound (p + 1)
  rw [hZ1] at hb
  have hlog : Nat.log 2 (p + 1) ≤ Nat.log 2 (8 * n + 8) := Nat.log_mono_right (by omega)
  have hint : |((p + 1 : ℕ) : ℤ) - 2 * n| ≤ 2 * Nat.log 2 (8 * n + 8) + 1 := by
    rw [abs_le]
    push_cast at hb ⊢
    constructor <;> omega
  have hlogR : (Nat.log 2 (8 * n + 8) : ℝ) ≤ Real.logb 2 (8 * n + 8) := by
    calc (Nat.log 2 (8 * n + 8) : ℝ) ≤ Real.logb 2 ((8 * n + 8 : ℕ) : ℝ) :=
          Real.natLog_le_logb _ _
      _ = Real.logb 2 (8 * n + 8) := by push_cast; ring
  rw [abs_le] at hint
  have h1a : -(2 * (Nat.log 2 (8 * n + 8) : ℝ) + 1) ≤ ((p : ℝ) + 1) - 2 * (n : ℝ) := by
    exact_mod_cast hint.1
  have h1b : ((p : ℝ) + 1) - 2 * (n : ℝ) ≤ 2 * (Nat.log 2 (8 * n + 8) : ℝ) + 1 := by
    exact_mod_cast hint.2
  rw [abs_le, ha]
  push_cast
  constructor <;> linarith

/-- Kimberling's conjecture: a(n)/n -> 2, and -1 < 2 - a(n)/n < 1 for n >= 2. -/
theorem conjecture : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 2) ∧
    ∀ n : ℕ, 2 ≤ n → -1 < 2 - (a n : ℝ) / n ∧ 2 - (a n : ℝ) / n < 1 := by
  refine ⟨?_, fun n hn => ?_⟩
  · have := lim_of_bound (f := a) (p := 2) (q := 1) (K := 2) (C := 1) (by norm_num)
      fun n hn => a_bound hn
    rw [div_one] at this
    exact this
  · have hle := a_le n (by omega)
    have hgt := a_gt n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hle' : (a n : ℝ) ≤ 2 * n := by exact_mod_cast hle
    have hgt' : (n : ℝ) < a n := by exact_mod_cast hgt
    have h3 : (a n : ℝ) / n < 3 := by
      rw [div_lt_iff₀ hn']
      linarith
    have h1 : 1 < (a n : ℝ) / n := by
      rw [lt_div_iff₀ hn']
      linarith
    constructor <;> linarith

end OMA.S_oeis_a288601

theorem OMA.solution : type_of% @OMA.S_oeis_a288601.main :=
  OMA.S_oeis_a288601.conjecture
