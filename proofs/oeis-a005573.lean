import OMAStatements.S_oeis_a005573

open Polynomial Finset

namespace OMA.OeisA005573

open OMA.S_oeis_a005573

/-- Walks from start height `h` never going below zero. -/
def good (n : ℕ) (h : ℤ) (w : Fin n → Fin 6) : Prop :=
  ∀ m ≤ n, 0 ≤ h + ∑ i : Fin n, if (i : ℕ) < m then dz (w i) else 0

open Classical in
noncomputable def W (n : ℕ) (h : ℤ) : ℚ :=
  (((Finset.univ : Finset (Fin n → Fin 6)).filter fun w => good n h w).card : ℚ)

lemma good_cons (n : ℕ) (h : ℤ) (s : Fin 6) (w : Fin n → Fin 6) :
    good (n + 1) h (Fin.cons s w) ↔ 0 ≤ h ∧ good n (h + dz s) w := by
  have key : ∀ m : ℕ, (∑ i : Fin (n + 1),
      if (i : ℕ) < m + 1 then dz ((Fin.cons s w : Fin (n+1) → Fin 6) i) else 0)
      = dz s + ∑ i : Fin n, if (i : ℕ) < m then dz (w i) else 0 := by
    intro m
    rw [Fin.sum_univ_succ]
    simp
  have key0 : (∑ i : Fin (n + 1),
      if (i : ℕ) < 0 then dz ((Fin.cons s w : Fin (n+1) → Fin 6) i) else 0) = 0 := by
    simp
  constructor
  · intro hg
    refine ⟨?_, ?_⟩
    · have := hg 0 (Nat.zero_le _)
      rw [key0] at this
      simpa using this
    · intro m hm
      have := hg (m + 1) (by omega)
      rw [key] at this
      linarith
  · rintro ⟨h0, hg⟩ m hm
    rcases m with _ | m
    · rw [key0]; simpa using h0
    · rw [key]
      have := hg m (by omega)
      linarith

lemma W_neg (n : ℕ) (h : ℤ) (hh : h < 0) : W n h = 0 := by
  classical
  unfold W
  rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _ hg
  have := hg 0 (Nat.zero_le _)
  simp at this
  omega

lemma W_zero (h : ℕ) : W 0 h = 1 := by
  classical
  unfold W
  rw [Finset.filter_true_of_mem]
  · simp
  · intro w _ m _
    simp

lemma W_succ (n : ℕ) (h : ℤ) :
    W (n + 1) h = if 0 ≤ h then ∑ s : Fin 6, W n (h + dz s) else 0 := by
  classical
  unfold W
  simp only [Finset.natCast_card_filter]
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 6)
    (fun p => if good (n + 1) h (Fin.cons p.1 p.2) then (1 : ℚ) else 0)
    (fun w => if good (n + 1) h w then (1 : ℚ) else 0) (fun p => rfl),
    Fintype.sum_prod_type]
  simp only [good_cons]
  split_ifs with hh <;> simp [hh]

lemma dz0 : dz 0 = 0 := by decide
lemma dz1 : dz 1 = 0 := by decide
lemma dz2 : dz 2 = 0 := by decide
lemma dz3 : dz 3 = 0 := by decide
lemma dz4 : dz 4 = 1 := by decide
lemma dz5 : dz 5 = -1 := by decide

lemma sum_six (n : ℕ) (h : ℤ) :
    ∑ s : Fin 6, W n (h + dz s) = 4 * W n h + W n (h + 1) + W n (h - 1) := by
  rw [Fin.sum_univ_six, dz0, dz1, dz2, dz3, dz4, dz5, add_zero, sub_eq_add_neg]
  ring

noncomputable def Q : ℚ[X] := X ^ 2 + 4 * X + 1

lemma Q_split (p : ℚ[X]) : p * Q = p * X ^ 2 + 4 * (p * X) + p := by
  unfold Q; ring

lemma coeffQ_add2 (p : ℚ[X]) (m : ℕ) :
    (p * Q).coeff (m + 2) = p.coeff m + 4 * p.coeff (m + 1) + p.coeff (m + 2) := by
  have hx : (p * X).coeff (m + 2) = p.coeff (m + 1) := coeff_mul_X p (m + 1)
  rw [Q_split, coeff_add, coeff_add, coeff_ofNat_mul, coeff_mul_X_pow, hx]

lemma coeffQ_one (p : ℚ[X]) : (p * Q).coeff 1 = 4 * p.coeff 0 + p.coeff 1 := by
  have hx : (p * X).coeff 1 = p.coeff 0 := coeff_mul_X p 0
  rw [Q_split, coeff_add, coeff_add, coeff_ofNat_mul, coeff_mul_X_pow', if_neg (by norm_num), hx]
  ring

lemma coeffQ_zero (p : ℚ[X]) : (p * Q).coeff 0 = p.coeff 0 := by
  rw [Q_split, coeff_add, coeff_add, coeff_ofNat_mul, coeff_mul_X_pow', if_neg (by norm_num),
    coeff_mul_X_zero]
  ring

noncomputable def cf (p : ℚ[X]) (i : ℤ) : ℚ := if 0 ≤ i then p.coeff i.toNat else 0

lemma cf_nat (p : ℚ[X]) (k : ℕ) : cf p (k : ℤ) = p.coeff k := by
  simp [cf]

lemma cf_neg (p : ℚ[X]) (i : ℤ) (hi : i < 0) : cf p i = 0 := by
  simp [cf, not_le.mpr hi]

lemma cf_mulQ (p : ℚ[X]) (i : ℤ) :
    cf (p * Q) (i + 1) = cf p (i - 1) + 4 * cf p i + cf p (i + 1) := by
  obtain h | h | h | h : i ≤ -2 ∨ i = -1 ∨ i = 0 ∨ 1 ≤ i := by omega
  · rw [cf_neg _ _ (by omega), cf_neg _ _ (by omega), cf_neg _ _ (by omega),
      cf_neg _ _ (by omega)]
    ring
  · subst h
    rw [cf_neg p (-1 - 1) (by norm_num), cf_neg p (-1) (by norm_num),
      show (-1 : ℤ) + 1 = ((0 : ℕ) : ℤ) by norm_num, cf_nat, cf_nat, coeffQ_zero]
    ring
  · subst h
    rw [cf_neg p (0 - 1) (by norm_num), show (0 : ℤ) + 1 = ((1 : ℕ) : ℤ) by norm_num,
      show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, cf_nat, cf_nat, cf_nat, coeffQ_one]
    ring
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = (k : ℤ) + 1 :=
      ⟨(i - 1).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    rw [show (k : ℤ) + 1 + 1 = ((k + 2 : ℕ) : ℤ) by push_cast; ring,
      show (k : ℤ) + 1 - 1 = ((k : ℕ) : ℤ) by ring,
      show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
      cf_nat, cf_nat, cf_nat, cf_nat, coeffQ_add2]

noncomputable def V (n h : ℕ) : ℚ :=
  ∑ j ∈ range (2 * h + 2), cf (Q ^ n) ((n : ℤ) - h + j)

noncomputable def U (n h : ℕ) : ℚ :=
  ∑ j ∈ range (2 * h), cf (Q ^ n) ((n : ℤ) - h + 1 + j)

lemma U_zero (n : ℕ) : U n 0 = 0 := by simp [U]

lemma U_succ (n k : ℕ) : U n (k + 1) = V n k := by
  unfold U V
  rw [show 2 * (k + 1) = 2 * k + 2 by ring]
  refine sum_congr rfl (fun j _ => ?_)
  congr 1
  push_cast
  ring

lemma V_succ (n h : ℕ) : V (n + 1) h = 4 * V n h + V n (h + 1) + U n h := by
  have e : V (n + 1) h = ∑ j ∈ range (2 * h + 2), cf (Q ^ n) ((n : ℤ) - h + j - 1)
      + 4 * V n h + ∑ j ∈ range (2 * h + 2), cf (Q ^ n) ((n : ℤ) - h + j + 1) := by
    unfold V
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun j _ => ?_)
    rw [show ((n + 1 : ℕ) : ℤ) - h + j = ((n : ℤ) - h + j) + 1 by push_cast; ring, pow_succ,
      cf_mulQ]
  have A : V n (h + 1) = ∑ j ∈ range (2 * h + 2), cf (Q ^ n) ((n : ℤ) - h + j - 1)
      + cf (Q ^ n) ((n : ℤ) + h + 1) + cf (Q ^ n) ((n : ℤ) + h + 2) := by
    unfold V
    rw [show 2 * (h + 1) + 2 = 2 * h + 2 + 1 + 1 by ring, sum_range_succ _ (2 * h + 2 + 1),
      sum_range_succ _ (2 * h + 2)]
    congr 1
    · congr 1
      · refine sum_congr rfl (fun j _ => ?_)
        congr 1
        push_cast
        ring
      · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  have B : ∑ j ∈ range (2 * h + 2), cf (Q ^ n) ((n : ℤ) - h + j + 1)
      = U n h + cf (Q ^ n) ((n : ℤ) + h + 1) + cf (Q ^ n) ((n : ℤ) + h + 2) := by
    unfold U
    rw [show 2 * h + 2 = 2 * h + 1 + 1 by ring, sum_range_succ _ (2 * h + 1),
      sum_range_succ _ (2 * h)]
    congr 1
    · congr 1
      · refine sum_congr rfl (fun j _ => ?_)
        congr 1
        ring
      · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  rw [e]
  linarith [A, B]

lemma V_zero (h : ℕ) : V 0 h = 1 := by
  unfold V
  rw [Finset.sum_eq_single h]
  · rw [show ((0 : ℕ) : ℤ) - h + h = ((0 : ℕ) : ℤ) by ring, cf_nat, pow_zero, coeff_one_zero]
  · intro j _ hj
    unfold cf
    split_ifs with h0
    · rw [pow_zero, coeff_one, if_neg]
      intro h1
      have h2 := Int.toNat_of_nonneg h0
      rw [h1] at h2
      push_cast at h2
      omega
    · rfl
  · intro hh
    simp at hh
    omega

lemma W_eq_V : ∀ n h : ℕ, W n h = V n h := by
  intro n
  induction n with
  | zero => intro h; rw [W_zero, V_zero]
  | succ n ih =>
    intro h
    rw [W_succ, if_pos (Nat.cast_nonneg h), sum_six, V_succ]
    have e1 : W n ((h : ℤ) + 1) = V n (h + 1) := by
      have := ih (h + 1); push_cast at this; exact this
    have e2 : W n ((h : ℤ) - 1) = U n h := by
      rcases h with _ | k
      · rw [U_zero]; exact W_neg n _ (by norm_num)
      · rw [U_succ, ← ih k]; congr 1; push_cast; ring
    rw [e1, e2, ih h]

lemma a_eq (n : ℕ) : (a n : ℚ) = W n ((0 : ℕ) : ℤ) := by
  unfold a W good
  simp only [Nat.cast_zero, zero_add]

lemma V_zero_h (n : ℕ) : V n 0 = (Q ^ n).coeff n + (Q ^ n).coeff (n + 1) := by
  unfold V
  rw [show 2 * 0 + 2 = 2 by rfl, sum_range_succ, sum_range_one,
    show (n : ℤ) - ((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) = ((n : ℕ) : ℤ) by push_cast; ring,
    show (n : ℤ) - ((0 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
    cf_nat, cf_nat]

lemma Q_eq : Q = (X + C (-1)) ^ 2 + C 6 * X := by
  rw [map_neg, map_one, show (C 6 : ℚ[X]) = 6 from rfl]
  unfold Q
  ring

lemma Qpow_eq (n : ℕ) : Q ^ n = ∑ k ∈ range (n + 1),
    C ((6 : ℚ) ^ (n - k) * (n.choose k : ℚ)) * (X ^ (n - k) * (X + C (-1)) ^ (2 * k)) := by
  rw [Q_eq, add_pow]
  refine sum_congr rfl (fun k _ => ?_)
  rw [C_mul, C_pow, pow_mul, mul_pow, C_eq_natCast]
  ring

lemma coeff_n (n : ℕ) : (Q ^ n).coeff n = ∑ k ∈ range (n + 1),
    (6 : ℚ) ^ (n - k) * (n.choose k : ℚ) * ((-1) ^ k * ((2 * k).choose k : ℚ)) := by
  rw [Qpow_eq, finsetSum_coeff]
  refine sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [coeff_C_mul, coeff_X_pow_mul', if_pos (by omega), coeff_X_add_C_pow,
    show n - (n - k) = k by omega, show 2 * k - k = k by omega]

lemma coeff_n1 (n : ℕ) : (Q ^ n).coeff (n + 1) = ∑ k ∈ range (n + 1),
    (6 : ℚ) ^ (n - k) * (n.choose k : ℚ) *
      ((-1) ^ (2 * k - (k + 1)) * ((2 * k).choose (k + 1) : ℚ)) := by
  rw [Qpow_eq, finsetSum_coeff]
  refine sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [coeff_C_mul, coeff_X_pow_mul', if_pos (by omega), coeff_X_add_C_pow,
    show n + 1 - (n - k) = k + 1 by omega]

lemma cat (k : ℕ) : ((-1 : ℚ) ^ k * ((2 * k).choose k : ℚ)
    + (-1) ^ (2 * k - (k + 1)) * ((2 * k).choose (k + 1) : ℚ)) * ((k : ℚ) + 1)
    = (-1) ^ k * ((2 * k).choose k : ℚ) := by
  rcases k with _ | k
  · simp
  · have h := Nat.choose_succ_right_eq (2 * (k + 1)) (k + 1)
    rw [show 2 * (k + 1) - (k + 1) = k + 1 by omega] at h
    have hq : ((2 * (k + 1)).choose (k + 1 + 1) : ℚ) * ((k : ℚ) + 1 + 1)
        = ((2 * (k + 1)).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by
      exact_mod_cast h
    rw [show 2 * (k + 1) - (k + 1 + 1) = k by omega]
    push_cast
    linear_combination ((-1 : ℚ) ^ k) * hq

lemma rf_half (k : ℕ) : rf (1 / 2) k = ((2 * k).choose k : ℚ) * k.factorial / 4 ^ k := by
  induction k with
  | zero => simp [rf]
  | succ k ih =>
    unfold rf at *
    rw [ascPochhammer_succ_eval, ih]
    have h := Nat.succ_mul_centralBinom_succ k
    simp only [Nat.centralBinom] at h
    have hq : ((k : ℚ) + 1) * ((2 * (k + 1)).choose (k + 1) : ℚ)
        = 2 * (2 * k + 1) * ((2 * k).choose k : ℚ) := by exact_mod_cast h
    push_cast [Nat.factorial_succ]
    linear_combination (-(k.factorial : ℚ) / 4 ^ (k + 1)) * hq

lemma rf_negn (n k : ℕ) : rf (-(n : ℚ)) k = (-1) ^ k * k.factorial * (n.choose k : ℚ) := by
  induction k with
  | zero => simp [rf]
  | succ k ih =>
    unfold rf at *
    rw [ascPochhammer_succ_eval, ih]
    by_cases hk : k ≤ n
    · have h : ((n.choose (k + 1) * (k + 1) : ℕ) : ℚ) = ((n.choose k * (n - k) : ℕ) : ℚ) := by
        rw [Nat.choose_succ_right_eq]
      push_cast [Nat.cast_sub hk] at h
      push_cast [Nat.factorial_succ]
      linear_combination ((-1 : ℚ) ^ k * k.factorial) * h
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
      simp

lemma rf_two (k : ℕ) : rf 2 k = (k + 1).factorial := by
  induction k with
  | zero => simp [rf]
  | succ k ih =>
    unfold rf at *
    rw [ascPochhammer_succ_eval, ih]
    push_cast [Nat.factorial_succ]
    ring

lemma hyp_eq (n : ℕ) : hyp n = (Q ^ n).coeff n + (Q ^ n).coeff (n + 1) := by
  rw [coeff_n, coeff_n1, ← sum_add_distrib]
  unfold hyp
  rw [mul_sum]
  refine sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hc := cat k
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  rw [← mul_add, eq_div_of_mul_eq hk1 hc, rf_half, rf_negn, rf_two,
    show (6 : ℚ) ^ n = 6 ^ (n - k) * 6 ^ k by rw [← pow_add]; congr 1; omega,
    show (6 : ℚ) ^ k = 2 ^ k * 3 ^ k by rw [← mul_pow]; norm_num,
    show (4 : ℚ) ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num, div_pow]
  push_cast [Nat.factorial_succ]
  field_simp

end OMA.OeisA005573

theorem OMA.solution : type_of% @OMA.S_oeis_a005573.main := by
  intro n
  rw [OMA.OeisA005573.a_eq, OMA.OeisA005573.W_eq_V, OMA.OeisA005573.V_zero_h,
    OMA.OeisA005573.hyp_eq]
