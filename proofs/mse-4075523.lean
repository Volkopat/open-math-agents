import OMAStatements.S_mse_4075523

namespace OMA.P_mse_4075523

open OMA.S_mse_4075523

/-- Pell numbers: `P 0 = 0`, `P 1 = 1`, `P (k + 2) = 2 * P (k + 1) + P k`. -/
private def pell : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k + 2 => 2 * pell (k + 1) + pell k

private lemma pell_pos {k : ℕ} (hk : 1 ≤ k) : 1 ≤ pell k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => omega
    | 1 => simp [pell]
    | m + 2 =>
      rw [pell]
      have := ih (m + 1) (by omega) (by omega)
      omega

private lemma pell_mono (k : ℕ) : pell k ≤ pell (k + 1) := by
  induction k with
  | zero => simp [pell]
  | succ m ih =>
    rw [pell]
    omega

/-- Backwards iterates `β 0 = √n + a`, `β (j + 1) = 2 + 1 / β j`. -/
private noncomputable def betaSeq (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | j + 1 => 2 + 1 / betaSeq x0 j

private lemma betaSeq_gt_two {x0 : ℝ} (hx0 : 2 < x0) (j : ℕ) : 2 < betaSeq x0 j := by
  induction j with
  | zero => exact hx0
  | succ j ih =>
    rw [betaSeq]
    have : 0 < 1 / betaSeq x0 j := by positivity
    linarith

private lemma betaSeq_succ_lt_three {x0 : ℝ} (hx0 : 2 < x0) (j : ℕ) :
    betaSeq x0 (j + 1) < 3 := by
  rw [betaSeq]
  have h2 := betaSeq_gt_two hx0 j
  have h1 : 1 / betaSeq x0 j < 1 / 2 := by
    rw [one_div_lt_one_div (by linarith) (by norm_num)]
    exact h2
  linarith

private lemma floor_betaSeq_succ {x0 : ℝ} (hx0 : 2 < x0) (j : ℕ) :
    ⌊betaSeq x0 (j + 1)⌋ = 2 := by
  rw [Int.floor_eq_iff]
  have hlo := betaSeq_gt_two hx0 (j + 1)
  have hhi := betaSeq_succ_lt_three hx0 j
  constructor <;> norm_num <;> linarith

private lemma betaSeq_eq_pell {x0 : ℝ} (hx0 : 2 < x0) (j : ℕ) :
    betaSeq x0 j =
      ((pell (j + 1) : ℝ) * x0 + (pell j : ℝ)) /
        ((pell j : ℝ) * x0 + (if j = 0 then (1 : ℝ) else (pell (j - 1) : ℝ))) := by
  induction j with
  | zero =>
    simp [betaSeq, pell]
  | succ j ih =>
    rw [betaSeq, ih]
    have hnum_pos : 0 < (pell (j + 1) : ℝ) * x0 + (pell j : ℝ) := by
      have hp : (1 : ℝ) ≤ (pell (j + 1) : ℝ) := by exact_mod_cast pell_pos (by omega : 1 ≤ j + 1)
      have hpj : (0 : ℝ) ≤ (pell j : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hden_pos : 0 < (pell j : ℝ) * x0 + (if j = 0 then (1 : ℝ) else (pell (j - 1) : ℝ)) := by
      split_ifs
      · positivity
      · have hpj : (1 : ℝ) ≤ (pell j : ℝ) := by exact_mod_cast pell_pos (by omega)
        have hpm : (0 : ℝ) ≤ (pell (j - 1) : ℝ) := Nat.cast_nonneg _
        nlinarith
    have hne1 : (pell (j + 1) : ℝ) * x0 + (pell j : ℝ) ≠ 0 := ne_of_gt hnum_pos
    have hne2 : (pell j : ℝ) * x0 + (if j = 0 then (1 : ℝ) else (pell (j - 1) : ℝ)) ≠ 0 :=
      ne_of_gt hden_pos
    cases j with
    | zero =>
      simp only [zero_add, one_ne_zero, ↓reduceIte, pell, Nat.cast_zero, Nat.cast_one,
        zero_mul, one_mul, add_zero, div_one] at hne1 hne2 ⊢
      have hp0 : (pell 0 : ℝ) = 0 := by simp [pell]
      rw [hp0]
      field_simp
      ring
    | succ m =>
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel] at hne1 hne2 ⊢
      have hpell : (pell (m + 3) : ℝ) = 2 * (pell (m + 2) : ℝ) + (pell (m + 1) : ℝ) := by
        exact_mod_cast (show pell (m + 3) = 2 * pell (m + 2) + pell (m + 1) from rfl)
      have hpell2 : (pell (m + 2) : ℝ) = 2 * (pell (m + 1) : ℝ) + (pell m : ℝ) := by
        exact_mod_cast (show pell (m + 2) = 2 * pell (m + 1) + pell m from rfl)
      field_simp
      rw [show m + 1 + 1 + 1 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl, hpell, hpell2]
      ring

private theorem main_proof : type_of% @OMA.S_mse_4075523.main := by
  intro k hk
  set a : ℕ := pell k + 1
  set n : ℕ := a ^ 2 + 2 * pell (k - 1) + 1
  have ha_ge2 : 2 ≤ a := by
    have := pell_pos hk
    omega
  have hlt_sq : a ^ 2 < n := by omega
  have hgt_sq : n < (a + 1) ^ 2 := by
    have hle : pell (k - 1) ≤ pell k := by
      have h1 : k = (k - 1) + 1 := by omega
      conv_rhs => rw [h1]
      exact pell_mono (k - 1)
    have : (a + 1) ^ 2 = a ^ 2 + 2 * a + 1 := by ring
    omega
  have hnot_sq : ¬ IsSquare n := by
    rintro ⟨r, hr⟩
    have h1 : a < r := by nlinarith
    have h2 : r < a + 1 := by nlinarith
    omega
  refine ⟨n, hnot_sq, ?_⟩
  set s : ℝ := Real.sqrt (n : ℝ)
  have hs_gt : (a : ℝ) < s := by
    rw [Real.lt_sqrt (Nat.cast_nonneg a)]
    have : ((a ^ 2 : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hlt_sq
    simpa [Nat.cast_pow] using this
  have hs_lt : s < (a : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    have : (n : ℝ) < (((a + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hgt_sq
    simpa [Nat.cast_pow, Nat.cast_add] using this
  have hfloor0 : ⌊s⌋ = (a : ℤ) := by
    rw [Int.floor_eq_iff]
    exact ⟨le_of_lt hs_gt, by simpa using hs_lt⟩
  have hx0_gt : 2 < s + (a : ℝ) := by
    have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_ge2
    linarith
  have hfloor_beta0 : ⌊betaSeq (s + (a : ℝ)) 0⌋ = (2 * a : ℤ) := by
    rw [betaSeq, Int.floor_eq_iff]
    constructor
    · push_cast; linarith
    · push_cast; linarith
  have hstep_beta0 : 1 / (betaSeq (s + (a : ℝ)) 0 - (⌊betaSeq (s + (a : ℝ)) 0⌋ : ℝ)) =
      1 / (s - (a : ℝ)) := by
    rw [hfloor_beta0, betaSeq]
    push_cast; ring
  have hstep_beta_succ : ∀ j : ℕ,
      1 / (betaSeq (s + (a : ℝ)) (j + 1) - (⌊betaSeq (s + (a : ℝ)) (j + 1)⌋ : ℝ)) =
      betaSeq (s + (a : ℝ)) j := by
    intro j
    rw [floor_betaSeq_succ hx0_gt j, betaSeq]
    push_cast
    have : 2 + 1 / betaSeq (s + (a : ℝ)) j - 2 = 1 / betaSeq (s + (a : ℝ)) j := by ring
    rw [this, one_div_one_div]
  have hlink : 1 / (s - (a : ℝ)) = betaSeq (s + (a : ℝ)) (k - 1) := by
    rw [betaSeq_eq_pell hx0_gt (k - 1)]
    have hk1 : (k - 1) + 1 = k := by omega
    rw [hk1]
    have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    have hn_sub : s ^ 2 - (a : ℝ) ^ 2 = 2 * (pell (k - 1) : ℝ) + 1 := by
      rw [hs2]
      have : (n : ℝ) = (a : ℝ) ^ 2 + 2 * (pell (k - 1) : ℝ) + 1 := by
        exact_mod_cast (show n = a ^ 2 + 2 * pell (k - 1) + 1 from rfl)
      linarith
    have hsa_ne : s - (a : ℝ) ≠ 0 := by linarith
    have hden_ne : (pell (k - 1) : ℝ) * (s + (a : ℝ)) +
        (if k - 1 = 0 then (1 : ℝ) else (pell (k - 1 - 1) : ℝ)) ≠ 0 := by
      split_ifs
      · positivity
      · have hp : (1 : ℝ) ≤ (pell (k - 1) : ℝ) := by exact_mod_cast pell_pos (by omega)
        have hpm : (0 : ℝ) ≤ (pell (k - 1 - 1) : ℝ) := Nat.cast_nonneg _
        nlinarith
    rw [div_eq_div_iff hsa_ne hden_ne, one_mul]
    have hkey : ((pell k : ℝ) * (s + (a : ℝ)) + (pell (k - 1) : ℝ)) * (s - (a : ℝ)) =
        (pell k : ℝ) * (s ^ 2 - (a : ℝ) ^ 2) + (pell (k - 1) : ℝ) * (s - (a : ℝ)) := by ring
    rw [hkey, hn_sub]
    have ha_eq : (a : ℝ) = (pell k : ℝ) + 1 := by exact_mod_cast (show a = pell k + 1 from rfl)
    by_cases hk1_eq : k - 1 = 0
    · have hkeq : k = 1 := by omega
      subst hkeq
      simp only [Nat.sub_self, ↓reduceIte, pell, Nat.cast_zero, Nat.cast_one] at ha_eq ⊢
      linarith
    · simp only [hk1_eq, ↓reduceIte]
      have hpell_rel : (pell k : ℝ) = 2 * (pell (k - 1) : ℝ) + (pell (k - 1 - 1) : ℝ) := by
        have hnat : pell k = 2 * pell (k - 1) + pell (k - 1 - 1) := by
          have hk2 : k = (k - 1 - 1) + 2 := by omega
          conv_lhs => rw [hk2]
          rw [pell]
          have hsub : k - 1 - 1 + 1 = k - 1 := by omega
          rw [hsub]
        exact_mod_cast hnat
      rw [ha_eq]
      nlinarith
  -- Now describe cfTail s m for all m >= 1!
  have htail_one : cfTail s 1 = betaSeq (s + (a : ℝ)) (k - 1) := by
    rw [cfTail, cfTail, hfloor0, Int.cast_natCast, hlink]
  have htail_cycle : ∀ r : ℕ, r < k → cfTail s (r + 1) = betaSeq (s + (a : ℝ)) (k - 1 - r) := by
    intro r hr
    induction r with
    | zero => simpa using htail_one
    | succ r ih =>
      rw [cfTail, ih (by omega)]
      have hpos : k - 1 - r = (k - 1 - (r + 1)) + 1 := by omega
      rw [hpos, hstep_beta_succ]
  have htail_k : cfTail s k = betaSeq (s + (a : ℝ)) 0 := by
    have h := htail_cycle (k - 1) (by omega)
    simpa [show k - 1 + 1 = k by omega] using h
  have htail_k_succ : cfTail s (k + 1) = cfTail s 1 := by
    rw [cfTail, htail_k, hstep_beta0, hlink, htail_one]
  have htail_per : ∀ m : ℕ, 1 ≤ m → cfTail s (m + k) = cfTail s m := by
    intro m hm
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, m = t + 1 := ⟨m - 1, by omega⟩
    clear hm
    induction t with
    | zero => simpa [add_comm] using htail_k_succ
    | succ t ih =>
      rw [show t + 1 + 1 + k = (t + 1 + k) + 1 from by omega, cfTail, ih]
      rfl
  constructor
  -- Part 1: Periodicity of cfCoeff!
  · intro m hm
    unfold cfCoeff
    rw [htail_per m hm]
  -- Part 2: Minimality of period k!
  · intro d hd1 hdk
    refine ⟨k - d, by omega, ?_⟩
    unfold cfCoeff
    rw [show k - d + d = k from by omega, htail_k, hfloor_beta0]
    have hlt : k - d - 1 < k := by omega
    have htc := htail_cycle (k - d - 1) hlt
    rw [show k - d - 1 + 1 = k - d by omega] at htc
    rw [htc]
    have hpos : k - 1 - (k - d - 1) = (d - 1) + 1 := by omega
    rw [hpos, floor_betaSeq_succ hx0_gt (d - 1)]
    omega

end OMA.P_mse_4075523

theorem OMA.solution : type_of% @OMA.S_mse_4075523.main :=
  OMA.P_mse_4075523.main_proof
