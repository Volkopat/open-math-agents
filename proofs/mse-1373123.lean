import OMAStatements.S_mse_1373123

namespace OMA.S_mse_1373123_proof

open OMA.S_mse_1373123

private noncomputable def Li2 (x : ℝ) : ℝ :=
  ∑' n : ℕ, x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2

private noncomputable def Li3 (x : ℝ) : ℝ :=
  ∑' n : ℕ, x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 3

private lemma Li2_zero : Li2 0 = 0 := by simp [Li2]

private lemma Li3_zero : Li3 0 = 0 := by simp [Li3]

private lemma Li4_zero : Li4 0 = 0 := by simp [Li4]

private lemma summable_inv_pow_two : Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  exact h.summable

private lemma summable_inv_pow_three : Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3 := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) summable_inv_pow_two
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hpow : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 3 :=
    pow_le_pow_right₀ h1 (by omega)
  exact one_div_le_one_div_of_le (by positivity) hpow

private lemma summable_inv_pow_four : Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four
  exact h.summable

private lemma Li2_one : Li2 1 = Real.pi ^ 2 / 6 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa [Li2] using h.tsum_eq

private lemma Li4_one : Li4 1 = Real.pi ^ 4 / 90 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four
  simpa [Li4] using h.tsum_eq

private lemma continuousOn_Li_pow (k : ℕ)
    (hu : Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ k) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ, x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ k) (Set.Icc (-1) 1) := by
  refine continuousOn_tsum (u := fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ k)
    (fun n => ((continuous_pow (n + 1)).div_const _).continuousOn) hu (fun n x hx => ?_)
  have hden : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg _) k
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_nonneg hden]
  have hax : |x| ≤ 1 := abs_le.mpr hx
  have hpow : |x| ^ (n + 1) ≤ 1 := pow_le_one₀ (abs_nonneg x) hax
  exact div_le_div_of_nonneg_right hpow hden

private lemma continuousOn_Li2 : ContinuousOn Li2 (Set.Icc (-1) 1) :=
  continuousOn_Li_pow 2 summable_inv_pow_two

private lemma continuousOn_Li3 : ContinuousOn Li3 (Set.Icc (-1) 1) :=
  continuousOn_Li_pow 3 summable_inv_pow_three

private lemma continuousOn_Li4 : ContinuousOn Li4 (Set.Icc (-1) 1) :=
  continuousOn_Li_pow 4 summable_inv_pow_four

private lemma hasDerivAt_Li_pow (k : ℕ) (hk : 1 ≤ k) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun z : ℝ => ∑' n : ℕ, z ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ k)
      (∑' n : ℕ, x ^ n / ((n + 1 : ℕ) : ℝ) ^ (k - 1)) x := by
  set r : ℝ := (|x| + 1) / 2
  have hr0 : 0 < r := by dsimp only [r]; linarith [abs_nonneg x]
  have hr1 : r < 1 := by dsimp only [r]; linarith
  have hxr : |x| < r := by dsimp only [r]; linarith
  have hx_mem : x ∈ Set.Ioo (-r) r := abs_lt.mp hxr
  have h0_mem : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr0⟩
  have hu : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one (le_of_lt hr0) hr1
  have hsum0 : Summable fun n : ℕ => (0 : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ k := by
    simp only [zero_pow (Nat.succ_ne_zero _), zero_div]
    exact summable_zero
  have hd : ∀ n : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      HasDerivAt (fun z : ℝ => z ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ k)
        (y ^ n / ((n + 1 : ℕ) : ℝ) ^ (k - 1)) y := by
    intro n y _
    refine ((hasDerivAt_pow (n + 1) y).div_const (((n + 1 : ℕ) : ℝ) ^ k)).congr_deriv ?_
    have hn_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have hpow : ((n + 1 : ℕ) : ℝ) ^ k = ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (k - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hk]
    simp only [Nat.add_sub_cancel, hpow]
    exact mul_div_mul_left _ _ hn_ne
  have hle : ∀ n : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      ‖y ^ n / ((n + 1 : ℕ) : ℝ) ^ (k - 1)‖ ≤ r ^ n := by
    intro n y hy
    have hden : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (k - 1) := pow_nonneg (Nat.cast_nonneg _) _
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_nonneg hden]
    have hay : |y| ≤ r := le_of_lt (abs_lt.mpr hy)
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (k - 1) :=
      one_le_pow₀ (by exact_mod_cast Nat.succ_pos n)
    have h2 : |y| ^ n ≤ r ^ n := pow_le_pow_left₀ (abs_nonneg y) hay n
    calc
      |y| ^ n / ((n + 1 : ℕ) : ℝ) ^ (k - 1) ≤ |y| ^ n / 1 :=
        div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg y) n) zero_lt_one h1
      _ = |y| ^ n := div_one _
      _ ≤ r ^ n := h2
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hd hle h0_mem hsum0 hx_mem

private lemma hasDerivAt_Li2 {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasDerivAt Li2 (-Real.log (1 - x) / x) x := by
  refine (hasDerivAt_Li_pow 2 (by omega) hx).congr_deriv ?_
  have hsum := (Real.hasSum_pow_div_log_of_abs_lt_one hx).tsum_eq
  rw [eq_div_iff hx0, mul_comm, ← tsum_mul_left]
  have heq : (fun n : ℕ => x * (x ^ n / ((n + 1 : ℕ) : ℝ) ^ (2 - 1))) =
      (fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1)) := by
    ext n
    simp only [Nat.reduceSub, Nat.cast_add, Nat.cast_one, pow_succ']
    ring
  rw [heq, hsum]

private lemma hasDerivAt_Li3 {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasDerivAt Li3 (Li2 x / x) x := by
  refine (hasDerivAt_Li_pow 3 (by omega) hx).congr_deriv ?_
  rw [eq_div_iff hx0, mul_comm, ← tsum_mul_left]
  unfold Li2
  congr 1
  ext n
  simp only [Nat.reduceSub, pow_succ']
  ring

private lemma hasDerivAt_Li4 {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasDerivAt Li4 (Li3 x / x) x := by
  refine (hasDerivAt_Li_pow 4 (by omega) hx).congr_deriv ?_
  rw [eq_div_iff hx0, mul_comm, ← tsum_mul_left]
  unfold Li3
  congr 1
  ext n
  simp only [Nat.reduceSub, pow_succ']
  ring

private lemma const_of_hasDerivAt_zero {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f 0 x) :
    ∀ x ∈ Set.Icc a b, f x = f a := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hlt
  · rfl
  · have hcont' : ContinuousOn f (Set.Icc a x) :=
      hcont.mono (Set.Icc_subset_Icc_right hx.2)
    have hderiv' : ∀ y ∈ Set.Ioo a x, HasDerivAt f 0 y :=
      fun y hy => hderiv y ⟨hy.1, lt_of_lt_of_le hy.2 hx.2⟩
    rcases exists_hasDerivAt_eq_slope f (fun _ => 0) hlt hcont' hderiv' with ⟨_, _, hc⟩
    have hne : x - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
    have hzero : f x - f a = 0 := (div_eq_zero_iff.mp hc.symm).resolve_right hne
    linarith

private lemma hasDerivAt_one_sub (t : ℝ) : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
  refine ((hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_id t)).congr_deriv ?_
  ring

private lemma hasDerivAt_one_sub_two_mul (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 - 2 * s) (-2) t := by
  refine ((hasDerivAt_const t (1 : ℝ)).fun_sub ((hasDerivAt_id t).const_mul 2)).congr_deriv ?_
  ring

private lemma hasDerivAt_sq (t : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
  refine (hasDerivAt_pow 2 t).congr_deriv ?_
  norm_num

private lemma Li2_dup {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Li2 x + Li2 (-x) = (1 / 2 : ℝ) * Li2 (x ^ 2) := by
  let g : ℝ → ℝ := fun t => Li2 t + Li2 (-t) - (1 / 2 : ℝ) * Li2 (t ^ 2)
  have hcont : ContinuousOn g (Set.Icc 0 1) := by
    have h1 : ContinuousOn Li2 (Set.Icc 0 1) :=
      continuousOn_Li2.mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
    have h2 : ContinuousOn (fun t => Li2 (-t)) (Set.Icc 0 1) :=
      continuousOn_Li2.comp continuous_neg.continuousOn
        (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have h3 : ContinuousOn (fun t => Li2 (t ^ 2)) (Set.Icc 0 1) :=
      continuousOn_Li2.comp (continuous_pow 2).continuousOn
        (fun t ht => ⟨by nlinarith [ht.1], by nlinarith [ht.1, ht.2]⟩)
    exact (h1.add h2).sub (continuousOn_const.mul h3)
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have ht_abs : |t| < 1 := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
    have hnt_abs : |-t| < 1 := by rw [abs_neg]; exact ht_abs
    have ht2_abs : |t ^ 2| < 1 := abs_lt.mpr ⟨by nlinarith [ht.1], by nlinarith [ht.1, ht.2]⟩
    have ht2_ne : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    have hd1 : HasDerivAt Li2 (-Real.log (1 - t) / t) t := hasDerivAt_Li2 ht_abs ht0
    have hd2 : HasDerivAt (fun s => Li2 (-s)) ((-Real.log (1 - -t) / -t) * (-1)) t :=
      (hasDerivAt_Li2 hnt_abs (neg_ne_zero.mpr ht0)).comp t (hasDerivAt_neg t)
    have hd3 : HasDerivAt (fun s => (1 / 2 : ℝ) * Li2 (s ^ 2))
        ((1 / 2 : ℝ) * ((-Real.log (1 - t ^ 2) / t ^ 2) * (2 * t))) t :=
      ((hasDerivAt_Li2 ht2_abs ht2_ne).comp (h := fun s : ℝ => s ^ 2) t (hasDerivAt_sq t)).const_mul (1 / 2)
    refine ((hd1.fun_add hd2).fun_sub hd3).congr_deriv ?_
    have hlog : Real.log (1 - t ^ 2) = Real.log (1 - t) + Real.log (1 + t) := by
      rw [show 1 - t ^ 2 = (1 - t) * (1 + t) by ring]
      exact Real.log_mul (by linarith [ht.2]) (by linarith [ht.1])
    rw [show 1 - -t = 1 + t by ring, hlog]
    field_simp [ht0]
    ring
  have h0 : g 0 = 0 := by simp [g, Li2_zero]
  have hgx := const_of_hasDerivAt_zero hcont hderiv x ⟨hx0, hx1⟩
  rw [h0] at hgx
  dsimp only [g] at hgx
  linarith

private lemma Li3_dup {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Li3 x + Li3 (-x) = (1 / 4 : ℝ) * Li3 (x ^ 2) := by
  let g : ℝ → ℝ := fun t => Li3 t + Li3 (-t) - (1 / 4 : ℝ) * Li3 (t ^ 2)
  have hcont : ContinuousOn g (Set.Icc 0 1) := by
    have h1 : ContinuousOn Li3 (Set.Icc 0 1) :=
      continuousOn_Li3.mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
    have h2 : ContinuousOn (fun t => Li3 (-t)) (Set.Icc 0 1) :=
      continuousOn_Li3.comp continuous_neg.continuousOn
        (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have h3 : ContinuousOn (fun t => Li3 (t ^ 2)) (Set.Icc 0 1) :=
      continuousOn_Li3.comp (continuous_pow 2).continuousOn
        (fun t ht => ⟨by nlinarith [ht.1], by nlinarith [ht.1, ht.2]⟩)
    exact (h1.add h2).sub (continuousOn_const.mul h3)
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have ht_abs : |t| < 1 := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
    have hnt_abs : |-t| < 1 := by rw [abs_neg]; exact ht_abs
    have ht2_abs : |t ^ 2| < 1 := abs_lt.mpr ⟨by nlinarith [ht.1], by nlinarith [ht.1, ht.2]⟩
    have ht2_ne : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    have hd1 : HasDerivAt Li3 (Li2 t / t) t := hasDerivAt_Li3 ht_abs ht0
    have hd2 : HasDerivAt (fun s => Li3 (-s)) ((Li2 (-t) / -t) * (-1)) t :=
      (hasDerivAt_Li3 hnt_abs (neg_ne_zero.mpr ht0)).comp t (hasDerivAt_neg t)
    have hd3 : HasDerivAt (fun s => (1 / 4 : ℝ) * Li3 (s ^ 2))
        ((1 / 4 : ℝ) * ((Li2 (t ^ 2) / t ^ 2) * (2 * t))) t :=
      ((hasDerivAt_Li3 ht2_abs ht2_ne).comp (h := fun s : ℝ => s ^ 2) t (hasDerivAt_sq t)).const_mul (1 / 4)
    refine ((hd1.fun_add hd2).fun_sub hd3).congr_deriv ?_
    have hdup := Li2_dup (le_of_lt ht.1) (le_of_lt ht.2)
    field_simp [ht0]
    linarith
  have h0 : g 0 = 0 := by simp [g, Li3_zero]
  have hgx := const_of_hasDerivAt_zero hcont hderiv x ⟨hx0, hx1⟩
  rw [h0] at hgx
  dsimp only [g] at hgx
  linarith

private lemma Li4_dup {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Li4 x + Li4 (-x) = (1 / 8 : ℝ) * Li4 (x ^ 2) := by
  let g : ℝ → ℝ := fun t => Li4 t + Li4 (-t) - (1 / 8 : ℝ) * Li4 (t ^ 2)
  have hcont : ContinuousOn g (Set.Icc 0 1) := by
    have h1 : ContinuousOn Li4 (Set.Icc 0 1) :=
      continuousOn_Li4.mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
    have h2 : ContinuousOn (fun t => Li4 (-t)) (Set.Icc 0 1) :=
      continuousOn_Li4.comp continuous_neg.continuousOn
        (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have h3 : ContinuousOn (fun t => Li4 (t ^ 2)) (Set.Icc 0 1) :=
      continuousOn_Li4.comp (continuous_pow 2).continuousOn
        (fun t ht => ⟨by nlinarith [ht.1], by nlinarith [ht.1, ht.2]⟩)
    exact (h1.add h2).sub (continuousOn_const.mul h3)
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have ht_abs : |t| < 1 := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
    have hnt_abs : |-t| < 1 := by rw [abs_neg]; exact ht_abs
    have ht2_abs : |t ^ 2| < 1 := abs_lt.mpr ⟨by nlinarith [ht.1], by nlinarith [ht.1, ht.2]⟩
    have ht2_ne : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    have hd1 : HasDerivAt Li4 (Li3 t / t) t := hasDerivAt_Li4 ht_abs ht0
    have hd2 : HasDerivAt (fun s => Li4 (-s)) ((Li3 (-t) / -t) * (-1)) t :=
      (hasDerivAt_Li4 hnt_abs (neg_ne_zero.mpr ht0)).comp t (hasDerivAt_neg t)
    have hd3 : HasDerivAt (fun s => (1 / 8 : ℝ) * Li4 (s ^ 2))
        ((1 / 8 : ℝ) * ((Li3 (t ^ 2) / t ^ 2) * (2 * t))) t :=
      ((hasDerivAt_Li4 ht2_abs ht2_ne).comp (h := fun s : ℝ => s ^ 2) t (hasDerivAt_sq t)).const_mul (1 / 8)
    refine ((hd1.fun_add hd2).fun_sub hd3).congr_deriv ?_
    have hdup := Li3_dup (le_of_lt ht.1) (le_of_lt ht.2)
    field_simp [ht0]
    linarith
  have h0 : g 0 = 0 := by simp [g, Li4_zero]
  have hgx := const_of_hasDerivAt_zero hcont hderiv x ⟨hx0, hx1⟩
  rw [h0] at hgx
  dsimp only [g] at hgx
  linarith

private lemma Li2_neg_one : Li2 (-1) = -Real.pi ^ 2 / 12 := by
  have h := Li2_dup (x := 1) (by norm_num) (le_refl 1)
  rw [one_pow, Li2_one] at h
  linarith

private lemma Li3_neg_one : Li3 (-1) = -(3 / 4 : ℝ) * Li3 1 := by
  have h := Li3_dup (x := 1) (by norm_num) (le_refl 1)
  rw [one_pow] at h
  linarith

private lemma Li4_neg_one : Li4 (-1) = -7 * Real.pi ^ 4 / 720 := by
  have h := Li4_dup (x := 1) (by norm_num) (le_refl 1)
  rw [one_pow, Li4_one] at h
  linarith

private lemma continuousOn_log_mul_log_sub (c : ℝ) (hc0 : 0 < c) (b : ℝ) (_hb0 : 0 ≤ b)
    (hcb : c * b < 1) :
    ContinuousOn (fun t : ℝ => Real.log t * Real.log (1 - c * t)) (Set.Icc 0 b) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | hpos
  · rw [ContinuousWithinAt, Real.log_zero, zero_mul]
    have hmul : Filter.Tendsto (fun s : ℝ => s * Real.log s) (nhdsWithin 0 (Set.Icc 0 b)) (nhds 0) := by
      have hcont := Real.continuous_mul_log.continuousWithinAt (x := (0 : ℝ)) (s := Set.Icc 0 b)
      rw [ContinuousWithinAt, zero_mul] at hcont
      exact hcont
    have hlo : Filter.Tendsto (fun s : ℝ => (-(c / (1 - c * b))) * (s * Real.log s))
        (nhdsWithin 0 (Set.Icc 0 b)) (nhds 0) := by
      simpa using hmul.const_mul (-(c / (1 - c * b)))
    have hhi : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) (nhdsWithin 0 (Set.Icc 0 b)) (nhds 0) :=
      tendsto_const_nhds
    have hnhds : Set.Icc (0 : ℝ) b ∈ nhdsWithin (0 : ℝ) (Set.Icc 0 b) := self_mem_nhdsWithin
    have hlt1 : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Icc 0 b), s < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have hmem_le : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Icc 0 b),
        0 ≤ Real.log s * Real.log (1 - c * s) ∧
        Real.log s * Real.log (1 - c * s) ≤ (-(c / (1 - c * b))) * (s * Real.log s) := by
      filter_upwards [hnhds, hlt1] with s hs hs1
      rcases eq_or_lt_of_le hs.1 with rfl | hs_pos
      · simp
      · have hlog_s : Real.log s ≤ 0 := Real.log_nonpos (le_of_lt hs_pos) (le_of_lt hs1)
        have h1cs_pos : 0 < 1 - c * s := by nlinarith [hs.2]
        have h1cs_le1 : 1 - c * s ≤ 1 := by nlinarith [hs.1]
        have hlog_1cs_le0 : Real.log (1 - c * s) ≤ 0 := Real.log_nonpos (le_of_lt h1cs_pos) h1cs_le1
        have hlog_1cs_ge : -(c / (1 - c * b)) * s ≤ Real.log (1 - c * s) := by
          have h1 := Real.one_sub_inv_le_log_of_pos h1cs_pos
          have h2 : 1 - (1 - c * s)⁻¹ = -(c * s / (1 - c * s)) := by
            field_simp [ne_of_gt h1cs_pos]
            ring
          have h3 : c * s / (1 - c * s) ≤ c * s / (1 - c * b) :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) (by nlinarith [hs.2])
          have h4 : -(c / (1 - c * b)) * s = -(c * s / (1 - c * b)) := by ring
          linarith
        refine ⟨mul_nonneg_of_nonpos_of_nonpos hlog_s hlog_1cs_le0, ?_⟩
        have hmul_ineq := mul_le_mul_of_nonpos_left hlog_1cs_ge hlog_s
        linarith [show Real.log s * (-(c / (1 - c * b)) * s) = (-(c / (1 - c * b))) * (s * Real.log s) by ring]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hhi hlo
      (hmem_le.mono fun _ h => h.1) (hmem_le.mono fun _ h => h.2)
  · have h1ct : 1 - c * t ≠ 0 := by nlinarith [ht.2]
    have hcont1 : ContinuousAt (fun s => Real.log s) t := Real.continuousAt_log (ne_of_gt hpos)
    have hlin : ContinuousAt (fun s : ℝ => 1 - c * s) t := by fun_prop
    have hcont2 : ContinuousAt (fun s => Real.log (1 - c * s)) t :=
      (Real.continuousAt_log h1ct).comp (f := fun s : ℝ => 1 - c * s) hlin
    exact (hcont1.mul hcont2).continuousWithinAt

private lemma Li2_euler {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    Li2 u + Li2 (1 - u) + Real.log u * Real.log (1 - u) = Real.pi ^ 2 / 6 := by
  let g : ℝ → ℝ := fun t => Li2 t + Li2 (1 - t) + Real.log t * Real.log (1 - t)
  have hcont : ContinuousOn g (Set.Icc 0 (1 / 2)) := by
    have h1 : ContinuousOn Li2 (Set.Icc 0 (1 / 2)) :=
      continuousOn_Li2.mono (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have h2 : ContinuousOn (fun t => Li2 (1 - t)) (Set.Icc 0 (1 / 2)) :=
      continuousOn_Li2.comp (by fun_prop : ContinuousOn (fun t : ℝ => 1 - t) _)
        (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have h3 : ContinuousOn (fun t => Real.log t * Real.log (1 - t)) (Set.Icc 0 (1 / 2)) := by
      simpa using continuousOn_log_mul_log_sub 1 (by norm_num) (1 / 2) (by norm_num) (by norm_num)
    exact (h1.add h2).add h3
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 2), HasDerivAt g 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have h1t0 : 1 - t ≠ 0 := by linarith [ht.2]
    have hd1 : HasDerivAt Li2 (-Real.log (1 - t) / t) t :=
      hasDerivAt_Li2 (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩) ht0
    have hd2 : HasDerivAt (fun s => Li2 (1 - s)) ((-Real.log (1 - (1 - t)) / (1 - t)) * (-1)) t :=
      (hasDerivAt_Li2 (abs_lt.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩) h1t0).comp t
        (hasDerivAt_one_sub t)
    have hd3 : HasDerivAt (fun s => Real.log s * Real.log (1 - s))
        (t⁻¹ * Real.log (1 - t) + Real.log t * ((1 - t)⁻¹ * (-1))) t :=
      (Real.hasDerivAt_log ht0).fun_mul
        ((Real.hasDerivAt_log h1t0).comp t (hasDerivAt_one_sub t))
    refine ((hd1.fun_add hd2).fun_add hd3).congr_deriv ?_
    rw [show 1 - (1 - t) = t by ring]
    field_simp [ht0, h1t0]
    ring
  have h0 : g 0 = Real.pi ^ 2 / 6 := by simp [g, Li2_zero, Li2_one]
  have hgu := const_of_hasDerivAt_zero hcont hderiv u ⟨hu0, hu1⟩
  rw [h0] at hgu
  dsimp only [g] at hgu
  linarith

private lemma Li2_half : Li2 (1 / 2) = Real.pi ^ 2 / 12 - (Real.log 2) ^ 2 / 2 := by
  have h := Li2_euler (u := 1 / 2) (by norm_num) (le_refl _)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring, one_div, Real.log_inv] at h
  linarith

private lemma Li2_landen {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    Li2 u + Li2 (-u / (1 - u)) + (Real.log (1 - u)) ^ 2 / 2 = 0 := by
  let g : ℝ → ℝ := fun t => Li2 t + Li2 (-t / (1 - t)) + (Real.log (1 - t)) ^ 2 / 2
  have hcont : ContinuousOn g (Set.Icc 0 (1 / 2)) := by
    have h1 : ContinuousOn Li2 (Set.Icc 0 (1 / 2)) :=
      continuousOn_Li2.mono (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hfrac : ContinuousOn (fun t : ℝ => -t / (1 - t)) (Set.Icc 0 (1 / 2)) :=
      (by fun_prop : ContinuousOn (fun t : ℝ => -t) _).div
        (by fun_prop : ContinuousOn (fun t : ℝ => 1 - t) _)
        (fun t ht => by linarith [ht.2])
    have h2 : ContinuousOn (fun t => Li2 (-t / (1 - t))) (Set.Icc 0 (1 / 2)) :=
      continuousOn_Li2.comp hfrac (fun t ht => by
        have h1t : 0 < 1 - t := by linarith [ht.2]
        refine ⟨?_, ?_⟩
        · rw [le_div_iff₀ h1t]; linarith [ht.2]
        · rw [div_le_iff₀ h1t]; linarith [ht.1, ht.2])
    have h3 : ContinuousOn (fun t : ℝ => (Real.log (1 - t)) ^ 2 / 2) (Set.Icc 0 (1 / 2)) := by
      have hlog : ContinuousOn (fun t : ℝ => Real.log (1 - t)) (Set.Icc 0 (1 / 2)) :=
        fun t ht => (Real.continuousAt_log (by linarith [ht.2])).comp
          (by fun_prop : ContinuousAt (fun s : ℝ => 1 - s) t) |>.continuousWithinAt
      exact (hlog.pow 2).div_const 2
    exact (h1.add h2).add h3
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 2), HasDerivAt g 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have h1t_pos : 0 < 1 - t := by linarith [ht.2]
    have h1t0 : 1 - t ≠ 0 := ne_of_gt h1t_pos
    have hfrac_ne : -t / (1 - t) ≠ 0 := div_ne_zero (neg_ne_zero.mpr ht0) h1t0
    have hfrac_abs : |-t / (1 - t)| < 1 := by
      rw [abs_div, abs_neg, abs_of_pos ht.1, abs_of_pos h1t_pos, div_lt_one h1t_pos]
      linarith [ht.2]
    have hd_frac : HasDerivAt (fun s : ℝ => -s / (1 - s)) (-1 / (1 - t) ^ 2) t := by
      refine ((hasDerivAt_neg t).fun_div (hasDerivAt_one_sub t) h1t0).congr_deriv ?_
      ring
    have hd1 : HasDerivAt Li2 (-Real.log (1 - t) / t) t :=
      hasDerivAt_Li2 (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩) ht0
    have hd2 : HasDerivAt (fun s => Li2 (-s / (1 - s)))
        ((-Real.log (1 - -t / (1 - t)) / (-t / (1 - t))) * (-1 / (1 - t) ^ 2)) t :=
      (hasDerivAt_Li2 hfrac_abs hfrac_ne).comp (h := fun s : ℝ => -s / (1 - s)) t hd_frac
    have hd3 : HasDerivAt (fun s => (Real.log (1 - s)) ^ 2 / 2)
        ((2 * (Real.log (1 - t)) ^ 1 * ((1 - t)⁻¹ * (-1))) / 2) t :=
      (((Real.hasDerivAt_log h1t0).comp t (hasDerivAt_one_sub t)).fun_pow 2).div_const 2
    refine ((hd1.fun_add hd2).fun_add hd3).congr_deriv ?_
    have hlog : Real.log (1 - -t / (1 - t)) = -Real.log (1 - t) := by
      rw [show 1 - -t / (1 - t) = (1 - t)⁻¹ by field_simp [h1t0]; ring, Real.log_inv]
    rw [hlog]
    field_simp [ht0, h1t0]
    ring
  have h0 : g 0 = 0 := by simp [g, Li2_zero]
  have hgu := const_of_hasDerivAt_zero hcont hderiv u ⟨hu0, hu1⟩
  rw [h0] at hgu
  dsimp only [g] at hgu
  linarith

private lemma Li3_half :
    Li3 (1 / 2) = (7 / 8 : ℝ) * Li3 1 - Real.pi ^ 2 / 12 * Real.log 2 + (Real.log 2) ^ 3 / 6 := by
  let g : ℝ → ℝ := fun t =>
    Li3 t + Li3 (1 - t) + Li3 (-t / (1 - t)) - (Real.pi ^ 2 / 6) * Real.log (1 - t) +
      (1 / 2 : ℝ) * (Real.log t * Real.log (1 - t)) * Real.log (1 - t) -
      (1 / 6 : ℝ) * (Real.log (1 - t)) ^ 3
  have hcont : ContinuousOn g (Set.Icc 0 (1 / 2)) := by
    have h1 : ContinuousOn Li3 (Set.Icc 0 (1 / 2)) :=
      continuousOn_Li3.mono (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have h2 : ContinuousOn (fun t => Li3 (1 - t)) (Set.Icc 0 (1 / 2)) :=
      continuousOn_Li3.comp (by fun_prop : ContinuousOn (fun t : ℝ => 1 - t) _)
        (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    have hfrac : ContinuousOn (fun t : ℝ => -t / (1 - t)) (Set.Icc 0 (1 / 2)) :=
      (by fun_prop : ContinuousOn (fun t : ℝ => -t) _).div
        (by fun_prop : ContinuousOn (fun t : ℝ => 1 - t) _)
        (fun t ht => by linarith [ht.2])
    have h3 : ContinuousOn (fun t => Li3 (-t / (1 - t))) (Set.Icc 0 (1 / 2)) :=
      continuousOn_Li3.comp hfrac (fun t ht => by
        have h1t : 0 < 1 - t := by linarith [ht.2]
        refine ⟨?_, ?_⟩
        · rw [le_div_iff₀ h1t]; linarith [ht.2]
        · rw [div_le_iff₀ h1t]; linarith [ht.1, ht.2])
    have hlog : ContinuousOn (fun t : ℝ => Real.log (1 - t)) (Set.Icc 0 (1 / 2)) :=
      fun t ht => (Real.continuousAt_log (by linarith [ht.2])).comp
        (by fun_prop : ContinuousAt (fun s : ℝ => 1 - s) t) |>.continuousWithinAt
    have hlog2 : ContinuousOn (fun t : ℝ => Real.log t * Real.log (1 - t)) (Set.Icc 0 (1 / 2)) := by
      simpa using continuousOn_log_mul_log_sub 1 (by norm_num) (1 / 2) (by norm_num) (by norm_num)
    exact ((((h1.add h2).add h3).sub (continuousOn_const.mul hlog)).add
      ((continuousOn_const.mul hlog2).mul hlog)).sub (continuousOn_const.mul (hlog.pow 3))
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 2), HasDerivAt g 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have h1t_pos : 0 < 1 - t := by linarith [ht.2]
    have h1t0 : 1 - t ≠ 0 := ne_of_gt h1t_pos
    have hfrac_ne : -t / (1 - t) ≠ 0 := div_ne_zero (neg_ne_zero.mpr ht0) h1t0
    have hfrac_abs : |-t / (1 - t)| < 1 := by
      rw [abs_div, abs_neg, abs_of_pos ht.1, abs_of_pos h1t_pos, div_lt_one h1t_pos]
      linarith [ht.2]
    have hd_frac : HasDerivAt (fun s : ℝ => -s / (1 - s)) (-1 / (1 - t) ^ 2) t := by
      refine ((hasDerivAt_neg t).fun_div (hasDerivAt_one_sub t) h1t0).congr_deriv ?_
      ring
    have hd_log1 : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - t)) t := by
      refine ((Real.hasDerivAt_log h1t0).comp t (hasDerivAt_one_sub t)).congr_deriv ?_
      field_simp [h1t0]
    have hd1 : HasDerivAt Li3 (Li2 t / t) t :=
      hasDerivAt_Li3 (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩) ht0
    have hd2 : HasDerivAt (fun s => Li3 (1 - s)) ((Li2 (1 - t) / (1 - t)) * (-1)) t :=
      (hasDerivAt_Li3 (abs_lt.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩) h1t0).comp t
        (hasDerivAt_one_sub t)
    have hd3 : HasDerivAt (fun s => Li3 (-s / (1 - s)))
        ((Li2 (-t / (1 - t)) / (-t / (1 - t))) * (-1 / (1 - t) ^ 2)) t :=
      (hasDerivAt_Li3 hfrac_abs hfrac_ne).comp (h := fun s : ℝ => -s / (1 - s)) t hd_frac
    have hd4 : HasDerivAt (fun s => (Real.pi ^ 2 / 6) * Real.log (1 - s))
        ((Real.pi ^ 2 / 6) * (-1 / (1 - t))) t := hd_log1.const_mul _
    have hd5 : HasDerivAt (fun s => (1 / 2 : ℝ) * (Real.log s * Real.log (1 - s)) * Real.log (1 - s))
        (((1 / 2 : ℝ) * (t⁻¹ * Real.log (1 - t) + Real.log t * (-1 / (1 - t)))) * Real.log (1 - t) +
          ((1 / 2 : ℝ) * (Real.log t * Real.log (1 - t))) * (-1 / (1 - t))) t :=
      ((((Real.hasDerivAt_log ht0).fun_mul hd_log1).const_mul (1 / 2)).fun_mul hd_log1)
    have hd6 : HasDerivAt (fun s => (1 / 6 : ℝ) * (Real.log (1 - s)) ^ 3)
        ((1 / 6 : ℝ) * (3 * (Real.log (1 - t)) ^ 2 * (-1 / (1 - t)))) t :=
      (hd_log1.fun_pow 3).const_mul _
    refine (((((hd1.fun_add hd2).fun_add hd3).fun_sub hd4).fun_add hd5).fun_sub hd6).congr_deriv ?_
    have heul := Li2_euler (le_of_lt ht.1) (le_of_lt ht.2)
    have hlan := Li2_landen (le_of_lt ht.1) (le_of_lt ht.2)
    have hdecomp :
        Li2 t / t + Li2 (1 - t) / (1 - t) * -1 +
            Li2 (-t / (1 - t)) / (-t / (1 - t)) * (-1 / (1 - t) ^ 2) -
          Real.pi ^ 2 / 6 * (-1 / (1 - t)) +
          (1 / 2 * (t⁻¹ * Real.log (1 - t) + Real.log t * (-1 / (1 - t))) * Real.log (1 - t) +
            1 / 2 * (Real.log t * Real.log (1 - t)) * (-1 / (1 - t))) -
          1 / 6 * (3 * Real.log (1 - t) ^ 2 * (-1 / (1 - t))) =
        (Li2 t + Li2 (-t / (1 - t)) + Real.log (1 - t) ^ 2 / 2) / t +
          ((Li2 t + Li2 (-t / (1 - t)) + Real.log (1 - t) ^ 2 / 2) -
            (Li2 t + Li2 (1 - t) + Real.log t * Real.log (1 - t) - Real.pi ^ 2 / 6)) / (1 - t) := by
      field_simp [ht0, h1t0]
      ring
    rw [hdecomp, hlan, heul]
    ring
  have h0 : g 0 = Li3 1 := by simp [g, Li3_zero]
  have h12 := const_of_hasDerivAt_zero hcont hderiv (1 / 2) ⟨by norm_num, le_refl _⟩
  rw [h0] at h12
  dsimp only [g] at h12
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring,
    show -(1 / 2 : ℝ) / (1 / 2 : ℝ) = -1 by norm_num,
    Li3_neg_one, one_div, Real.log_inv] at h12
  linarith

/-! Smooth real extensions `Li2E`, `Li3E`, `Li4E` on `(-∞, 1]` -/

private noncomputable def Li2E (x : ℝ) : ℝ :=
  if x < -1 then -Li2 (1 / x) - (Real.log (-x)) ^ 2 / 2 - Real.pi ^ 2 / 6 else Li2 x

private noncomputable def Li3E (x : ℝ) : ℝ :=
  if x < -1 then Li3 (1 / x) - (Real.log (-x)) ^ 3 / 6 - Real.pi ^ 2 * Real.log (-x) / 6 else Li3 x

private noncomputable def Li4E (x : ℝ) : ℝ :=
  if x < -1 then
    -Li4 (1 / x) - (Real.log (-x)) ^ 4 / 24 - Real.pi ^ 2 * (Real.log (-x)) ^ 2 / 12 -
      7 * Real.pi ^ 4 / 360
  else Li4 x

private lemma Li2E_of_lt {x : ℝ} (h : x < -1) :
    Li2E x = -Li2 (1 / x) - (Real.log (-x)) ^ 2 / 2 - Real.pi ^ 2 / 6 := by
  unfold Li2E
  split_ifs
  rfl

private lemma Li2E_of_ge {x : ℝ} (h : -1 ≤ x) : Li2E x = Li2 x := by
  unfold Li2E
  split_ifs with hlt
  · exact absurd hlt (not_lt.mpr h)
  · rfl

private lemma Li2E_of_le {x : ℝ} (h : x ≤ -1) :
    Li2E x = -Li2 (1 / x) - (Real.log (-x)) ^ 2 / 2 - Real.pi ^ 2 / 6 := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · rw [Li2E_of_ge (le_refl _)]
    norm_num [Li2_neg_one]
    ring
  · exact Li2E_of_lt hlt

private lemma Li3E_of_lt {x : ℝ} (h : x < -1) :
    Li3E x = Li3 (1 / x) - (Real.log (-x)) ^ 3 / 6 - Real.pi ^ 2 * Real.log (-x) / 6 := by
  unfold Li3E
  split_ifs
  rfl

private lemma Li3E_of_ge {x : ℝ} (h : -1 ≤ x) : Li3E x = Li3 x := by
  unfold Li3E
  split_ifs with hlt
  · exact absurd hlt (not_lt.mpr h)
  · rfl

private lemma Li3E_of_le {x : ℝ} (h : x ≤ -1) :
    Li3E x = Li3 (1 / x) - (Real.log (-x)) ^ 3 / 6 - Real.pi ^ 2 * Real.log (-x) / 6 := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · rw [Li3E_of_ge (le_refl _)]
    norm_num
  · exact Li3E_of_lt hlt

private lemma Li4E_of_lt {x : ℝ} (h : x < -1) :
    Li4E x = -Li4 (1 / x) - (Real.log (-x)) ^ 4 / 24 - Real.pi ^ 2 * (Real.log (-x)) ^ 2 / 12 -
      7 * Real.pi ^ 4 / 360 := by
  unfold Li4E
  split_ifs
  rfl

private lemma Li4E_of_ge {x : ℝ} (h : -1 ≤ x) : Li4E x = Li4 x := by
  unfold Li4E
  split_ifs with hlt
  · exact absurd hlt (not_lt.mpr h)
  · rfl

private lemma Li4E_of_le {x : ℝ} (h : x ≤ -1) :
    Li4E x = -Li4 (1 / x) - (Real.log (-x)) ^ 4 / 24 - Real.pi ^ 2 * (Real.log (-x)) ^ 2 / 12 -
      7 * Real.pi ^ 4 / 360 := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · rw [Li4E_of_ge (le_refl _)]
    norm_num [Li4_neg_one]
    ring
  · exact Li4E_of_lt hlt

private lemma continuousOn_Iic_one_glue {f : ℝ → ℝ}
    (h1 : ContinuousOn f (Set.Iic (-1))) (h2 : ContinuousOn f (Set.Icc (-1) 1)) :
    ContinuousOn f (Set.Iic 1) := by
  have hunion : Set.Iic (1 : ℝ) = Set.Iic (-1) ∪ Set.Icc (-1) 1 := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Icc]
    constructor
    · intro hx
      rcases le_total x (-1) with hle | hge
      · exact Or.inl hle
      · exact Or.inr ⟨hge, hx⟩
    · rintro (hle | ⟨_, hx⟩)
      · linarith
      · exact hx
  rw [hunion]
  intro x hx
  rcases hx with hle | hcc
  · rcases eq_or_lt_of_le (Set.mem_Iic.mp hle) with rfl | hlt
    · exact continuousWithinAt_union.mpr
        ⟨h1 (-1) (Set.mem_Iic.mpr (le_refl _)), h2 (-1) ⟨le_refl _, by norm_num⟩⟩
    · exact (h1 x hle).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (nhdsWithin_le_nhds (Iio_mem_nhds hlt))
          (fun y hy => Set.mem_Iic.mpr (le_of_lt hy)))
  · rcases eq_or_lt_of_le hcc.1 with rfl | hgt
    · exact continuousWithinAt_union.mpr
        ⟨h1 (-1) (Set.mem_Iic.mpr (le_refl _)), h2 (-1) ⟨le_refl _, by norm_num⟩⟩
    · have hmem : Set.Icc (-1 : ℝ) 1 ∈ nhdsWithin x (Set.Iic (-1) ∪ Set.Icc (-1) 1) := by
        rw [← hunion]
        exact Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Iic 1) (Ioi_mem_nhds hgt))
          (fun y hy => ⟨le_of_lt hy.2, hy.1⟩)
      exact (h2 x hcc).mono_of_mem_nhdsWithin hmem

private lemma continuousOn_inv_Iic_neg_one :
    ContinuousOn (fun x : ℝ => 1 / x) (Set.Iic (-1)) :=
  continuousOn_const.div continuousOn_id (fun x hx => by linarith [Set.mem_Iic.mp hx])

private lemma mapsTo_inv_Iic_neg_one :
    Set.MapsTo (fun x : ℝ => 1 / x) (Set.Iic (-1)) (Set.Icc (-1) 1) := by
  intro x hx
  have hx_neg : x < 0 := by linarith [Set.mem_Iic.mp hx]
  refine ⟨?_, ?_⟩
  · rw [le_div_iff_of_neg hx_neg]
    linarith [Set.mem_Iic.mp hx]
  · rw [div_le_iff_of_neg hx_neg]
    linarith [Set.mem_Iic.mp hx]

private lemma continuousOn_log_neg_Iic_neg_one :
    ContinuousOn (fun x : ℝ => Real.log (-x)) (Set.Iic (-1)) :=
  fun x hx => (Real.continuousAt_log (by linarith [Set.mem_Iic.mp hx])).comp
    continuousAt_neg |>.continuousWithinAt

private lemma continuousOn_Li2E : ContinuousOn Li2E (Set.Iic 1) := by
  refine continuousOn_Iic_one_glue ?_ ?_
  · refine ((((continuousOn_Li2.comp continuousOn_inv_Iic_neg_one mapsTo_inv_Iic_neg_one).neg).sub
      ((continuousOn_log_neg_Iic_neg_one.pow 2).div_const 2)).sub continuousOn_const).congr
      (fun x hx => Li2E_of_le hx)
  · exact continuousOn_Li2.congr (fun x hx => Li2E_of_ge hx.1)

private lemma continuousOn_Li3E : ContinuousOn Li3E (Set.Iic 1) := by
  refine continuousOn_Iic_one_glue ?_ ?_
  · refine ((((continuousOn_Li3.comp continuousOn_inv_Iic_neg_one mapsTo_inv_Iic_neg_one)).sub
      ((continuousOn_log_neg_Iic_neg_one.pow 3).div_const 6)).sub
      ((continuousOn_const.mul continuousOn_log_neg_Iic_neg_one).div_const 6)).congr
      (fun x hx => Li3E_of_le hx)
  · exact continuousOn_Li3.congr (fun x hx => Li3E_of_ge hx.1)

private lemma continuousOn_Li4E : ContinuousOn Li4E (Set.Iic 1) := by
  refine continuousOn_Iic_one_glue ?_ ?_
  · refine (((((continuousOn_Li4.comp continuousOn_inv_Iic_neg_one mapsTo_inv_Iic_neg_one).neg).sub
      ((continuousOn_log_neg_Iic_neg_one.pow 4).div_const 24)).sub
      ((continuousOn_const.mul (continuousOn_log_neg_Iic_neg_one.pow 2)).div_const 12)).sub
      continuousOn_const).congr (fun x hx => Li4E_of_le hx)
  · exact continuousOn_Li4.congr (fun x hx => Li4E_of_ge hx.1)

private lemma hasDerivAt_one_div {x : ℝ} (hx0 : x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
  have h := (hasDerivAt_inv hx0).congr_deriv (by ring : -(x ^ 2)⁻¹ = -1 / x ^ 2)
  simpa only [one_div] using h

private lemma hasDerivAt_Li2E {x : ℝ} (hx1 : x < 1) (hx0 : x ≠ 0) (hxm1 : x ≠ -1) :
    HasDerivAt Li2E (-Real.log (1 - x) / x) x := by
  rcases lt_or_gt_of_ne hxm1 with hlt | hgt
  · have hev : Li2E =ᶠ[nhds x] fun y => -Li2 (1 / y) - (Real.log (-y)) ^ 2 / 2 - Real.pi ^ 2 / 6 :=
      Filter.eventually_of_mem (Iio_mem_nhds hlt) (fun y hy => Li2E_of_lt hy)
    have hinv_abs : |1 / x| < 1 := by
      rw [abs_div, abs_one, abs_of_neg (by linarith), div_lt_one (by linarith)]
      linarith
    have hinv_ne : 1 / x ≠ 0 := one_div_ne_zero hx0
    have hd_log : HasDerivAt (fun y : ℝ => Real.log (-y)) (1 / x) x := by
      refine ((Real.hasDerivAt_log (by linarith : -x ≠ 0)).comp x (hasDerivAt_neg x)).congr_deriv ?_
      field_simp [hx0]
    have hd1 : HasDerivAt (fun y => -Li2 (1 / y))
        (-((-Real.log (1 - 1 / x) / (1 / x)) * (-1 / x ^ 2))) x :=
      ((hasDerivAt_Li2 hinv_abs hinv_ne).comp x (hasDerivAt_one_div hx0)).neg
    have hd2 : HasDerivAt (fun y => (Real.log (-y)) ^ 2 / 2)
        ((2 * (Real.log (-x)) ^ 1 * (1 / x)) / 2) x :=
      (hd_log.fun_pow 2).div_const 2
    refine ((hd1.fun_sub hd2).fun_sub (hasDerivAt_const x _)).congr_of_eventuallyEq hev |>.congr_deriv ?_
    have hlog : Real.log (1 - x) = Real.log (1 - 1 / x) + Real.log (-x) := by
      have h1 : 1 - 1 / x > 0 := by
        have : 1 / x < 0 := div_neg_of_pos_of_neg zero_lt_one (by linarith)
        linarith
      rw [← Real.log_mul (ne_of_gt h1) (by linarith : -x ≠ 0)]
      congr 1
      field_simp [hx0]
      ring
    rw [hlog]
    field_simp [hx0]
    ring
  · have hev : Li2E =ᶠ[nhds x] Li2 :=
      Filter.eventually_of_mem (Ioi_mem_nhds hgt) (fun y hy => Li2E_of_ge (le_of_lt hy))
    exact (hasDerivAt_Li2 (abs_lt.mpr ⟨hgt, hx1⟩) hx0).congr_of_eventuallyEq hev

private lemma hasDerivAt_Li3E {x : ℝ} (hx1 : x < 1) (hx0 : x ≠ 0) (hxm1 : x ≠ -1) :
    HasDerivAt Li3E (Li2E x / x) x := by
  rcases lt_or_gt_of_ne hxm1 with hlt | hgt
  · have hev : Li3E =ᶠ[nhds x]
        fun y => Li3 (1 / y) - (Real.log (-y)) ^ 3 / 6 - Real.pi ^ 2 * Real.log (-y) / 6 :=
      Filter.eventually_of_mem (Iio_mem_nhds hlt) (fun y hy => Li3E_of_lt hy)
    have hinv_abs : |1 / x| < 1 := by
      rw [abs_div, abs_one, abs_of_neg (by linarith), div_lt_one (by linarith)]
      linarith
    have hinv_ne : 1 / x ≠ 0 := one_div_ne_zero hx0
    have hd_log : HasDerivAt (fun y : ℝ => Real.log (-y)) (1 / x) x := by
      refine ((Real.hasDerivAt_log (by linarith : -x ≠ 0)).comp x (hasDerivAt_neg x)).congr_deriv ?_
      field_simp [hx0]
    have hd1 : HasDerivAt (fun y => Li3 (1 / y))
        ((Li2 (1 / x) / (1 / x)) * (-1 / x ^ 2)) x :=
      (hasDerivAt_Li3 hinv_abs hinv_ne).comp x (hasDerivAt_one_div hx0)
    have hd2 : HasDerivAt (fun y => (Real.log (-y)) ^ 3 / 6)
        ((3 * (Real.log (-x)) ^ 2 * (1 / x)) / 6) x :=
      (hd_log.fun_pow 3).div_const 6
    have hd3 : HasDerivAt (fun y => Real.pi ^ 2 * Real.log (-y) / 6)
        ((Real.pi ^ 2 * (1 / x)) / 6) x :=
      (hd_log.const_mul _).div_const 6
    refine ((hd1.fun_sub hd2).fun_sub hd3).congr_of_eventuallyEq hev |>.congr_deriv ?_
    rw [Li2E_of_lt hlt]
    field_simp [hx0]
    ring
  · have hev : Li3E =ᶠ[nhds x] Li3 :=
      Filter.eventually_of_mem (Ioi_mem_nhds hgt) (fun y hy => Li3E_of_ge (le_of_lt hy))
    rw [Li2E_of_ge (le_of_lt hgt)]
    exact (hasDerivAt_Li3 (abs_lt.mpr ⟨hgt, hx1⟩) hx0).congr_of_eventuallyEq hev

private lemma hasDerivAt_Li4E {x : ℝ} (hx1 : x < 1) (hx0 : x ≠ 0) (hxm1 : x ≠ -1) :
    HasDerivAt Li4E (Li3E x / x) x := by
  rcases lt_or_gt_of_ne hxm1 with hlt | hgt
  · have hev : Li4E =ᶠ[nhds x] fun y =>
        -Li4 (1 / y) - (Real.log (-y)) ^ 4 / 24 - Real.pi ^ 2 * (Real.log (-y)) ^ 2 / 12 -
          7 * Real.pi ^ 4 / 360 :=
      Filter.eventually_of_mem (Iio_mem_nhds hlt) (fun y hy => Li4E_of_lt hy)
    have hinv_abs : |1 / x| < 1 := by
      rw [abs_div, abs_one, abs_of_neg (by linarith), div_lt_one (by linarith)]
      linarith
    have hinv_ne : 1 / x ≠ 0 := one_div_ne_zero hx0
    have hd_log : HasDerivAt (fun y : ℝ => Real.log (-y)) (1 / x) x := by
      refine ((Real.hasDerivAt_log (by linarith : -x ≠ 0)).comp x (hasDerivAt_neg x)).congr_deriv ?_
      field_simp [hx0]
    have hd1 : HasDerivAt (fun y => -Li4 (1 / y))
        (-((Li3 (1 / x) / (1 / x)) * (-1 / x ^ 2))) x :=
      ((hasDerivAt_Li4 hinv_abs hinv_ne).comp x (hasDerivAt_one_div hx0)).neg
    have hd2 : HasDerivAt (fun y => (Real.log (-y)) ^ 4 / 24)
        ((4 * (Real.log (-x)) ^ 3 * (1 / x)) / 24) x :=
      (hd_log.fun_pow 4).div_const 24
    have hd3 : HasDerivAt (fun y => Real.pi ^ 2 * (Real.log (-y)) ^ 2 / 12)
        ((Real.pi ^ 2 * (2 * (Real.log (-x)) ^ 1 * (1 / x))) / 12) x :=
      ((hd_log.fun_pow 2).const_mul _).div_const 12
    refine (((hd1.fun_sub hd2).fun_sub hd3).fun_sub (hasDerivAt_const x _)).congr_of_eventuallyEq hev |>.congr_deriv ?_
    rw [Li3E_of_lt hlt]
    field_simp [hx0]
    ring
  · have hev : Li4E =ᶠ[nhds x] Li4 :=
      Filter.eventually_of_mem (Ioi_mem_nhds hgt) (fun y hy => Li4E_of_ge (le_of_lt hy))
    rw [Li3E_of_ge (le_of_lt hgt)]
    exact (hasDerivAt_Li4 (abs_lt.mpr ⟨hgt, hx1⟩) hx0).congr_of_eventuallyEq hev

/-! Three-interval constancy principle on `[0, 1/3]` -/

private lemma const_on_Icc_third {g : ℝ → ℝ}
    (hcont : ContinuousOn g (Set.Icc 0 (1 / 3)))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 3), t ≠ 3 - 2 * Real.sqrt 2 → t ≠ 1 / 4 → HasDerivAt g 0 t) :
    ∀ t ∈ Set.Icc (0 : ℝ) (1 / 3), g t = g 0 := by
  set r₁ : ℝ := 3 - 2 * Real.sqrt 2
  have hsq2_lo : (1.41 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsq2_hi : Real.sqrt 2 < (1.42 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hr1_pos : 0 < r₁ := by dsimp only [r₁]; linarith
  have hr1_lt : r₁ < 1 / 4 := by dsimp only [r₁]; linarith
  have hc1 : ∀ t ∈ Set.Icc 0 r₁, g t = g 0 :=
    const_of_hasDerivAt_zero
      (hcont.mono (Set.Icc_subset_Icc_right (by linarith)))
      (fun t ht => hderiv t ⟨ht.1, by linarith [ht.2]⟩ (ne_of_lt ht.2) (by linarith [ht.2]))
  have hc2 : ∀ t ∈ Set.Icc r₁ (1 / 4), g t = g r₁ :=
    const_of_hasDerivAt_zero
      (hcont.mono (Set.Icc_subset_Icc (le_of_lt hr1_pos) (by norm_num)))
      (fun t ht => hderiv t ⟨by linarith [ht.1], by linarith [ht.2]⟩ (ne_of_gt ht.1) (ne_of_lt ht.2))
  have hc3 : ∀ t ∈ Set.Icc (1 / 4) (1 / 3), g t = g (1 / 4) :=
    const_of_hasDerivAt_zero
      (hcont.mono (Set.Icc_subset_Icc (by norm_num) (le_refl _)))
      (fun t ht => hderiv t ⟨by linarith [ht.1], ht.2⟩ (by linarith [ht.1]) (ne_of_gt ht.1))
  have hgr1 : g r₁ = g 0 := hc1 r₁ ⟨le_of_lt hr1_pos, le_refl _⟩
  have hg14 : g (1 / 4) = g 0 := (hc2 (1 / 4) ⟨le_of_lt hr1_lt, le_refl _⟩).trans hgr1
  intro t ht
  rcases le_total t r₁ with h1 | h1
  · exact hc1 t ⟨ht.1, h1⟩
  · rcases le_total t (1 / 4) with h2 | h2
    · exact (hc2 t ⟨h1, h2⟩).trans hgr1
    · exact (hc3 t ⟨h2, ht.2⟩).trans hg14

/-! The 19-term functional equation family on `[0, 1/3]` -/

private structure Term where
  c : ℝ
  s : ℝ
  e2 : ℤ
  et : ℕ
  ey : ℤ
  ez : ℤ

private def T : Fin 19 → Term :=
  ![⟨  3,  1,  0, 2,  0,  0⟩,
    ⟨ -8,  1,  1, 2, -1,  0⟩,
    ⟨ -8,  1,  1, 2, -1, -1⟩,
    ⟨  6,  1,  2, 2, -2,  0⟩,
    ⟨ 16,  1,  1, 1,  0,  0⟩,
    ⟨-16,  1,  0, 1,  0,  0⟩,
    ⟨ 24,  1,  0, 1,  0, -1⟩,
    ⟨ -4,  1,  2, 1, -2,  1⟩,
    ⟨  4,  1,  0, 0, -2,  1⟩,
    ⟨  8,  1, -1, 0, -1,  0⟩,
    ⟨ 32,  1,  0, 0,  1,  0⟩,
    ⟨-24,  1, -1, 0,  1,  0⟩,
    ⟨  8,  1, -1, 0, -1,  1⟩,
    ⟨-32,  1,  0, 0, -1,  1⟩,
    ⟨-24,  1, -1, 0,  1, -1⟩,
    ⟨ -4, -1,  0, 2,  0, -1⟩,
    ⟨ 16, -1,  1, 1,  0, -1⟩,
    ⟨  8, -1,  0, 1,  0, -1⟩,
    ⟨ -4, -1,  2, 1, -2,  0⟩]

private noncomputable def evalTerm (τ : Term) (t : ℝ) : ℝ :=
  τ.s * (2 : ℝ) ^ τ.e2 * t ^ τ.et * (1 - t) ^ τ.ey * (1 - 2 * t) ^ τ.ez

private lemma continuousOn_evalTerm (τ : Term) : ContinuousOn (evalTerm τ) (Set.Icc 0 (1 / 3)) := by
  have h1 : ContinuousOn (fun t : ℝ => τ.s * (2 : ℝ) ^ τ.e2 * t ^ τ.et) (Set.Icc 0 (1 / 3)) := by
    fun_prop
  have h2 : ContinuousOn (fun t : ℝ => (1 - t) ^ τ.ey) (Set.Icc 0 (1 / 3)) :=
    (by fun_prop : ContinuousOn (fun t : ℝ => 1 - t) _).zpow₀ τ.ey
      (fun t ht => Or.inl (by linarith [ht.2]))
  have h3 : ContinuousOn (fun t : ℝ => (1 - 2 * t) ^ τ.ez) (Set.Icc 0 (1 / 3)) :=
    (by fun_prop : ContinuousOn (fun t : ℝ => 1 - 2 * t) _).zpow₀ τ.ez
      (fun t ht => Or.inl (by linarith [ht.2]))
  exact (h1.mul h2).mul h3

private lemma evalTerm_ne_zero (τ : Term) (hs : τ.s ≠ 0) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 3)) :
    evalTerm τ t ≠ 0 := by
  unfold evalTerm
  have h2 : (2 : ℝ) ^ τ.e2 ≠ 0 := zpow_ne_zero _ (by norm_num)
  have ht0 : t ^ τ.et ≠ 0 := pow_ne_zero _ (ne_of_gt ht.1)
  have hy : (1 - t) ^ τ.ey ≠ 0 := zpow_ne_zero _ (by linarith [ht.2])
  have hz : (1 - 2 * t) ^ τ.ez ≠ 0 := zpow_ne_zero _ (by linarith [ht.2])
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs h2) ht0) hy) hz

private lemma hasDerivAt_evalTerm (τ : Term) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 3)) :
    HasDerivAt (evalTerm τ)
      (evalTerm τ t * ((τ.et : ℝ) / t - (τ.ey : ℝ) / (1 - t) - 2 * (τ.ez : ℝ) / (1 - 2 * t))) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht.1
  have hy0 : 1 - t ≠ 0 := by linarith [ht.2]
  have hz0 : 1 - 2 * t ≠ 0 := by linarith [ht.2]
  have h1 : HasDerivAt (fun s : ℝ => τ.s * (2 : ℝ) ^ τ.e2 * s ^ τ.et)
      (τ.s * (2 : ℝ) ^ τ.e2 * ((τ.et : ℝ) * t ^ (τ.et - 1))) t :=
    (hasDerivAt_pow τ.et t).const_mul _
  have h2 : HasDerivAt (fun s : ℝ => (1 - s) ^ τ.ey)
      ((τ.ey : ℝ) * (1 - t) ^ (τ.ey - 1) * (-1)) t :=
    (hasDerivAt_zpow τ.ey (1 - t) (Or.inl hy0)).comp (h := fun s : ℝ => 1 - s) t (hasDerivAt_one_sub t)
  have h3 : HasDerivAt (fun s : ℝ => (1 - 2 * s) ^ τ.ez)
      ((τ.ez : ℝ) * (1 - 2 * t) ^ (τ.ez - 1) * (-2)) t :=
    (hasDerivAt_zpow τ.ez (1 - 2 * t) (Or.inl hz0)).comp (h := fun s : ℝ => 1 - 2 * s) t
      (hasDerivAt_one_sub_two_mul t)
  refine ((h1.fun_mul h2).fun_mul h3).congr_deriv ?_
  have hpow_t : (τ.et : ℝ) * t ^ (τ.et - 1) = t ^ τ.et * ((τ.et : ℝ) / t) := by
    cases h : τ.et with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp [ht0]
  have hpow_y : (1 - t) ^ (τ.ey - 1) = (1 - t) ^ τ.ey / (1 - t) := by
    rw [zpow_sub₀ hy0, zpow_one]
  have hpow_z : (1 - 2 * t) ^ (τ.ez - 1) = (1 - 2 * t) ^ τ.ez / (1 - 2 * t) := by
    rw [zpow_sub₀ hz0, zpow_one]
  rw [hpow_t, hpow_y, hpow_z]
  unfold evalTerm
  ring

private def log1mExps : Fin 19 → ℤ × ℤ × ℤ × ℤ × ℤ × ℤ :=
  ![( 0,  0,  1,  0,  1,  0),
    ( 0,  0, -1,  1,  1,  0),
    ( 0,  0, -1, -1,  0,  1),
    ( 0,  0, -2,  0,  1,  1),
    ( 0,  0,  0,  1,  0,  0),
    ( 0,  0,  1,  0,  0,  0),
    ( 0,  0,  0, -1,  0,  1),
    ( 0,  0, -2,  0,  0,  2),
    ( 0,  2, -2,  0,  0,  0),
    (-1,  0, -1,  1,  0,  0),
    ( 0,  1,  0,  0,  0,  0),
    (-1,  0,  0,  0,  1,  0),
    (-1,  0, -1,  0,  0,  0),
    ( 0,  1, -1,  0,  0,  0),
    (-1,  0,  0, -1,  0,  1),
    ( 0,  0,  2, -1,  0,  0),
    ( 0,  0,  0, -1,  0,  0),
    ( 0,  0,  1, -1,  0,  0),
    ( 0,  0, -2,  0,  2,  0)]

private lemma one_sub_evalTerm_eq (k : Fin 19) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 3)) :
    let e := log1mExps k
    1 - evalTerm (T k) t =
      (2 : ℝ) ^ e.1 * t ^ e.2.1 * (1 - t) ^ e.2.2.1 * (1 - 2 * t) ^ e.2.2.2.1 *
        (1 + t) ^ e.2.2.2.2.1 * (1 - 3 * t) ^ e.2.2.2.2.2 := by
  have hy0 : 1 - t ≠ 0 := by linarith [ht.2]
  have hz0 : 1 - 2 * t ≠ 0 := by linarith [ht.2]
  fin_cases k <;> (dsimp only; simp [T, log1mExps, evalTerm]; try grind)

private lemma evalTerm_lt_one (k : Fin 19) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 3)) :
    evalTerm (T k) t < 1 := by
  have h1 := one_sub_evalTerm_eq k ht
  have hpos : (0 : ℝ) < 1 - evalTerm (T k) t := by
    rw [h1]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (log1mExps k).1 := zpow_pos (by norm_num) _
    have ht0 : (0 : ℝ) < t ^ (log1mExps k).2.1 := zpow_pos ht.1 _
    have hy0 : (0 : ℝ) < (1 - t) ^ (log1mExps k).2.2.1 := zpow_pos (by linarith [ht.2]) _
    have hz0 : (0 : ℝ) < (1 - 2 * t) ^ (log1mExps k).2.2.2.1 := zpow_pos (by linarith [ht.2]) _
    have hw0 : (0 : ℝ) < (1 + t) ^ (log1mExps k).2.2.2.2.1 := zpow_pos (by linarith [ht.1]) _
    have hu0 : (0 : ℝ) < (1 - 3 * t) ^ (log1mExps k).2.2.2.2.2 := zpow_pos (by linarith [ht.2]) _
    positivity
  linarith

private lemma evalTerm_le_one (k : Fin 19) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (1 / 3)) :
    evalTerm (T k) t ≤ 1 := by
  rcases eq_or_lt_of_le ht.1 with rfl | ht0
  · fin_cases k <;> (dsimp only; norm_num [T, evalTerm])
  · rcases eq_or_lt_of_le ht.2 with rfl | ht13
    · fin_cases k <;> (dsimp only; norm_num [T, evalTerm])
    · exact le_of_lt (evalTerm_lt_one k ⟨ht0, ht13⟩)

private lemma T_s_eq_one_of_lt {k : Fin 19} (hk : k.1 < 15) : (T k).s = 1 := by
  fin_cases k <;> simp_all [T]

private lemma evalTerm_ne_neg_one (k : Fin 19) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 3))
    (hr1 : t ≠ 3 - 2 * Real.sqrt 2) (h14 : t ≠ 1 / 4) :
    evalTerm (T k) t ≠ -1 := by
  have hy_pos : 0 < 1 - t := by linarith [ht.2]
  have hz_pos : 0 < 1 - 2 * t := by linarith [ht.2]
  by_cases hk : k.1 < 15
  · have hpos : 0 < evalTerm (T k) t := by
      unfold evalTerm
      rw [T_s_eq_one_of_lt hk]
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (T k).e2 := zpow_pos (by norm_num) _
      have ht0 : (0 : ℝ) < t ^ (T k).et := pow_pos ht.1 _
      have hy0 : (0 : ℝ) < (1 - t) ^ (T k).ey := zpow_pos hy_pos _
      have hz0 : (0 : ℝ) < (1 - 2 * t) ^ (T k).ez := zpow_pos hz_pos _
      positivity
    linarith
  · fin_cases k <;> dsimp only at hk ⊢
    all_goals try (exfalso; omega)
    · rw [show evalTerm (T ⟨15, by decide⟩) t = -(t ^ 2 / (1 - 2 * t)) by
        simp [T, evalTerm, div_eq_mul_inv]]
      intro heq
      have h1 : t ^ 2 / (1 - 2 * t) = 1 := by linarith
      rw [div_eq_iff (ne_of_gt hz_pos)] at h1
      nlinarith [ht.1, ht.2]
    · rw [show evalTerm (T ⟨16, by decide⟩) t = -(2 * t / (1 - 2 * t)) by
        simp [T, evalTerm, div_eq_mul_inv]]
      intro heq
      have h1 : 2 * t / (1 - 2 * t) = 1 := by linarith
      rw [div_eq_iff (ne_of_gt hz_pos)] at h1
      exact h14 (by linarith)
    · rw [show evalTerm (T ⟨17, by decide⟩) t = -(t / (1 - 2 * t)) by
        simp [T, evalTerm, div_eq_mul_inv]]
      intro heq
      have h1 : t / (1 - 2 * t) = 1 := by linarith
      rw [div_eq_iff (ne_of_gt hz_pos)] at h1
      linarith [ht.2]
    · rw [show evalTerm (T ⟨18, by decide⟩) t = -(4 * t / (1 - t) ^ 2) by
        simp [T, evalTerm, div_eq_mul_inv]
        exact Or.inl (Or.inl (by norm_num))]
      intro heq
      have h1 : 4 * t / (1 - t) ^ 2 = 1 := by linarith
      rw [div_eq_iff (pow_ne_zero 2 (ne_of_gt hy_pos))] at h1
      have h2 : (3 - t) ^ 2 = (2 * Real.sqrt 2) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        linarith
      have h3 : 3 - t = 2 * Real.sqrt 2 := by
        have hsq : 0 ≤ 2 * Real.sqrt 2 := by positivity
        have h3t : 0 ≤ 3 - t := by linarith [ht.2]
        nlinarith
      exact hr1 (by linarith)

private lemma T_s_ne_zero (k : Fin 19) : (T k).s ≠ 0 := by
  fin_cases k <;> norm_num [T]

private lemma log_one_sub_evalTerm {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 3)) (k : Fin 19) :
    let e := log1mExps k
    Real.log (1 - evalTerm (T k) t) =
      (e.1 : ℝ) * Real.log 2 + (e.2.1 : ℝ) * Real.log t +
      (e.2.2.1 : ℝ) * Real.log (1 - t) + (e.2.2.2.1 : ℝ) * Real.log (1 - 2 * t) +
      (e.2.2.2.2.1 : ℝ) * Real.log (1 + t) + (e.2.2.2.2.2 : ℝ) * Real.log (1 - 3 * t) := by
  rw [one_sub_evalTerm_eq k ht]
  have h2 : (0 : ℝ) < 2 := by norm_num
  have ht0 : 0 < t := ht.1
  have hy0 : 0 < 1 - t := by linarith [ht.2]
  have hz0 : 0 < 1 - 2 * t := by linarith [ht.2]
  have hw0 : 0 < 1 + t := by linarith [ht.1]
  have hu0 : 0 < 1 - 3 * t := by linarith [ht.2]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_zpow]

private lemma hasDerivAt_Li2E_T (k : Fin 19) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 3))
    (hr1 : t ≠ 3 - 2 * Real.sqrt 2) (h14 : t ≠ 1 / 4) :
    HasDerivAt (fun s => Li2E (evalTerm (T k) s))
      (-Real.log (1 - evalTerm (T k) t) *
        (((T k).et : ℝ) / t - ((T k).ey : ℝ) / (1 - t) - 2 * ((T k).ez : ℝ) / (1 - 2 * t))) t := by
  have hne := evalTerm_ne_zero (T k) (T_s_ne_zero k) ht
  refine ((hasDerivAt_Li2E (evalTerm_lt_one k ht) hne (evalTerm_ne_neg_one k ht hr1 h14)).comp t
    (hasDerivAt_evalTerm (T k) ht)).congr_deriv ?_
  field_simp [hne]

private lemma hasDerivAt_Li3E_T (k : Fin 19) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 3))
    (hr1 : t ≠ 3 - 2 * Real.sqrt 2) (h14 : t ≠ 1 / 4) :
    HasDerivAt (fun s => Li3E (evalTerm (T k) s))
      (Li2E (evalTerm (T k) t) *
        (((T k).et : ℝ) / t - ((T k).ey : ℝ) / (1 - t) - 2 * ((T k).ez : ℝ) / (1 - 2 * t))) t := by
  have hne := evalTerm_ne_zero (T k) (T_s_ne_zero k) ht
  refine ((hasDerivAt_Li3E (evalTerm_lt_one k ht) hne (evalTerm_ne_neg_one k ht hr1 h14)).comp t
    (hasDerivAt_evalTerm (T k) ht)).congr_deriv ?_
  field_simp [hne]

private lemma hasDerivAt_Li4E_T (k : Fin 19) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 3))
    (hr1 : t ≠ 3 - 2 * Real.sqrt 2) (h14 : t ≠ 1 / 4) :
    HasDerivAt (fun s => Li4E (evalTerm (T k) s))
      (Li3E (evalTerm (T k) t) *
        (((T k).et : ℝ) / t - ((T k).ey : ℝ) / (1 - t) - 2 * ((T k).ez : ℝ) / (1 - 2 * t))) t := by
  have hne := evalTerm_ne_zero (T k) (T_s_ne_zero k) ht
  refine ((hasDerivAt_Li4E (evalTerm_lt_one k ht) hne (evalTerm_ne_neg_one k ht hr1 h14)).comp t
    (hasDerivAt_evalTerm (T k) ht)).congr_deriv ?_
  field_simp [hne]

private lemma continuousOn_Li2E_T (k : Fin 19) :
    ContinuousOn (fun t => Li2E (evalTerm (T k) t)) (Set.Icc 0 (1 / 3)) :=
  continuousOn_Li2E.comp (continuousOn_evalTerm (T k)) (fun _ ht => evalTerm_le_one k ht)

private lemma continuousOn_Li3E_T (k : Fin 19) :
    ContinuousOn (fun t => Li3E (evalTerm (T k) t)) (Set.Icc 0 (1 / 3)) :=
  continuousOn_Li3E.comp (continuousOn_evalTerm (T k)) (fun _ ht => evalTerm_le_one k ht)

private lemma continuousOn_Li4E_T (k : Fin 19) :
    ContinuousOn (fun t => Li4E (evalTerm (T k) t)) (Set.Icc 0 (1 / 3)) :=
  continuousOn_Li4E.comp (continuousOn_evalTerm (T k)) (fun _ ht => evalTerm_le_one k ht)

private lemma continuousOn_y : ContinuousOn (fun t : ℝ => Real.log (1 - t)) (Set.Icc 0 (1 / 3)) :=
  fun t ht => (Real.continuousAt_log (by linarith [ht.2])).comp
    (by fun_prop : ContinuousAt (fun s : ℝ => 1 - s) t) |>.continuousWithinAt

private lemma continuousOn_z :
    ContinuousOn (fun t : ℝ => Real.log (1 - 2 * t)) (Set.Icc 0 (1 / 3)) :=
  fun t ht => (Real.continuousAt_log (by linarith [ht.2])).comp
    (by fun_prop : ContinuousAt (fun s : ℝ => 1 - 2 * s) t) |>.continuousWithinAt

private lemma continuousOn_xy :
    ContinuousOn (fun t : ℝ => Real.log t * Real.log (1 - t)) (Set.Icc 0 (1 / 3)) := by
  simpa using continuousOn_log_mul_log_sub 1 (by norm_num) (1 / 3) (by norm_num) (by norm_num)

private lemma continuousOn_xz :
    ContinuousOn (fun t : ℝ => Real.log t * Real.log (1 - 2 * t)) (Set.Icc 0 (1 / 3)) :=
  continuousOn_log_mul_log_sub 2 (by norm_num) (1 / 3) (by norm_num) (by norm_num)

private lemma hasDerivAt_y {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 3)) :
    HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - t)) t := by
  have hy0 : 1 - t ≠ 0 := by linarith [ht.2]
  refine ((Real.hasDerivAt_log hy0).comp t (hasDerivAt_one_sub t)).congr_deriv ?_
  field_simp [hy0]

private lemma hasDerivAt_z {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (1 / 3)) :
    HasDerivAt (fun s : ℝ => Real.log (1 - 2 * s)) (-2 / (1 - 2 * t)) t := by
  have hz0 : 1 - 2 * t ≠ 0 := by linarith [ht.2]
  refine ((Real.hasDerivAt_log hz0).comp t (hasDerivAt_one_sub_two_mul t)).congr_deriv ?_
  field_simp [hz0]

private lemma sum_Fin19_expand (f : Fin 19 → ℝ) :
    ∑ k : Fin 19, f k =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 +
      f 10 + f 11 + f 12 + f 13 + f 14 + f 15 + f 16 + f 17 + f 18 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, ← add_assoc]
  rfl

private lemma T_all :
    T 0 = ⟨3, 1, 0, 2, 0, 0⟩ ∧ T 1 = ⟨-8, 1, 1, 2, -1, 0⟩ ∧
    T 2 = ⟨-8, 1, 1, 2, -1, -1⟩ ∧ T 3 = ⟨6, 1, 2, 2, -2, 0⟩ ∧
    T 4 = ⟨16, 1, 1, 1, 0, 0⟩ ∧ T 5 = ⟨-16, 1, 0, 1, 0, 0⟩ ∧
    T 6 = ⟨24, 1, 0, 1, 0, -1⟩ ∧ T 7 = ⟨-4, 1, 2, 1, -2, 1⟩ ∧
    T 8 = ⟨4, 1, 0, 0, -2, 1⟩ ∧ T 9 = ⟨8, 1, -1, 0, -1, 0⟩ ∧
    T 10 = ⟨32, 1, 0, 0, 1, 0⟩ ∧ T 11 = ⟨-24, 1, -1, 0, 1, 0⟩ ∧
    T 12 = ⟨8, 1, -1, 0, -1, 1⟩ ∧ T 13 = ⟨-32, 1, 0, 0, -1, 1⟩ ∧
    T 14 = ⟨-24, 1, -1, 0, 1, -1⟩ ∧ T 15 = ⟨-4, -1, 0, 2, 0, -1⟩ ∧
    T 16 = ⟨16, -1, 1, 1, 0, -1⟩ ∧ T 17 = ⟨8, -1, 0, 1, 0, -1⟩ ∧
    T 18 = ⟨-4, -1, 2, 1, -2, 0⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma log1mExps_all :
    log1mExps 0 = (0, 0, 1, 0, 1, 0) ∧ log1mExps 1 = (0, 0, -1, 1, 1, 0) ∧
    log1mExps 2 = (0, 0, -1, -1, 0, 1) ∧ log1mExps 3 = (0, 0, -2, 0, 1, 1) ∧
    log1mExps 4 = (0, 0, 0, 1, 0, 0) ∧ log1mExps 5 = (0, 0, 1, 0, 0, 0) ∧
    log1mExps 6 = (0, 0, 0, -1, 0, 1) ∧ log1mExps 7 = (0, 0, -2, 0, 0, 2) ∧
    log1mExps 8 = (0, 2, -2, 0, 0, 0) ∧ log1mExps 9 = (-1, 0, -1, 1, 0, 0) ∧
    log1mExps 10 = (0, 1, 0, 0, 0, 0) ∧ log1mExps 11 = (-1, 0, 0, 0, 1, 0) ∧
    log1mExps 12 = (-1, 0, -1, 0, 0, 0) ∧ log1mExps 13 = (0, 1, -1, 0, 0, 0) ∧
    log1mExps 14 = (-1, 0, 0, -1, 0, 1) ∧ log1mExps 15 = (0, 0, 2, -1, 0, 0) ∧
    log1mExps 16 = (0, 0, 0, -1, 0, 0) ∧ log1mExps 17 = (0, 0, 1, -1, 0, 0) ∧
    log1mExps 18 = (0, 0, -2, 0, 2, 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma evalTerm_zero_vals :
    evalTerm (T 0) 0 = 0 ∧ evalTerm (T 1) 0 = 0 ∧ evalTerm (T 2) 0 = 0 ∧
    evalTerm (T 3) 0 = 0 ∧ evalTerm (T 4) 0 = 0 ∧ evalTerm (T 5) 0 = 0 ∧
    evalTerm (T 6) 0 = 0 ∧ evalTerm (T 7) 0 = 0 ∧ evalTerm (T 8) 0 = 1 ∧
    evalTerm (T 9) 0 = 1 / 2 ∧ evalTerm (T 10) 0 = 1 ∧ evalTerm (T 11) 0 = 1 / 2 ∧
    evalTerm (T 12) 0 = 1 / 2 ∧ evalTerm (T 13) 0 = 1 ∧ evalTerm (T 14) 0 = 1 / 2 ∧
    evalTerm (T 15) 0 = 0 ∧ evalTerm (T 16) 0 = 0 ∧ evalTerm (T 17) 0 = 0 ∧
    evalTerm (T 18) 0 = 0 := by
  rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
  rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18]
  unfold evalTerm
  norm_num

private lemma evalTerm_third_vals :
    evalTerm (T 0) (1 / 3) = 1 / 9 ∧ evalTerm (T 1) (1 / 3) = 1 / 3 ∧
    evalTerm (T 2) (1 / 3) = 1 ∧ evalTerm (T 3) (1 / 3) = 1 ∧
    evalTerm (T 4) (1 / 3) = 2 / 3 ∧ evalTerm (T 5) (1 / 3) = 1 / 3 ∧
    evalTerm (T 6) (1 / 3) = 1 ∧ evalTerm (T 7) (1 / 3) = 1 ∧
    evalTerm (T 8) (1 / 3) = 3 / 4 ∧ evalTerm (T 9) (1 / 3) = 3 / 4 ∧
    evalTerm (T 10) (1 / 3) = 2 / 3 ∧ evalTerm (T 11) (1 / 3) = 1 / 3 ∧
    evalTerm (T 12) (1 / 3) = 1 / 4 ∧ evalTerm (T 13) (1 / 3) = 1 / 2 ∧
    evalTerm (T 14) (1 / 3) = 1 ∧ evalTerm (T 15) (1 / 3) = -(1 / 3) ∧
    evalTerm (T 16) (1 / 3) = -2 ∧ evalTerm (T 17) (1 / 3) = -1 ∧
    evalTerm (T 18) (1 / 3) = -3 := by
  rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
  rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18]
  unfold evalTerm
  norm_num

/-! Weight-2 identities `M_xx, M_xy, M_xz, M_yy, M_yz, M_zz = 0` on `[0, 1/3]` -/

private noncomputable def M_xx (t : ℝ) : ℝ :=
  ∑ k : Fin 19, (T k).c * ((T k).et : ℝ) * ((T k).et : ℝ) * Li2E (evalTerm (T k) t)

private noncomputable def M_xy (t : ℝ) : ℝ :=
  (∑ k : Fin 19, (T k).c * ((T k).et : ℝ) * ((T k).ey : ℝ) * Li2E (evalTerm (T k) t)) -
    (-8 * (Real.log (1 - 2 * t)) ^ 2)

private noncomputable def M_xz (t : ℝ) : ℝ :=
  (∑ k : Fin 19, (T k).c * ((T k).et : ℝ) * ((T k).ez : ℝ) * Li2E (evalTerm (T k) t)) -
    (-16 * Real.log (1 - t) * Real.log (1 - 2 * t) + 12 * (Real.log (1 - 2 * t)) ^ 2)

private noncomputable def M_yy (t : ℝ) : ℝ :=
  (∑ k : Fin 19, (T k).c * ((T k).ey : ℝ) * ((T k).ey : ℝ) * Li2E (evalTerm (T k) t)) -
    (16 * (Real.log 2) ^ 2 - 64 * Real.log 2 * Real.log (1 - t) +
      32 * Real.log 2 * Real.log (1 - 2 * t) -
      16 * Real.log (1 - t) * Real.log (1 - 2 * t) + 16 * (Real.log (1 - 2 * t)) ^ 2)

private noncomputable def M_yz (t : ℝ) : ℝ :=
  (∑ k : Fin 19, (T k).c * ((T k).ey : ℝ) * ((T k).ez : ℝ) * Li2E (evalTerm (T k) t)) -
    (-8 * (Real.log 2) ^ 2 + 32 * Real.log 2 * Real.log (1 - t) -
      32 * Real.log 2 * Real.log (1 - 2 * t) + 16 * Real.pi ^ 2 / 3 -
      16 * (Real.log t * Real.log (1 - 2 * t)) - 8 * (Real.log (1 - t)) ^ 2 +
      32 * Real.log (1 - t) * Real.log (1 - 2 * t) - 8 * (Real.log (1 - 2 * t)) ^ 2)

private noncomputable def M_zz (t : ℝ) : ℝ :=
  (∑ k : Fin 19, (T k).c * ((T k).ez : ℝ) * ((T k).ez : ℝ) * Li2E (evalTerm (T k) t)) -
    (8 * (Real.log 2) ^ 2 - 32 * Real.log 2 * Real.log (1 - t) +
      32 * Real.log 2 * Real.log (1 - 2 * t) - 6 * Real.pi ^ 2 -
      16 * (Real.log t * Real.log (1 - t)) + 24 * (Real.log t * Real.log (1 - 2 * t)) +
      16 * (Real.log (1 - t)) ^ 2 - 16 * Real.log (1 - t) * Real.log (1 - 2 * t) -
      6 * (Real.log (1 - 2 * t)) ^ 2)

private lemma M_xx_eq_zero : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 3), M_xx t = 0 := by
  have hcont : ContinuousOn M_xx (Set.Icc 0 (1 / 3)) :=
    continuousOn_finsetSum _ (fun k _ => continuousOn_const.mul (continuousOn_Li2E_T k))
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 3), t ≠ 3 - 2 * Real.sqrt 2 → t ≠ 1 / 4 →
      HasDerivAt M_xx 0 t := by
    intro t ht hr1 h14
    refine (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_Li2E_T k ht hr1 h14).const_mul _)).congr_deriv ?_
    rw [sum_Fin19_expand]
    simp only [log_one_sub_evalTerm ht]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rcases log1mExps_all with ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18,
      l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18]
    norm_num
    ring
  have h0 : M_xx 0 = 0 := by
    unfold M_xx
    rw [sum_Fin19_expand]
    rcases evalTerm_zero_vals with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      Li2E_of_ge (by norm_num : (-1 : ℝ) ≤ 0), Li2_zero]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18]
    norm_num
  intro t ht
  rw [const_on_Icc_third hcont hderiv t ht, h0]

private lemma M_xy_eq_zero : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 3), M_xy t = 0 := by
  have hcont : ContinuousOn M_xy (Set.Icc 0 (1 / 3)) :=
    (continuousOn_finsetSum _ (fun k _ => continuousOn_const.mul (continuousOn_Li2E_T k))).sub
      (continuousOn_const.mul (continuousOn_z.pow 2))
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 3), t ≠ 3 - 2 * Real.sqrt 2 → t ≠ 1 / 4 →
      HasDerivAt M_xy 0 t := by
    intro t ht hr1 h14
    have hd1 := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_Li2E_T k ht hr1 h14).const_mul ((T k).c * ((T k).et : ℝ) * ((T k).ey : ℝ)))
    have hd2 := ((hasDerivAt_z ht).fun_pow 2).const_mul (-8 : ℝ)
    refine (hd1.fun_sub hd2).congr_deriv ?_
    rw [sum_Fin19_expand]
    simp only [log_one_sub_evalTerm ht]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rcases log1mExps_all with ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18,
      l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18]
    norm_num
    ring
  have h0 : M_xy 0 = 0 := by
    unfold M_xy
    rw [sum_Fin19_expand]
    rcases evalTerm_zero_vals with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      Li2E_of_ge (by norm_num : (-1 : ℝ) ≤ 0), Li2_zero]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18]
    norm_num
  intro t ht
  rw [const_on_Icc_third hcont hderiv t ht, h0]

private lemma M_xz_eq_zero : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 3), M_xz t = 0 := by
  have hcont : ContinuousOn M_xz (Set.Icc 0 (1 / 3)) :=
    (continuousOn_finsetSum _ (fun k _ => continuousOn_const.mul (continuousOn_Li2E_T k))).sub
      (((continuousOn_const.mul continuousOn_y).mul continuousOn_z).add
        (continuousOn_const.mul (continuousOn_z.pow 2)))
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 3), t ≠ 3 - 2 * Real.sqrt 2 → t ≠ 1 / 4 →
      HasDerivAt M_xz 0 t := by
    intro t ht hr1 h14
    have hd1 := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_Li2E_T k ht hr1 h14).const_mul ((T k).c * ((T k).et : ℝ) * ((T k).ez : ℝ)))
    have hd2 := (((hasDerivAt_y ht).const_mul (-16 : ℝ)).fun_mul (hasDerivAt_z ht)).fun_add
      (((hasDerivAt_z ht).fun_pow 2).const_mul (12 : ℝ))
    refine (hd1.fun_sub hd2).congr_deriv ?_
    rw [sum_Fin19_expand]
    simp only [log_one_sub_evalTerm ht]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rcases log1mExps_all with ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18,
      l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18]
    norm_num
    ring
  have h0 : M_xz 0 = 0 := by
    unfold M_xz
    rw [sum_Fin19_expand]
    rcases evalTerm_zero_vals with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      Li2E_of_ge (by norm_num : (-1 : ℝ) ≤ 0), Li2_zero]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18]
    norm_num
  intro t ht
  rw [const_on_Icc_third hcont hderiv t ht, h0]

private lemma M_yy_eq_zero : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 3), M_yy t = 0 := by
  have hcont : ContinuousOn M_yy (Set.Icc 0 (1 / 3)) :=
    (continuousOn_finsetSum _ (fun k _ => continuousOn_const.mul (continuousOn_Li2E_T k))).sub
      ((((continuousOn_const.sub (continuousOn_const.mul continuousOn_y)).add
        (continuousOn_const.mul continuousOn_z)).sub
        ((continuousOn_const.mul continuousOn_y).mul continuousOn_z)).add
        (continuousOn_const.mul (continuousOn_z.pow 2)))
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 3), t ≠ 3 - 2 * Real.sqrt 2 → t ≠ 1 / 4 →
      HasDerivAt M_yy 0 t := by
    intro t ht hr1 h14
    have hd1 := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_Li2E_T k ht hr1 h14).const_mul ((T k).c * ((T k).ey : ℝ) * ((T k).ey : ℝ)))
    have hdy := hasDerivAt_y ht
    have hdz := hasDerivAt_z ht
    have hd2 := ((((hasDerivAt_const t (16 * (Real.log 2) ^ 2)).fun_sub
      (hdy.const_mul (64 * Real.log 2))).fun_add
      (hdz.const_mul (32 * Real.log 2))).fun_sub
      ((hdy.const_mul (16 : ℝ)).fun_mul hdz)).fun_add
      ((hdz.fun_pow 2).const_mul (16 : ℝ))
    refine (hd1.fun_sub hd2).congr_deriv ?_
    rw [sum_Fin19_expand]
    simp only [log_one_sub_evalTerm ht]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rcases log1mExps_all with ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18,
      l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18]
    norm_num
    ring
  have h0 : M_yy 0 = 0 := by
    unfold M_yy
    rw [sum_Fin19_expand]
    rcases evalTerm_zero_vals with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      Li2E_of_ge (by norm_num : (-1 : ℝ) ≤ 0), Li2E_of_ge (by norm_num : (-1 : ℝ) ≤ 1),
      Li2E_of_ge (by norm_num : (-1 : ℝ) ≤ 1 / 2), Li2_zero, Li2_one, Li2_half]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18]
    norm_num
    ring
  intro t ht
  rw [const_on_Icc_third hcont hderiv t ht, h0]

private lemma M_yz_eq_zero : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 3), M_yz t = 0 := by
  have hcont : ContinuousOn M_yz (Set.Icc 0 (1 / 3)) :=
    (continuousOn_finsetSum _ (fun k _ => continuousOn_const.mul (continuousOn_Li2E_T k))).sub
      (((((((continuousOn_const.add (continuousOn_const.mul continuousOn_y)).sub
        (continuousOn_const.mul continuousOn_z)).add continuousOn_const).sub
        (continuousOn_const.mul continuousOn_xz)).sub
        (continuousOn_const.mul (continuousOn_y.pow 2))).add
        ((continuousOn_const.mul continuousOn_y).mul continuousOn_z)).sub
        (continuousOn_const.mul (continuousOn_z.pow 2)))
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 3), t ≠ 3 - 2 * Real.sqrt 2 → t ≠ 1 / 4 →
      HasDerivAt M_yz 0 t := by
    intro t ht hr1 h14
    have hd1 := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_Li2E_T k ht hr1 h14).const_mul ((T k).c * ((T k).ey : ℝ) * ((T k).ez : ℝ)))
    have hdx := Real.hasDerivAt_log (ne_of_gt ht.1)
    have hdy := hasDerivAt_y ht
    have hdz := hasDerivAt_z ht
    have hd2 := (((((((hasDerivAt_const t (-8 * (Real.log 2) ^ 2)).fun_add
      (hdy.const_mul (32 * Real.log 2))).fun_sub (hdz.const_mul (32 * Real.log 2))).fun_add
      (hasDerivAt_const t (16 * Real.pi ^ 2 / 3))).fun_sub
      ((hdx.fun_mul hdz).const_mul (16 : ℝ))).fun_sub ((hdy.fun_pow 2).const_mul (8 : ℝ))).fun_add
      ((hdy.const_mul (32 : ℝ)).fun_mul hdz)).fun_sub ((hdz.fun_pow 2).const_mul (8 : ℝ))
    refine (hd1.fun_sub hd2).congr_deriv ?_
    rw [sum_Fin19_expand]
    simp only [log_one_sub_evalTerm ht]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rcases log1mExps_all with ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18,
      l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18]
    norm_num
    ring
  have h0 : M_yz 0 = 0 := by
    unfold M_yz
    rw [sum_Fin19_expand]
    rcases evalTerm_zero_vals with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      Li2E_of_ge (by norm_num : (-1 : ℝ) ≤ 0), Li2E_of_ge (by norm_num : (-1 : ℝ) ≤ 1),
      Li2E_of_ge (by norm_num : (-1 : ℝ) ≤ 1 / 2), Li2_zero, Li2_one, Li2_half]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18]
    norm_num
    ring
  intro t ht
  rw [const_on_Icc_third hcont hderiv t ht, h0]

private lemma M_zz_eq_zero : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 3), M_zz t = 0 := by
  have hcont : ContinuousOn M_zz (Set.Icc 0 (1 / 3)) :=
    (continuousOn_finsetSum _ (fun k _ => continuousOn_const.mul (continuousOn_Li2E_T k))).sub
      ((((((((continuousOn_const.sub (continuousOn_const.mul continuousOn_y)).add
        (continuousOn_const.mul continuousOn_z)).sub continuousOn_const).sub
        (continuousOn_const.mul continuousOn_xy)).add
        (continuousOn_const.mul continuousOn_xz)).add
        (continuousOn_const.mul (continuousOn_y.pow 2))).sub
        ((continuousOn_const.mul continuousOn_y).mul continuousOn_z)).sub
        (continuousOn_const.mul (continuousOn_z.pow 2)))
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 3), t ≠ 3 - 2 * Real.sqrt 2 → t ≠ 1 / 4 →
      HasDerivAt M_zz 0 t := by
    intro t ht hr1 h14
    have hd1 := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_Li2E_T k ht hr1 h14).const_mul ((T k).c * ((T k).ez : ℝ) * ((T k).ez : ℝ)))
    have hdx := Real.hasDerivAt_log (ne_of_gt ht.1)
    have hdy := hasDerivAt_y ht
    have hdz := hasDerivAt_z ht
    have hd2 := ((((((((hasDerivAt_const t (8 * (Real.log 2) ^ 2)).fun_sub
      (hdy.const_mul (32 * Real.log 2))).fun_add (hdz.const_mul (32 * Real.log 2))).fun_sub
      (hasDerivAt_const t (6 * Real.pi ^ 2))).fun_sub ((hdx.fun_mul hdy).const_mul (16 : ℝ))).fun_add
      ((hdx.fun_mul hdz).const_mul (24 : ℝ))).fun_add ((hdy.fun_pow 2).const_mul (16 : ℝ))).fun_sub
      ((hdy.const_mul (16 : ℝ)).fun_mul hdz)).fun_sub ((hdz.fun_pow 2).const_mul (6 : ℝ))
    refine (hd1.fun_sub hd2).congr_deriv ?_
    rw [sum_Fin19_expand]
    simp only [log_one_sub_evalTerm ht]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rcases log1mExps_all with ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18,
      l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18]
    norm_num
    ring
  have h0 : M_zz 0 = 0 := by
    unfold M_zz
    rw [sum_Fin19_expand]
    rcases evalTerm_zero_vals with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      Li2E_of_ge (by norm_num : (-1 : ℝ) ≤ 0), Li2E_of_ge (by norm_num : (-1 : ℝ) ≤ 1),
      Li2E_of_ge (by norm_num : (-1 : ℝ) ≤ 1 / 2), Li2_zero, Li2_one, Li2_half]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18]
    norm_num
    ring
  intro t ht
  rw [const_on_Icc_third hcont hderiv t ht, h0]

/-! Weight-3 identities `W3_x, W3_y, W3_z = 0` on `[0, 1/3]` -/

private noncomputable def W3_x (t : ℝ) : ℝ :=
  (∑ k : Fin 19, (T k).c * ((T k).et : ℝ) * Li3E (evalTerm (T k) t)) -
    (-8 * Real.log (1 - t) * (Real.log (1 - 2 * t)) ^ 2 + 4 * (Real.log (1 - 2 * t)) ^ 3)

private noncomputable def W3_y (t : ℝ) : ℝ :=
  (∑ k : Fin 19, (T k).c * ((T k).ey : ℝ) * Li3E (evalTerm (T k) t)) -
    (-32 * (Real.log 2) ^ 3 / 3 + 16 * (Real.log 2) ^ 2 * Real.log (1 - t) -
      8 * (Real.log 2) ^ 2 * Real.log (1 - 2 * t) + 16 * Real.log 2 * Real.pi ^ 2 / 3 -
      32 * Real.log 2 * (Real.log (1 - t)) ^ 2 +
      32 * Real.log 2 * Real.log (1 - t) * Real.log (1 - 2 * t) -
      16 * Real.log 2 * (Real.log (1 - 2 * t)) ^ 2 +
      16 * Real.pi ^ 2 * Real.log (1 - 2 * t) / 3 -
      8 * (Real.log t * Real.log (1 - 2 * t)) * Real.log (1 - 2 * t) -
      8 * (Real.log (1 - t)) ^ 2 * Real.log (1 - 2 * t) +
      16 * Real.log (1 - t) * (Real.log (1 - 2 * t)) ^ 2 -
      8 * (Real.log (1 - 2 * t)) ^ 3 / 3)

private noncomputable def W3_z (t : ℝ) : ℝ :=
  (∑ k : Fin 19, (T k).c * ((T k).ez : ℝ) * Li3E (evalTerm (T k) t)) -
    (16 * (Real.log 2) ^ 3 / 3 - 8 * (Real.log 2) ^ 2 * Real.log (1 - t) +
      8 * (Real.log 2) ^ 2 * Real.log (1 - 2 * t) - 8 * Real.log 2 * Real.pi ^ 2 / 3 +
      16 * Real.log 2 * (Real.log (1 - t)) ^ 2 -
      32 * Real.log 2 * Real.log (1 - t) * Real.log (1 - 2 * t) +
      16 * Real.log 2 * (Real.log (1 - 2 * t)) ^ 2 +
      16 * Real.pi ^ 2 * Real.log (1 - t) / 3 - 6 * Real.pi ^ 2 * Real.log (1 - 2 * t) -
      16 * (Real.log t * Real.log (1 - t)) * Real.log (1 - 2 * t) +
      12 * (Real.log t * Real.log (1 - 2 * t)) * Real.log (1 - 2 * t) -
      8 * (Real.log (1 - t)) ^ 3 / 3 + 16 * (Real.log (1 - t)) ^ 2 * Real.log (1 - 2 * t) -
      8 * Real.log (1 - t) * (Real.log (1 - 2 * t)) ^ 2 - 2 * (Real.log (1 - 2 * t)) ^ 3)

private lemma W3_x_eq_zero : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 3), W3_x t = 0 := by
  have hcont : ContinuousOn W3_x (Set.Icc 0 (1 / 3)) :=
    (continuousOn_finsetSum _ (fun k _ => continuousOn_const.mul (continuousOn_Li3E_T k))).sub
      (((continuousOn_const.mul continuousOn_y).mul (continuousOn_z.pow 2)).add
        (continuousOn_const.mul (continuousOn_z.pow 3)))
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 3), t ≠ 3 - 2 * Real.sqrt 2 → t ≠ 1 / 4 →
      HasDerivAt W3_x 0 t := by
    intro t ht hr1 h14
    have ht_cc : t ∈ Set.Icc (0 : ℝ) (1 / 3) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hd1 := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_Li3E_T k ht hr1 h14).const_mul ((T k).c * ((T k).et : ℝ)))
    have hdy := hasDerivAt_y ht
    have hdz := hasDerivAt_z ht
    have hd2 := ((hdy.const_mul (-8 : ℝ)).fun_mul (hdz.fun_pow 2)).fun_add
      ((hdz.fun_pow 3).const_mul (4 : ℝ))
    refine (hd1.fun_sub hd2).congr_deriv ?_
    have hxx := M_xx_eq_zero t ht_cc
    have hxy := M_xy_eq_zero t ht_cc
    have hxz := M_xz_eq_zero t ht_cc
    unfold M_xx at hxx
    unfold M_xy at hxy
    unfold M_xz at hxz
    have hsum :
        (∑ k : Fin 19, (T k).c * ((T k).et : ℝ) * (Li2E (evalTerm (T k) t) *
          (((T k).et : ℝ) / t - ((T k).ey : ℝ) / (1 - t) - 2 * ((T k).ez : ℝ) / (1 - 2 * t)))) =
        (∑ k : Fin 19, (T k).c * ((T k).et : ℝ) * ((T k).et : ℝ) * Li2E (evalTerm (T k) t)) / t -
        (∑ k : Fin 19, (T k).c * ((T k).et : ℝ) * ((T k).ey : ℝ) * Li2E (evalTerm (T k) t)) / (1 - t) -
        2 * (∑ k : Fin 19, (T k).c * ((T k).et : ℝ) * ((T k).ez : ℝ) * Li2E (evalTerm (T k) t)) / (1 - 2 * t) := by
      simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hsum]
    linear_combination hxx / t - hxy / (1 - t) - 2 * hxz / (1 - 2 * t)
  have h0 : W3_x 0 = 0 := by
    unfold W3_x
    rw [sum_Fin19_expand]
    rcases evalTerm_zero_vals with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      Li3E_of_ge (by norm_num : (-1 : ℝ) ≤ 0), Li3_zero]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18]
    norm_num
  intro t ht
  rw [const_on_Icc_third hcont hderiv t ht, h0]

private lemma W3_y_eq_zero : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 3), W3_y t = 0 := by
  have hcont : ContinuousOn W3_y (Set.Icc 0 (1 / 3)) :=
    (continuousOn_finsetSum _ (fun k _ => continuousOn_const.mul (continuousOn_Li3E_T k))).sub
      (((((((((((continuousOn_const.add (continuousOn_const.mul continuousOn_y)).sub
        (continuousOn_const.mul continuousOn_z)).add continuousOn_const).sub
        (continuousOn_const.mul (continuousOn_y.pow 2))).add
        ((continuousOn_const.mul continuousOn_y).mul continuousOn_z)).sub
        (continuousOn_const.mul (continuousOn_z.pow 2))).add
        ((continuousOn_const.mul continuousOn_z).div_const 3)).sub
        ((continuousOn_const.mul continuousOn_xz).mul continuousOn_z)).sub
        ((continuousOn_const.mul (continuousOn_y.pow 2)).mul continuousOn_z)).add
        ((continuousOn_const.mul continuousOn_y).mul (continuousOn_z.pow 2))).sub
        ((continuousOn_const.mul (continuousOn_z.pow 3)).div_const 3))
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 3), t ≠ 3 - 2 * Real.sqrt 2 → t ≠ 1 / 4 →
      HasDerivAt W3_y 0 t := by
    intro t ht hr1 h14
    have ht_cc : t ∈ Set.Icc (0 : ℝ) (1 / 3) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hd1 := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_Li3E_T k ht hr1 h14).const_mul ((T k).c * ((T k).ey : ℝ)))
    have hdx := Real.hasDerivAt_log (ne_of_gt ht.1)
    have hdy := hasDerivAt_y ht
    have hdz := hasDerivAt_z ht
    have hd2 := (((((((((((hasDerivAt_const t (-32 * (Real.log 2) ^ 3 / 3)).fun_add
      (hdy.const_mul (16 * (Real.log 2) ^ 2))).fun_sub (hdz.const_mul (8 * (Real.log 2) ^ 2))).fun_add
      (hasDerivAt_const t (16 * Real.log 2 * Real.pi ^ 2 / 3))).fun_sub
      ((hdy.fun_pow 2).const_mul (32 * Real.log 2))).fun_add
      ((hdy.const_mul (32 * Real.log 2)).fun_mul hdz)).fun_sub
      ((hdz.fun_pow 2).const_mul (16 * Real.log 2))).fun_add
      ((hdz.const_mul (16 * Real.pi ^ 2)).div_const 3)).fun_sub
      (((hdx.fun_mul hdz).const_mul (8 : ℝ)).fun_mul hdz)).fun_sub
      (((hdy.fun_pow 2).const_mul (8 : ℝ)).fun_mul hdz)).fun_add
      ((hdy.const_mul (16 : ℝ)).fun_mul (hdz.fun_pow 2))).fun_sub
      (((hdz.fun_pow 3).const_mul (8 : ℝ)).div_const 3)
    refine (hd1.fun_sub hd2).congr_deriv ?_
    have hxy := M_xy_eq_zero t ht_cc
    have hyy := M_yy_eq_zero t ht_cc
    have hyz := M_yz_eq_zero t ht_cc
    unfold M_xy at hxy
    unfold M_yy at hyy
    unfold M_yz at hyz
    have hsum :
        (∑ k : Fin 19, (T k).c * ((T k).ey : ℝ) * (Li2E (evalTerm (T k) t) *
          (((T k).et : ℝ) / t - ((T k).ey : ℝ) / (1 - t) - 2 * ((T k).ez : ℝ) / (1 - 2 * t)))) =
        (∑ k : Fin 19, (T k).c * ((T k).et : ℝ) * ((T k).ey : ℝ) * Li2E (evalTerm (T k) t)) / t -
        (∑ k : Fin 19, (T k).c * ((T k).ey : ℝ) * ((T k).ey : ℝ) * Li2E (evalTerm (T k) t)) / (1 - t) -
        2 * (∑ k : Fin 19, (T k).c * ((T k).ey : ℝ) * ((T k).ez : ℝ) * Li2E (evalTerm (T k) t)) / (1 - 2 * t) := by
      simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hsum]
    linear_combination hxy / t - hyy / (1 - t) - 2 * hyz / (1 - 2 * t)
  have h0 : W3_y 0 = 0 := by
    unfold W3_y
    rw [sum_Fin19_expand]
    rcases evalTerm_zero_vals with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      Li3E_of_ge (by norm_num : (-1 : ℝ) ≤ 0), Li3E_of_ge (by norm_num : (-1 : ℝ) ≤ 1),
      Li3E_of_ge (by norm_num : (-1 : ℝ) ≤ 1 / 2), Li3_zero, Li3_half]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18]
    norm_num
    ring
  intro t ht
  rw [const_on_Icc_third hcont hderiv t ht, h0]

private lemma W3_z_eq_zero : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 3), W3_z t = 0 := by
  have hcont : ContinuousOn W3_z (Set.Icc 0 (1 / 3)) :=
    (continuousOn_finsetSum _ (fun k _ => continuousOn_const.mul (continuousOn_Li3E_T k))).sub
      ((((((((((((((continuousOn_const.sub (continuousOn_const.mul continuousOn_y)).add
        (continuousOn_const.mul continuousOn_z)).sub continuousOn_const).add
        (continuousOn_const.mul (continuousOn_y.pow 2))).sub
        ((continuousOn_const.mul continuousOn_y).mul continuousOn_z)).add
        (continuousOn_const.mul (continuousOn_z.pow 2))).add
        ((continuousOn_const.mul continuousOn_y).div_const 3)).sub
        (continuousOn_const.mul continuousOn_z)).sub
        ((continuousOn_const.mul continuousOn_xy).mul continuousOn_z)).add
        ((continuousOn_const.mul continuousOn_xz).mul continuousOn_z)).sub
        ((continuousOn_const.mul (continuousOn_y.pow 3)).div_const 3)).add
        ((continuousOn_const.mul (continuousOn_y.pow 2)).mul continuousOn_z)).sub
        ((continuousOn_const.mul continuousOn_y).mul (continuousOn_z.pow 2))).sub
        (continuousOn_const.mul (continuousOn_z.pow 3)))
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 3), t ≠ 3 - 2 * Real.sqrt 2 → t ≠ 1 / 4 →
      HasDerivAt W3_z 0 t := by
    intro t ht hr1 h14
    have ht_cc : t ∈ Set.Icc (0 : ℝ) (1 / 3) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hd1 := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_Li3E_T k ht hr1 h14).const_mul ((T k).c * ((T k).ez : ℝ)))
    have hdx := Real.hasDerivAt_log (ne_of_gt ht.1)
    have hdy := hasDerivAt_y ht
    have hdz := hasDerivAt_z ht
    have hd2 := ((((((((((((((hasDerivAt_const t (16 * (Real.log 2) ^ 3 / 3)).fun_sub
      (hdy.const_mul (8 * (Real.log 2) ^ 2))).fun_add (hdz.const_mul (8 * (Real.log 2) ^ 2))).fun_sub
      (hasDerivAt_const t (8 * Real.log 2 * Real.pi ^ 2 / 3))).fun_add
      ((hdy.fun_pow 2).const_mul (16 * Real.log 2))).fun_sub
      ((hdy.const_mul (32 * Real.log 2)).fun_mul hdz)).fun_add
      ((hdz.fun_pow 2).const_mul (16 * Real.log 2))).fun_add
      ((hdy.const_mul (16 * Real.pi ^ 2)).div_const 3)).fun_sub
      (hdz.const_mul (6 * Real.pi ^ 2))).fun_sub
      (((hdx.fun_mul hdy).const_mul (16 : ℝ)).fun_mul hdz)).fun_add
      (((hdx.fun_mul hdz).const_mul (12 : ℝ)).fun_mul hdz)).fun_sub
      (((hdy.fun_pow 3).const_mul (8 : ℝ)).div_const 3)).fun_add
      (((hdy.fun_pow 2).const_mul (16 : ℝ)).fun_mul hdz)).fun_sub
      ((hdy.const_mul (8 : ℝ)).fun_mul (hdz.fun_pow 2))).fun_sub
      ((hdz.fun_pow 3).const_mul (2 : ℝ))
    refine (hd1.fun_sub hd2).congr_deriv ?_
    have hxz := M_xz_eq_zero t ht_cc
    have hyz := M_yz_eq_zero t ht_cc
    have hzz := M_zz_eq_zero t ht_cc
    unfold M_xz at hxz
    unfold M_yz at hyz
    unfold M_zz at hzz
    have hsum :
        (∑ k : Fin 19, (T k).c * ((T k).ez : ℝ) * (Li2E (evalTerm (T k) t) *
          (((T k).et : ℝ) / t - ((T k).ey : ℝ) / (1 - t) - 2 * ((T k).ez : ℝ) / (1 - 2 * t)))) =
        (∑ k : Fin 19, (T k).c * ((T k).et : ℝ) * ((T k).ez : ℝ) * Li2E (evalTerm (T k) t)) / t -
        (∑ k : Fin 19, (T k).c * ((T k).ey : ℝ) * ((T k).ez : ℝ) * Li2E (evalTerm (T k) t)) / (1 - t) -
        2 * (∑ k : Fin 19, (T k).c * ((T k).ez : ℝ) * ((T k).ez : ℝ) * Li2E (evalTerm (T k) t)) / (1 - 2 * t) := by
      simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hsum]
    linear_combination hxz / t - hyz / (1 - t) - 2 * hzz / (1 - 2 * t)
  have h0 : W3_z 0 = 0 := by
    unfold W3_z
    rw [sum_Fin19_expand]
    rcases evalTerm_zero_vals with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      Li3E_of_ge (by norm_num : (-1 : ℝ) ≤ 0), Li3E_of_ge (by norm_num : (-1 : ℝ) ≤ 1),
      Li3E_of_ge (by norm_num : (-1 : ℝ) ≤ 1 / 2), Li3_zero, Li3_half]
    rcases T_all with ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
    rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18]
    norm_num
    ring
  intro t ht
  rw [const_on_Icc_third hcont hderiv t ht, h0]

/-! Master weight-4 identity `F(t) - P(t) = F(0)` on `[0, 1/3]` -/

private noncomputable def F_poly (t : ℝ) : ℝ :=
  (16 * (Real.log 2) ^ 3 / 3 - 8 * Real.pi ^ 2 * Real.log 2 / 3) * Real.log (1 - 2 * t) +
    (-32 * (Real.log 2) ^ 3 / 3 + 16 * Real.pi ^ 2 * Real.log 2 / 3) * Real.log (1 - t) +
    (4 * (Real.log 2) ^ 2 - 3 * Real.pi ^ 2) * (Real.log (1 - 2 * t)) ^ 2 +
    (-8 * (Real.log 2) ^ 2 + 16 * Real.pi ^ 2 / 3) * Real.log (1 - t) * Real.log (1 - 2 * t) +
    8 * (Real.log 2) ^ 2 * (Real.log (1 - t)) ^ 2 +
    16 * Real.log 2 * (Real.log (1 - 2 * t)) ^ 3 / 3 -
    16 * Real.log 2 * Real.log (1 - t) * (Real.log (1 - 2 * t)) ^ 2 +
    16 * Real.log 2 * (Real.log (1 - t)) ^ 2 * Real.log (1 - 2 * t) -
    32 * Real.log 2 * (Real.log (1 - t)) ^ 3 / 3 -
    (Real.log (1 - 2 * t)) ^ 4 / 2 -
    8 * Real.log (1 - t) * (Real.log (1 - 2 * t)) ^ 3 / 3 +
    8 * (Real.log (1 - t)) ^ 2 * (Real.log (1 - 2 * t)) ^ 2 -
    8 * (Real.log (1 - t)) ^ 3 * Real.log (1 - 2 * t) / 3 +
    4 * (Real.log t * Real.log (1 - 2 * t)) * (Real.log (1 - 2 * t)) ^ 2 -
    8 * (Real.log t * Real.log (1 - 2 * t)) * Real.log (1 - t) * Real.log (1 - 2 * t)

private noncomputable def W4 (t : ℝ) : ℝ :=
  (∑ k : Fin 19, (T k).c * Li4E (evalTerm (T k) t)) - F_poly t

private lemma W4_third_eq_zero : W4 (1 / 3) = W4 0 := by
  have hcont_P : ContinuousOn F_poly (Set.Icc 0 (1 / 3)) :=
    ((((((((((((((continuousOn_const.mul continuousOn_z).add
      (continuousOn_const.mul continuousOn_y)).add
      (continuousOn_const.mul (continuousOn_z.pow 2))).add
      ((continuousOn_const.mul continuousOn_y).mul continuousOn_z)).add
      (continuousOn_const.mul (continuousOn_y.pow 2))).add
      ((continuousOn_const.mul (continuousOn_z.pow 3)).div_const 3)).sub
      ((continuousOn_const.mul continuousOn_y).mul (continuousOn_z.pow 2))).add
      ((continuousOn_const.mul (continuousOn_y.pow 2)).mul continuousOn_z)).sub
      ((continuousOn_const.mul (continuousOn_y.pow 3)).div_const 3)).sub
      ((continuousOn_z.pow 4).div_const 2)).sub
      (((continuousOn_const.mul continuousOn_y).mul (continuousOn_z.pow 3)).div_const 3)).add
      ((continuousOn_const.mul (continuousOn_y.pow 2)).mul (continuousOn_z.pow 2))).sub
      (((continuousOn_const.mul (continuousOn_y.pow 3)).mul continuousOn_z).div_const 3)).add
      ((continuousOn_const.mul continuousOn_xz).mul (continuousOn_z.pow 2))).sub
      (((continuousOn_const.mul continuousOn_xz).mul continuousOn_y).mul continuousOn_z)
  have hcont : ContinuousOn W4 (Set.Icc 0 (1 / 3)) :=
    (continuousOn_finsetSum _ (fun k _ => continuousOn_const.mul (continuousOn_Li4E_T k))).sub hcont_P
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 3), t ≠ 3 - 2 * Real.sqrt 2 → t ≠ 1 / 4 →
      HasDerivAt W4 0 t := by
    intro t ht hr1 h14
    have ht_cc : t ∈ Set.Icc (0 : ℝ) (1 / 3) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hd1 := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_Li4E_T k ht hr1 h14).const_mul (T k).c)
    have hdx := Real.hasDerivAt_log (ne_of_gt ht.1)
    have hdy := hasDerivAt_y ht
    have hdz := hasDerivAt_z ht
    have hd2 := ((((((((((((((hdz.const_mul (16 * (Real.log 2) ^ 3 / 3 - 8 * Real.pi ^ 2 * Real.log 2 / 3)).fun_add
      (hdy.const_mul (-32 * (Real.log 2) ^ 3 / 3 + 16 * Real.pi ^ 2 * Real.log 2 / 3))).fun_add
      ((hdz.fun_pow 2).const_mul (4 * (Real.log 2) ^ 2 - 3 * Real.pi ^ 2))).fun_add
      ((hdy.const_mul (-8 * (Real.log 2) ^ 2 + 16 * Real.pi ^ 2 / 3)).fun_mul hdz)).fun_add
      ((hdy.fun_pow 2).const_mul (8 * (Real.log 2) ^ 2))).fun_add
      (((hdz.fun_pow 3).const_mul (16 * Real.log 2)).div_const 3)).fun_sub
      ((hdy.const_mul (16 * Real.log 2)).fun_mul (hdz.fun_pow 2))).fun_add
      (((hdy.fun_pow 2).const_mul (16 * Real.log 2)).fun_mul hdz)).fun_sub
      (((hdy.fun_pow 3).const_mul (32 * Real.log 2)).div_const 3)).fun_sub
      ((hdz.fun_pow 4).div_const 2)).fun_sub
      (((hdy.const_mul (8 : ℝ)).fun_mul (hdz.fun_pow 3)).div_const 3)).fun_add
      (((hdy.fun_pow 2).const_mul (8 : ℝ)).fun_mul (hdz.fun_pow 2))).fun_sub
      ((((hdy.fun_pow 3).const_mul (8 : ℝ)).fun_mul hdz).div_const 3)).fun_add
      (((hdx.fun_mul hdz).const_mul (4 : ℝ)).fun_mul (hdz.fun_pow 2))).fun_sub
      ((((hdx.fun_mul hdz).const_mul (8 : ℝ)).fun_mul hdy).fun_mul hdz)
    refine (hd1.fun_sub hd2).congr_deriv ?_
    have hwx := W3_x_eq_zero t ht_cc
    have hwy := W3_y_eq_zero t ht_cc
    have hwz := W3_z_eq_zero t ht_cc
    unfold W3_x at hwx
    unfold W3_y at hwy
    unfold W3_z at hwz
    have hsum :
        (∑ k : Fin 19, (T k).c * (Li3E (evalTerm (T k) t) *
          (((T k).et : ℝ) / t - ((T k).ey : ℝ) / (1 - t) - 2 * ((T k).ez : ℝ) / (1 - 2 * t)))) =
        (∑ k : Fin 19, (T k).c * ((T k).et : ℝ) * Li3E (evalTerm (T k) t)) / t -
        (∑ k : Fin 19, (T k).c * ((T k).ey : ℝ) * Li3E (evalTerm (T k) t)) / (1 - t) -
        2 * (∑ k : Fin 19, (T k).c * ((T k).ez : ℝ) * Li3E (evalTerm (T k) t)) / (1 - 2 * t) := by
      simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hsum]
    linear_combination hwx / t - hwy / (1 - t) - 2 * hwz / (1 - 2 * t)
  exact const_on_Icc_third hcont hderiv (1 / 3) ⟨by norm_num, le_refl _⟩

end OMA.S_mse_1373123_proof

theorem OMA.solution : type_of% @OMA.S_mse_1373123.main := by
  have hmain := OMA.S_mse_1373123_proof.W4_third_eq_zero
  unfold OMA.S_mse_1373123_proof.W4 OMA.S_mse_1373123_proof.F_poly at hmain
  rw [OMA.S_mse_1373123_proof.sum_Fin19_expand, OMA.S_mse_1373123_proof.sum_Fin19_expand] at hmain
  rcases OMA.S_mse_1373123_proof.evalTerm_zero_vals with
    ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18⟩
  rcases OMA.S_mse_1373123_proof.evalTerm_third_vals with
    ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18⟩
  rw [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18,
    t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18,
    OMA.S_mse_1373123_proof.Li4E_of_ge (by norm_num : (-1 : ℝ) ≤ 1 / 9),
    OMA.S_mse_1373123_proof.Li4E_of_ge (by norm_num : (-1 : ℝ) ≤ 1 / 3),
    OMA.S_mse_1373123_proof.Li4E_of_ge (by norm_num : (-1 : ℝ) ≤ 1),
    OMA.S_mse_1373123_proof.Li4E_of_ge (by norm_num : (-1 : ℝ) ≤ 2 / 3),
    OMA.S_mse_1373123_proof.Li4E_of_ge (by norm_num : (-1 : ℝ) ≤ 3 / 4),
    OMA.S_mse_1373123_proof.Li4E_of_ge (by norm_num : (-1 : ℝ) ≤ 1 / 4),
    OMA.S_mse_1373123_proof.Li4E_of_ge (by norm_num : (-1 : ℝ) ≤ 1 / 2),
    OMA.S_mse_1373123_proof.Li4E_of_ge (by norm_num : (-1 : ℝ) ≤ -(1 / 3)),
    OMA.S_mse_1373123_proof.Li4E_of_ge (by norm_num : (-1 : ℝ) ≤ -1),
    OMA.S_mse_1373123_proof.Li4E_of_ge (by norm_num : (-1 : ℝ) ≤ 0),
    OMA.S_mse_1373123_proof.Li4E_of_lt (by norm_num : (-2 : ℝ) < -1),
    OMA.S_mse_1373123_proof.Li4E_of_lt (by norm_num : (-3 : ℝ) < -1)] at hmain
  have h1 : (1 : ℝ) / (-2 : ℝ) = -(1 / 2 : ℝ) := by norm_num
  have h2 : (1 : ℝ) / (-3 : ℝ) = -(1 / 3 : ℝ) := by norm_num
  have h13 : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
  have h23 : (1 : ℝ) - 2 * (1 / 3) = 1 / 3 := by norm_num
  have h01 : (1 : ℝ) - 0 = 1 := by norm_num
  have h02 : (1 : ℝ) - 2 * (0 : ℝ) = 1 := by norm_num
  have hlog23 : Real.log (2 / 3 : ℝ) = Real.log 2 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  have hlog13 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by
    rw [one_div, Real.log_inv]
  have hdup2 := OMA.S_mse_1373123_proof.Li4_dup (x := 1 / 2) (by norm_num) (by norm_num)
  rw [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num] at hdup2
  rcases OMA.S_mse_1373123_proof.T_all with
    ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩
  rw [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18] at hmain
  rw [h1, h2, h13, h23, h01, h02, neg_neg, neg_neg, hlog23, hlog13,
    Real.log_one, Real.log_zero,
    OMA.S_mse_1373123_proof.Li4_zero,
    OMA.S_mse_1373123_proof.Li4_one,
    OMA.S_mse_1373123_proof.Li4_neg_one] at hmain
  norm_num at hmain hdup2
  dsimp only
  linear_combination 45 * hmain + 720 * hdup2
