import OMAStatements.S_mse_4948679

namespace OMA.Mse4948679

open MeasureTheory

private lemma prefix_abs_le (g : ℝ → ℝ)
    (hg : IntervalIntegrable (fun t => (g t)^2) volume 0 1)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |∫ t in (0 : ℝ)..x, g t| ≤ Real.sqrt (∫ t in (0 : ℝ)..1, (g t)^2) := by
  by_cases h : IntervalIntegrable g volume 0 x
  · let I : ℝ := ∫ t in (0 : ℝ)..x, |g t|
    have hI : IntervalIntegrable (fun t => |g t|) volume 0 x := by
      simpa only [Real.norm_eq_abs] using h.norm
    have hgs : IntervalIntegrable (fun t => (g t)^2) volume 0 x :=
      hg.mono_set (by
        simpa only [Set.uIcc_of_le hx.1, Set.uIcc_of_le zero_le_one] using
          Set.Icc_subset_Icc (le_refl (0 : ℝ)) hx.2)
    have henergy : (∫ t in (0 : ℝ)..x, (g t)^2) ≤ ∫ t in (0 : ℝ)..1, (g t)^2 :=
      intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
        (Filter.Eventually.of_forall fun t => sq_nonneg (g t)) hg
    have hconst : IntervalIntegrable (fun _ : ℝ => I^2) volume 0 x :=
      intervalIntegrable_const
    have hyoung := intervalIntegral.integral_mono_on hx.1
      (hI.const_mul (2 * I)) (hgs.add hconst) (fun t _ => by
        change (2 * I) * |g t| ≤ (g t)^2 + I^2
        nlinarith only [sq_nonneg (|g t| - I), sq_abs (g t)])
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hgs hconst,
      intervalIntegral.integral_const] at hyoung
    simp only [sub_zero, smul_eq_mul] at hyoung
    change (2 * I) * I ≤ (∫ t in (0 : ℝ)..x, (g t)^2) + x * I^2 at hyoung
    have htail : x * I^2 ≤ I^2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hx.2 (sq_nonneg I)
    have hs : I^2 ≤ ∫ t in (0 : ℝ)..1, (g t)^2 := by
      nlinarith only [hyoung, htail, henergy]
    exact (intervalIntegral.abs_integral_le_integral_abs hx.1).trans
      (Real.le_sqrt_of_sq_le hs)
  · rw [intervalIntegral.integral_undef h, abs_zero]
    exact Real.sqrt_nonneg _

private lemma normalized_gap (f : ℝ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hf : (∫ x in (0 : ℝ)..1, (f x) ^ 2) = 1)
    (osc : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |f x - f y| ≤ D) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |(|f x|) - 1| ≤ D := by
  intro x hx
  have hfi : IntervalIntegrable (fun u => f u ^ 2) volume 0 1 :=
    intervalIntegral.intervalIntegrable_of_integral_ne_zero (by rw [hf]; norm_num)
  have hclose (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
      -D ≤ |f x| - |f y| ∧ |f x| - |f y| ≤ D :=
    abs_le.mp ((abs_abs_sub_abs_le_abs_sub (f x) (f y)).trans (osc x hx y hy))
  apply abs_le.mpr
  constructor
  · by_contra! h
    have hupper (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
        f y ^ 2 ≤ (|f x| + D) ^ 2 := by
      have hbound : |f y| ≤ |f x| + D := by linarith only [(hclose y hy).1]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f y)) hbound 2
    have hav := intervalIntegral.integral_mono_on zero_le_one hfi
      intervalIntegrable_const hupper
    rw [hf, intervalIntegral.integral_const, sub_zero, one_smul] at hav
    have hsmall : |f x| + D < 1 := by linarith only [h]
    have hsq := pow_lt_pow_left₀ hsmall (add_nonneg (abs_nonneg (f x)) hD)
      (by norm_num : (2 : ℕ) ≠ 0)
    exact (not_lt_of_ge hav) (by simpa only [one_pow] using hsq)
  · by_contra! h
    have hlarge : 1 < |f x| - D := by linarith only [h]
    have hlower (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
        (|f x| - D) ^ 2 ≤ f y ^ 2 := by
      have hbound : |f x| - D ≤ |f y| := by linarith only [(hclose y hy).2]
      simpa only [sq_abs] using
        pow_le_pow_left₀ (zero_le_one.trans hlarge.le) hbound 2
    have hav := intervalIntegral.integral_mono_on zero_le_one
      intervalIntegrable_const hfi hlower
    rw [intervalIntegral.integral_const, sub_zero, one_smul, hf] at hav
    have hsq := pow_lt_pow_left₀ hlarge zero_le_one (by norm_num : (2 : ℕ) ≠ 0)
    exact (not_lt_of_ge hav) (by simpa only [one_pow] using hsq)

private theorem entropy_from_gap (f : ℝ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : (∫ x in (0 : ℝ)..1, (f x)^2) = 1)
    (gap : ∀ x ∈ Set.Icc (0 : ℝ) 1, |(|f x|) - 1| ≤ 2 * Real.sqrt E) :
    (∫ x in (0 : ℝ)..1, (f x)^2 * Real.log ((f x)^2)) ≤ 16 * E := by
  have hfInt : IntervalIntegrable (fun x => (f x)^2) volume 0 1 := by
    by_contra hn
    rw [intervalIntegral.integral_undef hn] at hf
    norm_num at hf
  by_cases hLogInt : IntervalIntegrable (fun x => (f x)^2 * Real.log ((f x)^2))
      volume 0 1
  · have hMajor (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
        (f x)^2 * Real.log ((f x)^2) ≤ (1 + 8 * E) * (f x)^2 + (8 * E - 1) := by
      have hLog : (f x)^2 * Real.log ((f x)^2) ≤ (f x)^2 - 1 + ((f x)^2 - 1)^2 := by
        rcases eq_or_lt_of_le (sq_nonneg (f x)) with hzero | hpos
        · rw [← hzero]
          norm_num
        calc
          _ ≤ (f x)^2 * ((f x)^2 - 1) :=
            mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hpos) (sq_nonneg _)
          _ = _ := by ring
      have hGapSq : (|f x| - 1)^2 ≤ 4 * E := by
        have h := (sq_le_sq₀ (abs_nonneg (|f x| - 1))
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg E))).2 (gap x hx)
        rw [sq_abs, mul_pow, Real.sq_sqrt hE] at h
        norm_num at h
        exact h
      have hPlusSq : (|f x| + 1)^2 ≤ 2 * (f x)^2 + 2 := by
        rw [← sq_abs (f x)]
        nlinarith only [sq_nonneg (|f x| - 1)]
      have hSquared : ((f x)^2 - 1)^2 ≤ 4 * E * (2 * (f x)^2 + 2) := by
        calc
          ((f x)^2 - 1)^2 = (|f x| - 1)^2 * (|f x| + 1)^2 := by
            rw [← sq_abs (f x)]
            ring
          _ ≤ (4 * E) * (|f x| + 1)^2 := mul_le_mul_of_nonneg_right hGapSq (sq_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_left hPlusSq (mul_nonneg (by norm_num) hE)
      calc
        _ ≤ (f x)^2 - 1 + ((f x)^2 - 1)^2 := hLog
        _ ≤ (f x)^2 - 1 + 4 * E * (2 * (f x)^2 + 2) := add_le_add (le_refl _) hSquared
        _ = _ := by ring
    have hScaled := hfInt.const_mul (1 + 8 * E)
    have hConst : IntervalIntegrable (fun _ : ℝ => 8 * E - 1) volume 0 1 :=
      intervalIntegrable_const
    calc
      _ ≤ ∫ x in (0 : ℝ)..1, (1 + 8 * E) * (f x)^2 + (8 * E - 1) :=
        intervalIntegral.integral_mono_on (by norm_num) hLogInt (hScaled.add hConst) hMajor
      _ = _ := by
        rw [intervalIntegral.integral_add hScaled hConst, intervalIntegral.integral_const_mul,
          hf, intervalIntegral.integral_const]
        simp
        ring
  · rw [intervalIntegral.integral_undef hLogInt]
    exact mul_nonneg (by norm_num) hE

theorem interval_log_sobolev (f g : ℝ → ℝ)
    (hg : IntervalIntegrable (fun x => (g x) ^ 2) volume 0 1)
    (hprefix : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x - f 0 = ∫ t in (0 : ℝ)..x, g t)
    (hf : (∫ x in (0 : ℝ)..1, (f x) ^ 2) = 1) :
    (∫ x in (0 : ℝ)..1, (f x) ^ 2 * Real.log ((f x) ^ 2)) ≤
      16 * (∫ x in (0 : ℝ)..1, (g x) ^ 2) := by
  let E := ∫ x in (0 : ℝ)..1, (g x) ^ 2
  have hE : 0 ≤ E :=
    intervalIntegral.integral_nonneg zero_le_one (fun x _ => sq_nonneg (g x))
  have hanchor (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : |f x - f 0| ≤ Real.sqrt E := by
    rw [hprefix x hx]
    exact prefix_abs_le g hg hx
  have hosc (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
      (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) : |f x - f y| ≤ 2 * Real.sqrt E := by
    calc
      |f x - f y| = |(f x - f 0) + -(f y - f 0)| := by
        congr 1
        ring
      _ ≤ |f x - f 0| + |-(f y - f 0)| := abs_add_le _ _
      _ = |f x - f 0| + |f y - f 0| := by rw [abs_neg]
      _ ≤ 2 * Real.sqrt E := by linarith [hanchor x hx, hanchor y hy]
  exact entropy_from_gap f E hE hf (normalized_gap f (2 * Real.sqrt E) (by positivity) hf hosc)

end OMA.Mse4948679

theorem OMA.solution : type_of% @OMA.S_mse_4948679.main := by
  refine ⟨16, by norm_num, ?_⟩
  exact OMA.Mse4948679.interval_log_sobolev
