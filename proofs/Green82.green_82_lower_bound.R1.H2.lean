import OMAReductions.R_Green82_green_82_lower_bound_R1

-- Step Green82.green_82_lower_bound.R1.H2: hypothesis H2 of reduction Green82.green_82_lower_bound.R1
-- Credit: @minimumnz

namespace Green82Proof

open Real Complex MeasureTheory Filter Set Finset
open scoped BigOperators Topology

/-! ### Section 1: Trigonometric Polynomials and Normalized Circle Integrals -/

abbrev TrigPoly := ℤ →₀ ℂ

noncomputable def eChar (m : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))

lemma eChar_zero (x : ℝ) : eChar 0 x = 1 := by
  simp [eChar]

lemma eChar_add (m n : ℤ) (x : ℝ) : eChar (m + n) x = eChar m x * eChar n x := by
  unfold eChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma eChar_neg (m : ℤ) (x : ℝ) : eChar (-m) x = starRingEnd ℂ (eChar m x) := by
  unfold eChar
  rw [← Complex.exp_conj]
  congr 1
  simp [mul_assoc]

lemma norm_eChar (m : ℤ) (x : ℝ) : ‖eChar m x‖ = 1 := by
  unfold eChar
  have h : Complex.I * (m : ℂ) * (x : ℂ) = (((m : ℝ) * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_eChar (m : ℤ) : Continuous (eChar m) := by
  unfold eChar
  fun_prop

lemma eChar_two_pi (m : ℤ) : eChar m (2 * Real.pi) = 1 := by
  unfold eChar
  have h : Complex.I * (m : ℂ) * ((2 * Real.pi : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I m

lemma hasDerivAt_eChar (m : ℤ) (x : ℝ) :
    HasDerivAt (eChar m) (Complex.I * (m : ℂ) * eChar m x) x := by
  unfold eChar
  have h1 : HasDerivAt (fun t : ℝ => Complex.I * (m : ℂ) * (t : ℂ)) (Complex.I * (m : ℂ)) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (Complex.I * (m : ℂ))
  have h2 := h1.cexp
  simpa [mul_comm, mul_left_comm, mul_assoc] using h2

lemma integral_eChar (m : ℤ) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), eChar m x) = if m = 0 then (2 * Real.pi : ℂ) else 0 := by
  split_ifs with hm
  · subst hm
    simp [eChar_zero]
  · have hne : Complex.I * (m : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hm)
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        HasDerivAt (fun t : ℝ => (Complex.I * (m : ℂ))⁻¹ * eChar m t) (eChar m x) x := by
      intro x _
      have h := (hasDerivAt_eChar m x).const_mul (Complex.I * (m : ℂ))⁻¹
      rwa [← mul_assoc, inv_mul_cancel₀ hne, one_mul] at h
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((continuous_eChar m).intervalIntegrable 0 (2 * Real.pi))]
    rw [eChar_two_pi]
    have h0 : eChar m 0 = 1 := by simp [eChar]
    rw [h0, sub_self]

noncomputable def circleInt (f : ℝ → ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ x in (0 : ℝ)..(2 * Real.pi), f x

noncomputable def circleIntR (f : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ x in (0 : ℝ)..(2 * Real.pi), f x

lemma circleInt_eChar (m : ℤ) : circleInt (eChar m) = if m = 0 then 1 else 0 := by
  unfold circleInt
  rw [integral_eChar]
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
  split_ifs
  · push_cast at hpi ⊢
    exact inv_mul_cancel₀ hpi
  · simp

lemma circleInt_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    circleInt (fun x => f x + g x) = circleInt f + circleInt g := by
  unfold circleInt
  rw [intervalIntegral.integral_add (hf.intervalIntegrable 0 (2 * Real.pi))
    (hg.intervalIntegrable 0 (2 * Real.pi)), mul_add]

lemma circleInt_const_mul (c : ℂ) (f : ℝ → ℂ) :
    circleInt (fun x => c * f x) = c * circleInt f := by
  unfold circleInt
  rw [intervalIntegral.integral_const_mul]
  ring

lemma circleInt_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    circleInt (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, circleInt (f i) := by
  unfold circleInt
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).intervalIntegrable 0 (2 * Real.pi)),
    Finset.mul_sum]

lemma circleInt_ofReal (f : ℝ → ℝ) :
    circleInt (fun x => (f x : ℂ)) = ((circleIntR f : ℝ) : ℂ) := by
  unfold circleInt circleIntR
  rw [intervalIntegral.integral_ofReal]
  push_cast
  rfl

lemma circleInt_re (f : ℝ → ℂ) (hf : Continuous f) :
    (circleInt f).re = circleIntR (fun x => (f x).re) := by
  unfold circleInt circleIntR
  have hre : (∫ x in (0 : ℝ)..(2 * Real.pi), f x).re =
      ∫ x in (0 : ℝ)..(2 * Real.pi), (f x).re := by
    simpa using (Complex.reCLM.intervalIntegral_comp_comm
      (hf.intervalIntegrable 0 (2 * Real.pi))).symm
  rw [show (((2 * Real.pi : ℝ) : ℂ)⁻¹) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.re_ofReal_mul, hre]

lemma circleInt_conj (f : ℝ → ℂ) (hf : Continuous f) :
    circleInt (fun x => starRingEnd ℂ (f x)) = starRingEnd ℂ (circleInt f) := by
  unfold circleInt
  have hconj : (∫ x in (0 : ℝ)..(2 * Real.pi), starRingEnd ℂ (f x)) =
      starRingEnd ℂ (∫ x in (0 : ℝ)..(2 * Real.pi), f x) := by
    simpa using (Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
      (hf.intervalIntegrable 0 (2 * Real.pi)))
  rw [hconj, map_mul, map_inv₀, Complex.conj_ofReal]

lemma norm_circleInt_le (f : ℝ → ℂ) (_hf : Continuous f) :
    ‖circleInt f‖ ≤ circleIntR (fun x => ‖f x‖) := by
  unfold circleInt circleIntR
  have hpi : 0 ≤ (2 * Real.pi : ℝ) := by positivity
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hpi]
  gcongr
  exact intervalIntegral.norm_integral_le_integral_norm hpi

lemma circleIntR_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi), f x ≤ g x) :
    circleIntR f ≤ circleIntR g := by
  unfold circleIntR
  have hpi : 0 ≤ (2 * Real.pi : ℝ) := by positivity
  gcongr
  exact intervalIntegral.integral_mono_on hpi (hf.intervalIntegrable 0 (2 * Real.pi))
    (hg.intervalIntegrable 0 (2 * Real.pi)) hfg

lemma circleIntR_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi), 0 ≤ f x) :
    0 ≤ circleIntR f := by
  have := circleIntR_mono continuous_const hf h0
  simpa [circleIntR] using this

lemma circleIntR_const (c : ℝ) : circleIntR (fun _ => c) = c := by
  unfold circleIntR
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]

lemma circleIntR_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    circleIntR (fun x => f x + g x) = circleIntR f + circleIntR g := by
  unfold circleIntR
  rw [intervalIntegral.integral_add (hf.intervalIntegrable 0 (2 * Real.pi))
    (hg.intervalIntegrable 0 (2 * Real.pi)), mul_add]

lemma circleIntR_const_mul (c : ℝ) (f : ℝ → ℝ) :
    circleIntR (fun x => c * f x) = c * circleIntR f := by
  unfold circleIntR
  rw [intervalIntegral.integral_const_mul]
  ring

lemma circleIntR_cauchy_schwarz {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    circleIntR (fun x => |f x * g x|) ≤
      Real.sqrt (circleIntR (fun x => f x ^ 2)) * Real.sqrt (circleIntR (fun x => g x ^ 2)) := by
  have hA : 0 ≤ circleIntR (fun x => f x ^ 2) :=
    circleIntR_nonneg (hf.pow 2) (fun x _ => sq_nonneg _)
  have hB : 0 ≤ circleIntR (fun x => g x ^ 2) :=
    circleIntR_nonneg (hg.pow 2) (fun x _ => sq_nonneg _)
  have hAB : 0 ≤ circleIntR (fun x => |f x * g x|) :=
    circleIntR_nonneg (hf.mul hg).abs (fun x _ => abs_nonneg _)
  suffices hsq : (circleIntR (fun x => |f x * g x|)) ^ 2 ≤
      circleIntR (fun x => f x ^ 2) * circleIntR (fun x => g x ^ 2) by
    rw [← Real.sqrt_mul hA]
    exact Real.le_sqrt_of_sq_le hsq
  by_cases hB0 : circleIntR (fun x => g x ^ 2) = 0
  · have hq : ∀ t : ℝ, 0 ≤ t ^ 2 * circleIntR (fun x => f x ^ 2) -
        2 * t * circleIntR (fun x => |f x * g x|) + circleIntR (fun x => g x ^ 2) := by
      intro t
      have h1 : 0 ≤ circleIntR (fun x => (t * |f x| - |g x|) ^ 2) :=
        circleIntR_nonneg (((hf.abs.const_mul t).sub hg.abs).pow 2) (fun x _ => sq_nonneg _)
      have heq : (fun x => (t * |f x| - |g x|) ^ 2) =
          fun x => t ^ 2 * f x ^ 2 + ((-2 * t) * |f x * g x| + g x ^ 2) := by
        ext x
        rw [abs_mul, sub_sq, mul_pow, sq_abs, sq_abs]
        ring
      rw [heq, circleIntR_add (f := fun x => t ^ 2 * f x ^ 2)
          (g := fun x => (-2 * t) * |f x * g x| + g x ^ 2) (by fun_prop) (by fun_prop),
        circleIntR_add (f := fun x => (-2 * t) * |f x * g x|) (g := fun x => g x ^ 2)
          (by fun_prop) (by fun_prop),
        circleIntR_const_mul, circleIntR_const_mul] at h1
      linarith
    rw [hB0, mul_zero]
    by_contra hpos
    push Not at hpos
    have hc : 0 < circleIntR (fun x => |f x * g x|) := by nlinarith
    let t := (circleIntR (fun x => f x ^ 2) + 1)⁻¹ * circleIntR (fun x => |f x * g x|)
    have hqt := hq t
    rw [hB0, add_zero] at hqt
    have hden : 0 < circleIntR (fun x => f x ^ 2) + 1 := by linarith
    have ht_pos : 0 < t := mul_pos (inv_pos.mpr hden) hc
    have hmul : t * circleIntR (fun x => f x ^ 2) < circleIntR (fun x => |f x * g x|) := by
      dsimp [t]
      rw [inv_mul_eq_div, div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    nlinarith
  · have hBpos : 0 < circleIntR (fun x => g x ^ 2) := lt_of_le_of_ne hB (Ne.symm hB0)
    let t := circleIntR (fun x => |f x * g x|) / circleIntR (fun x => g x ^ 2)
    have h1 : 0 ≤ circleIntR (fun x => (|f x| - t * |g x|) ^ 2) :=
      circleIntR_nonneg ((hf.abs.sub (hg.abs.const_mul t)).pow 2) (fun x _ => sq_nonneg _)
    have heq : (fun x => (|f x| - t * |g x|) ^ 2) =
        fun x => f x ^ 2 + ((-2 * t) * |f x * g x| + t ^ 2 * g x ^ 2) := by
      ext x
      rw [abs_mul, sub_sq, mul_pow, sq_abs, sq_abs]
      ring
    rw [heq, circleIntR_add (f := fun x => f x ^ 2)
        (g := fun x => (-2 * t) * |f x * g x| + t ^ 2 * g x ^ 2) (by fun_prop) (by fun_prop),
      circleIntR_add (f := fun x => (-2 * t) * |f x * g x|) (g := fun x => t ^ 2 * g x ^ 2)
        (by fun_prop) (by fun_prop),
      circleIntR_const_mul, circleIntR_const_mul] at h1
    have htB : t * circleIntR (fun x => g x ^ 2) = circleIntR (fun x => |f x * g x|) :=
      div_mul_cancel₀ _ hB0
    have h2 : t ^ 2 * circleIntR (fun x => g x ^ 2) = t * circleIntR (fun x => |f x * g x|) := by
      rw [sq, mul_assoc, htB]
    have h3 : t * circleIntR (fun x => |f x * g x|) ≤ circleIntR (fun x => f x ^ 2) := by
      linarith
    have h4 := mul_le_mul_of_nonneg_right h3 hB
    rw [show t * circleIntR (fun x => |f x * g x|) * circleIntR (fun x => g x ^ 2) =
      (t * circleIntR (fun x => g x ^ 2)) * circleIntR (fun x => |f x * g x|) by ring,
      htB, ← sq] at h4
    exact h4

/-! ### Evaluation and Algebra of Trigonometric Polynomials -/

noncomputable def evalTP (p : TrigPoly) (x : ℝ) : ℂ :=
  p.sum fun m c => c * eChar m x

lemma evalTP_zero (x : ℝ) : evalTP 0 x = 0 := by
  simp [evalTP]

lemma evalTP_single (m : ℤ) (c : ℂ) (x : ℝ) :
    evalTP (Finsupp.single m c) x = c * eChar m x := by
  simp [evalTP, Finsupp.sum_single_index]

lemma evalTP_add (p q : TrigPoly) (x : ℝ) :
    evalTP (p + q) x = evalTP p x + evalTP q x := by
  unfold evalTP
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

lemma evalTP_smul (c : ℂ) (p : TrigPoly) (x : ℝ) :
    evalTP (c • p) x = c * evalTP p x := by
  unfold evalTP
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun m _ => by simp [mul_assoc]

lemma evalTP_neg (p : TrigPoly) (x : ℝ) :
    evalTP (-p) x = -evalTP p x := by
  have h : -p = (-1 : ℂ) • p := by ext m; simp
  rw [h, evalTP_smul]; ring

lemma evalTP_finset_sum {ι : Type*} (s : Finset ι) (f : ι → TrigPoly) (x : ℝ) :
    evalTP (∑ i ∈ s, f i) x = ∑ i ∈ s, evalTP (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalTP_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, evalTP_add, ih, Finset.sum_insert ha]

lemma continuous_evalTP (p : TrigPoly) : Continuous (evalTP p) := by
  unfold evalTP Finsupp.sum
  exact continuous_finset_sum _ fun m _ => continuous_const.mul (continuous_eChar m)

noncomputable def mulTP (p q : TrigPoly) : TrigPoly :=
  p.sum fun m a => q.sum fun n b => Finsupp.single (m + n) (a * b)

lemma evalTP_mulTP (p q : TrigPoly) (x : ℝ) :
    evalTP (mulTP p q) x = evalTP p x * evalTP q x := by
  unfold mulTP
  rw [Finsupp.sum, evalTP_finset_sum]
  simp_rw [Finsupp.sum, evalTP_finset_sum, evalTP_single, eChar_add]
  unfold evalTP Finsupp.sum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => by ring

lemma support_mulTP_subset (p q : TrigPoly) :
    ∀ k ∈ (mulTP p q).support, ∃ m ∈ p.support, ∃ n ∈ q.support, k = m + n := by
  intro k hk
  unfold mulTP at hk
  rw [Finsupp.sum, Finsupp.mem_support_iff] at hk
  have hne : (∑ m ∈ p.support, q.sum fun n b => Finsupp.single (m + n) (p m * b)) k ≠ 0 := hk
  rw [Finsupp.finset_sum_apply] at hne
  obtain ⟨m, hm, hne2⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  rw [Finsupp.sum, Finsupp.finset_sum_apply] at hne2
  obtain ⟨n, hn, hne3⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne2
  rw [Finsupp.single_apply] at hne3
  split_ifs at hne3 with h
  · exact ⟨m, hm, n, hn, h.symm⟩
  · exact absurd rfl hne3

noncomputable def conjTP (p : TrigPoly) : TrigPoly :=
  p.sum fun m a => Finsupp.single (-m) (starRingEnd ℂ a)

lemma evalTP_conjTP (p : TrigPoly) (x : ℝ) :
    evalTP (conjTP p) x = starRingEnd ℂ (evalTP p x) := by
  unfold conjTP
  rw [Finsupp.sum, evalTP_finset_sum]
  conv_rhs => unfold evalTP Finsupp.sum
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [evalTP_single, map_mul, eChar_neg]

lemma support_conjTP_subset (p : TrigPoly) :
    ∀ k ∈ (conjTP p).support, ∃ m ∈ p.support, k = -m := by
  intro k hk
  unfold conjTP at hk
  rw [Finsupp.sum, Finsupp.mem_support_iff, Finsupp.finset_sum_apply] at hk
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
  rw [Finsupp.single_apply] at hne
  split_ifs at hne with h
  · exact ⟨m, hm, h.symm⟩
  · exact absurd rfl hne

noncomputable def powTP (p : TrigPoly) : ℕ → TrigPoly
  | 0 => Finsupp.single 0 1
  | n + 1 => mulTP (powTP p n) p

lemma evalTP_powTP (p : TrigPoly) (n : ℕ) (x : ℝ) :
    evalTP (powTP p n) x = (evalTP p x) ^ n := by
  induction n with
  | zero => simp [powTP, evalTP_single, eChar_zero]
  | succ n ih => rw [powTP, evalTP_mulTP, ih, pow_succ]

lemma support_powTP_nonneg {p : TrigPoly} (hp : ∀ m ∈ p.support, 0 ≤ m) (n : ℕ) :
    ∀ k ∈ (powTP p n).support, 0 ≤ k := by
  induction n with
  | zero =>
    intro k hk
    simp only [powTP, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hk
    omega
  | succ n ih =>
    intro k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := support_mulTP_subset _ _ k hk
    linarith [ih a ha, hp b hb]

lemma circleInt_evalTP (p : TrigPoly) : circleInt (evalTP p) = p 0 := by
  have hev : evalTP p = fun x => ∑ m ∈ p.support, p m * eChar m x := rfl
  rw [hev, circleInt_finset_sum p.support (fun m x => p m * eChar m x)
    (fun m _ => continuous_const.mul (continuous_eChar m))]
  simp_rw [circleInt_const_mul, circleInt_eChar, mul_ite, mul_one, mul_zero]
  by_cases h0 : (0 : ℤ) ∈ p.support
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro m _ hm; simp [hm]
    · intro h; exact absurd h0 h
  · rw [Finset.sum_eq_zero]
    · exact (Finsupp.notMem_support_iff.mp h0).symm
    · intro m hm
      have : m ≠ 0 := fun h => h0 (h ▸ hm)
      simp [this]

lemma circleInt_evalTP_mul_eChar (p : TrigPoly) (m : ℤ) :
    circleInt (fun x => evalTP p x * eChar (-m) x) = p m := by
  have h : (fun x => evalTP p x * eChar (-m) x) = evalTP (mulTP p (Finsupp.single (-m) 1)) := by
    ext x
    rw [evalTP_mulTP, evalTP_single, one_mul]
  rw [h, circleInt_evalTP]
  unfold mulTP
  rw [Finsupp.sum, Finsupp.finsetSum_apply]
  have hsingle : ∀ k : ℤ, (Finsupp.single (-m) (1 : ℂ)).sum
      (fun n b => Finsupp.single (k + n) (p k * b)) = Finsupp.single (k + -m) (p k) := by
    intro k
    rw [Finsupp.sum_single_index (by simp), mul_one]
  simp_rw [hsingle, Finsupp.single_apply]
  by_cases hm : m ∈ p.support
  · rw [Finset.sum_eq_single m]
    · simp
    · intro k _ hkm; split_ifs with h <;> [omega; rfl]
    · intro h; exact absurd hm h
  · rw [Finset.sum_eq_zero]
    · exact (Finsupp.notMem_support_iff.mp hm).symm
    · intro k hk
      have hkm : k ≠ m := fun h => hm (h ▸ hk)
      split_ifs with h <;> [omega; rfl]

lemma circleInt_evalTP_mul_conj (p q : TrigPoly) :
    circleInt (fun x => evalTP p x * starRingEnd ℂ (evalTP q x)) =
      p.sum fun m c => c * starRingEnd ℂ (q m) := by
  have h1 : (fun x => evalTP p x * starRingEnd ℂ (evalTP q x)) =
      fun x => ∑ m ∈ p.support, p m * (starRingEnd ℂ (evalTP q x) * eChar m x) := by
    ext x
    unfold evalTP Finsupp.sum
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => by ring
  rw [h1, circleInt_finset_sum p.support
    (fun m x => p m * (starRingEnd ℂ (evalTP q x) * eChar m x))
    (fun m _ => continuous_const.mul ((Complex.continuous_conj.comp (continuous_evalTP q)).mul (continuous_eChar m)))]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [circleInt_const_mul]
  congr 1
  have h2 : (fun x => starRingEnd ℂ (evalTP q x) * eChar m x) =
      fun x => starRingEnd ℂ (evalTP q x * eChar (-m) x) := by
    ext x; rw [map_mul, ← eChar_neg, neg_neg]
  rw [h2, circleInt_conj (fun x => evalTP q x * eChar (-m) x)
    ((continuous_evalTP q).mul (continuous_eChar (-m))),
    circleInt_evalTP_mul_eChar]

lemma parseval_evalTP (p : TrigPoly) :
    circleIntR (fun x => ‖evalTP p x‖ ^ 2) = p.sum fun _ c => ‖c‖ ^ 2 := by
  have h1 : (fun x => ((‖evalTP p x‖ ^ 2 : ℝ) : ℂ)) =
      fun x => evalTP p x * starRingEnd ℂ (evalTP p x) := by
    ext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 := circleInt_evalTP_mul_conj p p
  rw [← h1, circleInt_ofReal] at h2
  have h3 : (p.sum fun m c => c * starRingEnd ℂ (p m)) =
      ((p.sum fun _ c => ‖c‖ ^ 2 : ℝ) : ℂ) := by
    unfold Finsupp.sum
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    dsimp only
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h3] at h2
  exact Complex.ofReal_injective h2

lemma norm_evalTP_le_l1 (p : TrigPoly) (x : ℝ) :
    ‖evalTP p x‖ ≤ p.sum fun _ c => ‖c‖ := by
  unfold evalTP Finsupp.sum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, norm_eChar, mul_one]

lemma coeff_neg_of_real_evalTP {p : TrigPoly} (hr : ∀ x, (evalTP p x).im = 0) (m : ℤ) :
    p (-m) = starRingEnd ℂ (p m) := by
  have hconj : ∀ x, starRingEnd ℂ (evalTP p x) = evalTP p x := by
    intro x
    exact Complex.ext (by simp) (by simp [hr x])
  rw [← circleInt_evalTP_mul_eChar p m, ← circleInt_evalTP_mul_eChar p (-m),
    ← circleInt_conj (fun x => evalTP p x * eChar (-m) x)
      ((continuous_evalTP p).mul (continuous_eChar (-m)))]
  congr 1
  ext x
  rw [map_mul, hconj x, ← eChar_neg]

/-! ### Weierstrass Approximation and Analytic Projection for MPS -/

noncomputable def compPolyTP (P : Polynomial ℝ) (p : TrigPoly) : TrigPoly :=
  P.sum fun k a => (a : ℂ) • powTP p k

lemma evalTP_compPolyTP (P : Polynomial ℝ) (p : TrigPoly) (x : ℝ)
    (hr : ∀ t, (evalTP p t).im = 0) :
    evalTP (compPolyTP P p) x = ((P.eval (evalTP p x).re : ℝ) : ℂ) := by
  unfold compPolyTP
  rw [Polynomial.sum_def, evalTP_finset_sum]
  rw [Polynomial.eval_eq_sum]
  unfold Polynomial.sum
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [evalTP_smul, evalTP_powTP]
  have hre : evalTP p x = ((evalTP p x).re : ℂ) := Complex.ext rfl (by simp [hr x])
  conv_lhs => rw [hre]
  push_cast
  rfl

lemma exists_trigPoly_approx_norm (G : TrigPoly) {ε : ℝ} (hε : 0 < ε)
    (hG : ∀ x, ‖evalTP G x‖ ≤ 1) :
    ∃ V : TrigPoly, (∀ x, (evalTP V x).im = 0) ∧
      ∀ x, ‖evalTP G x‖ ≤ (evalTP V x).re ∧ (evalTP V x).re ≤ ‖evalTP G x‖ + ε := by
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn 0 1 Real.sqrt
    Real.continuous_sqrt.continuousOn (ε / 2) (by linarith)
  let Gsq : TrigPoly := mulTP G (conjTP G)
  have hGsq_eval : ∀ x, evalTP Gsq x = ((‖evalTP G x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [evalTP_mulTP, evalTP_conjTP, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hGsq_im : ∀ x, (evalTP Gsq x).im = 0 := by
    intro x; rw [hGsq_eval, Complex.ofReal_im]
  let V : TrigPoly := compPolyTP P Gsq + Finsupp.single 0 ((ε / 2 : ℝ) : ℂ)
  refine ⟨V, ?_, ?_⟩
  · intro x
    rw [evalTP_add, evalTP_compPolyTP P Gsq x hGsq_im, evalTP_single, eChar_zero, mul_one]
    simp
  · intro x
    have hmem : ‖evalTP G x‖ ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨sq_nonneg _, ?_⟩
      have h1 := hG x
      nlinarith [norm_nonneg (evalTP G x)]
    have hnear := hP (‖evalTP G x‖ ^ 2) hmem
    rw [Real.sqrt_sq (norm_nonneg _)] at hnear
    have hre : (evalTP V x).re = P.eval (‖evalTP G x‖ ^ 2) + ε / 2 := by
      rw [evalTP_add, evalTP_compPolyTP P Gsq x hGsq_im, evalTP_single, eChar_zero, mul_one]
      have hsqre : (evalTP Gsq x).re = ‖evalTP G x‖ ^ 2 := by rw [hGsq_eval, Complex.ofReal_re]
      rw [hsqre]
      simp
    rw [hre]
    rw [abs_lt] at hnear
    constructor <;> linarith

noncomputable def projNonpos (V : TrigPoly) : TrigPoly :=
  V.sum fun m c =>
    if m < 0 then Finsupp.single m (2 * c)
    else if m = 0 then Finsupp.single 0 c
    else 0

lemma projNonpos_apply (V : TrigPoly) (m : ℤ) :
    projNonpos V m = if m < 0 then 2 * V m else if m = 0 then V 0 else 0 := by
  unfold projNonpos
  rw [Finsupp.sum, Finsupp.finsetSum_apply]
  by_cases hm : m ∈ V.support
  · rw [Finset.sum_eq_single m]
    · split_ifs with h1 h2
      · simp
      · subst h2; simp
      · simp
    · intro k _ hkm
      split_ifs with h1 h2
      · simp [hkm]
      · subst h2; simp [hkm]
      · simp
    · intro h; exact absurd hm h
  · have hVm : V m = 0 := Finsupp.notMem_support_iff.mp hm
    rw [Finset.sum_eq_zero]
    · split_ifs with h1 h2
      · simp [hVm]
      · subst h2; simp [hVm]
      · rfl
    · intro k hk
      have hkm : k ≠ m := fun h => hm (h ▸ hk)
      split_ifs with h1 h2
      · simp [hkm]
      · subst h2; simp [hkm]
      · simp

lemma support_projNonpos_nonpos (V : TrigPoly) :
    ∀ m ∈ (projNonpos V).support, m ≤ 0 := by
  intro m hm
  rw [Finsupp.mem_support_iff, projNonpos_apply] at hm
  by_contra h
  push_neg at h
  have h1 : ¬ m < 0 := by omega
  have h2 : m ≠ 0 := by omega
  simp [h1, h2] at hm

lemma evalTP_projNonpos_re {V : TrigPoly} (hV : ∀ x, (evalTP V x).im = 0) (x : ℝ) :
    (evalTP (projNonpos V) x).re = (evalTP V x).re := by
  have hcoeff := coeff_neg_of_real_evalTP hV
  have hconj : evalTP (projNonpos V) x + starRingEnd ℂ (evalTP (projNonpos V) x) =
      2 * evalTP V x := by
    rw [← evalTP_conjTP, ← evalTP_add]
    have htp : projNonpos V + conjTP (projNonpos V) = (2 : ℂ) • V := by
      ext m
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      have hconj_apply : ∀ (p : TrigPoly) (k : ℤ), conjTP p k = starRingEnd ℂ (p (-k)) := by
        intro p k
        unfold conjTP
        rw [Finsupp.sum, Finsupp.finset_sum_apply]
        by_cases hk : -k ∈ p.support
        · rw [Finset.sum_eq_single (-k)]
          · simp
          · intro j _ hjk
            rw [Finsupp.single_apply]
            split_ifs with h <;> [omega; rfl]
          · intro h; exact absurd hk h
        · rw [Finset.sum_eq_zero]
          · simp [Finsupp.notMem_support_iff.mp hk]
          · intro j hj
            have hjk : j ≠ -k := fun h => hk (h ▸ hj)
            rw [Finsupp.single_apply]
            split_ifs with h <;> [omega; rfl]
      rw [hconj_apply, projNonpos_apply, projNonpos_apply]
      rcases lt_trichotomy m 0 with hm | rfl | hm
      · rw [if_pos hm, if_neg (by omega : ¬ -m < 0), if_neg (by omega : -m ≠ 0), map_zero, add_zero]
      · rw [if_neg (by omega : ¬ (0 : ℤ) < 0), if_pos rfl, neg_zero, if_neg (by omega : ¬ (0 : ℤ) < 0), if_pos rfl]
        have h0 : starRingEnd ℂ (V 0) = V 0 := by simpa using (hcoeff 0).symm
        rw [h0]; ring
      · rw [if_neg (by omega : ¬ m < 0), if_neg (by omega : m ≠ 0), if_pos (by omega : -m < 0),
          zero_add, map_mul, map_ofNat, hcoeff m, starRingEnd_self_apply]
    rw [htp, evalTP_smul]
  have hre := congrArg Complex.re hconj
  simp at hre
  linarith

lemma l2_projNonpos_le {V : TrigPoly} (hV : ∀ x, (evalTP V x).im = 0) :
    circleIntR (fun x => ‖evalTP (projNonpos V) x‖ ^ 2) ≤
      2 * circleIntR (fun x => ‖evalTP V x‖ ^ 2) := by
  rw [parseval_evalTP, parseval_evalTP]
  have hcoeff := coeff_neg_of_real_evalTP hV
  have hsub : (projNonpos V).support ⊆ V.support := by
    intro m hm
    rw [Finsupp.mem_support_iff, projNonpos_apply] at hm
    rw [Finsupp.mem_support_iff]
    split_ifs at hm with h1 h2
    · exact fun h => hm (by simp [h])
    · subst h2; exact hm
    · exact absurd rfl hm
  unfold Finsupp.sum
  have h1 : ∑ m ∈ (projNonpos V).support, ‖projNonpos V m‖ ^ 2 =
      ∑ m ∈ V.support, ‖projNonpos V m‖ ^ 2 := by
    refine Finset.sum_subset hsub fun m _ hm => ?_
    simp [Finsupp.notMem_support_iff.mp hm]
  rw [h1]
  have hsym : ∑ m ∈ V.support, ‖V m‖ ^ 2 = ∑ m ∈ V.support, ‖V (-m)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hcoeff m, Complex.norm_conj]
  have h2 : ∑ m ∈ V.support, ‖projNonpos V m‖ ^ 2 ≤
      ∑ m ∈ V.support, (‖V m‖ ^ 2 + ‖V (-m)‖ ^ 2) := by
    have hsplit : ∑ m ∈ V.support, ‖projNonpos V m‖ ^ 2 =
        (∑ m ∈ V.support.filter (fun m => m < 0), 4 * ‖V m‖ ^ 2) +
        (∑ m ∈ V.support.filter (fun m => m = 0), ‖V m‖ ^ 2) := by
      have hunion : V.support =
          (V.support.filter (fun m => m < 0)) ∪
          ((V.support.filter (fun m => m = 0)) ∪ (V.support.filter (fun m => 0 < m))) := by
        ext m; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hm
          rcases lt_trichotomy m 0 with h | h | h
          · exact Or.inl ⟨hm, h⟩
          · exact Or.inr (Or.inl ⟨hm, h⟩)
          · exact Or.inr (Or.inr ⟨hm, h⟩)
        · rintro (⟨hm, _⟩ | ⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
      have hd1 : Disjoint (V.support.filter (fun m => m < 0))
          ((V.support.filter (fun m => m = 0)) ∪ (V.support.filter (fun m => 0 < m))) := by
        rw [Finset.disjoint_left]; intro m hm1 hm2
        simp only [Finset.mem_filter, Finset.mem_union] at hm1 hm2; omega
      have hd2 : Disjoint (V.support.filter (fun m => m = 0))
          (V.support.filter (fun m => 0 < m)) := by
        rw [Finset.disjoint_left]; intro m hm1 hm2
        simp only [Finset.mem_filter] at hm1 hm2; omega
      conv_lhs => rw [hunion]
      rw [Finset.sum_union hd1, Finset.sum_union hd2]
      have hpos0 : ∑ m ∈ V.support.filter (fun m => 0 < m), ‖projNonpos V m‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        have hgt : 0 < m := (Finset.mem_filter.mp hm).2
        rw [projNonpos_apply, if_neg (by omega), if_neg (by omega)]
        simp
      rw [hpos0, add_zero]
      congr 1
      · refine Finset.sum_congr rfl fun m hm => ?_
        have hlt : m < 0 := (Finset.mem_filter.mp hm).2
        rw [projNonpos_apply, if_pos hlt, norm_mul]
        norm_num
        ring
      · refine Finset.sum_congr rfl fun m hm => ?_
        have heq : m = 0 := (Finset.mem_filter.mp hm).2
        subst heq
        rw [projNonpos_apply, if_neg (by omega), if_pos rfl]
    have hneg_eq_pos :
        ∑ m ∈ V.support.filter (fun m => m < 0), ‖V m‖ ^ 2 =
        ∑ m ∈ V.support.filter (fun m => 0 < m), ‖V m‖ ^ 2 := by
      refine Finset.sum_nbij (fun m => -m) ?_ ?_ ?_ ?_
      · intro m hm
        simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hm ⊢
        refine ⟨?_, by omega⟩
        rw [hcoeff m]; simp [hm.1]
      · intro a _ b _ h; exact neg_inj.mp h
      · intro m hm
        simp only [Finset.mem_coe, Finset.mem_filter, Finsupp.mem_support_iff] at hm
        refine ⟨-m, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ?_, by omega⟩), by simp⟩
        rw [hcoeff m]; simp [hm.1]
      · intro m _
        rw [hcoeff m, Complex.norm_conj]
    have htot : ∑ m ∈ V.support, ‖V m‖ ^ 2 =
        (∑ m ∈ V.support.filter (fun m => m < 0), ‖V m‖ ^ 2) +
        (∑ m ∈ V.support.filter (fun m => m = 0), ‖V m‖ ^ 2) +
        (∑ m ∈ V.support.filter (fun m => 0 < m), ‖V m‖ ^ 2) := by
      have hunion : V.support =
          (V.support.filter (fun m => m < 0)) ∪
          ((V.support.filter (fun m => m = 0)) ∪ (V.support.filter (fun m => 0 < m))) := by
        ext m; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hm
          rcases lt_trichotomy m 0 with h | h | h
          · exact Or.inl ⟨hm, h⟩
          · exact Or.inr (Or.inl ⟨hm, h⟩)
          · exact Or.inr (Or.inr ⟨hm, h⟩)
        · rintro (⟨hm, _⟩ | ⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
      have hd1 : Disjoint (V.support.filter (fun m => m < 0))
          ((V.support.filter (fun m => m = 0)) ∪ (V.support.filter (fun m => 0 < m))) := by
        rw [Finset.disjoint_left]; intro m hm1 hm2
        simp only [Finset.mem_filter, Finset.mem_union] at hm1 hm2; omega
      have hd2 : Disjoint (V.support.filter (fun m => m = 0))
          (V.support.filter (fun m => 0 < m)) := by
        rw [Finset.disjoint_left]; intro m hm1 hm2
        simp only [Finset.mem_filter] at hm1 hm2; omega
      conv_lhs => rw [hunion]
      rw [Finset.sum_union hd1, Finset.sum_union hd2, add_assoc]
    rw [Finset.sum_add_distrib, ← hsym, hsplit]
    have h0nn : 0 ≤ ∑ m ∈ V.support.filter (fun m => m = 0), ‖V m‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h4 : ∑ m ∈ V.support.filter (fun m => m < 0), 4 * ‖V m‖ ^ 2 =
        4 * ∑ m ∈ V.support.filter (fun m => m < 0), ‖V m‖ ^ 2 := by
      rw [Finset.mul_sum]
    rw [h4]
    linarith
  rw [Finset.sum_add_distrib, ← hsym] at h2
  linarith

lemma circleInt_pos_freq_exp_eq_zero (A H : TrigPoly)
    (hA : ∀ m ∈ A.support, 0 < m) (hH : ∀ m ∈ H.support, 0 ≤ m) :
    circleInt (fun x => evalTP A x * Complex.exp (evalTP H x)) = 0 := by
  have hterm : ∀ N : ℕ,
      circleInt (fun x => evalTP A x * (evalTP H x) ^ N / (N.factorial : ℂ)) = 0 := by
    intro N
    have h1 : (fun x => evalTP A x * (evalTP H x) ^ N / (N.factorial : ℂ)) =
        evalTP (((N.factorial : ℂ)⁻¹) • mulTP A (powTP H N)) := by
      ext x
      rw [evalTP_smul, evalTP_mulTP, evalTP_powTP]
      ring
    rw [h1, circleInt_evalTP, Finsupp.smul_apply, smul_eq_mul]
    have h0 : mulTP A (powTP H N) 0 = 0 := by
      by_contra hne
      obtain ⟨a, ha, b, hb, hab⟩ := support_mulTP_subset A (powTP H N) 0
        (Finsupp.mem_support_iff.mpr hne)
      have ha' := hA a ha
      have hb' := support_powTP_nonneg hH N b hb
      omega
    rw [h0, mul_zero]
  let MA : ℝ := A.sum fun _ c => ‖c‖
  let MH : ℝ := H.sum fun _ c => ‖c‖
  have hMA : 0 ≤ MA := Finsupp.sum_nonneg fun _ _ => norm_nonneg _
  have hMH : 0 ≤ MH := Finsupp.sum_nonneg fun _ _ => norm_nonneg _
  have hpart : ∀ n : ℕ,
      circleInt (fun x => ∑ k ∈ Finset.range n,
        evalTP A x * (evalTP H x) ^ k / (k.factorial : ℂ)) = 0 := by
    intro n
    rw [circleInt_finset_sum (Finset.range n)
      (fun k x => evalTP A x * (evalTP H x) ^ k / (k.factorial : ℂ))
      (fun k _ => ((continuous_evalTP A).mul ((continuous_evalTP H).pow k)).div_const _)]
    exact Finset.sum_eq_zero fun k _ => hterm k
  have hdiff : ∀ n : ℕ,
      ‖circleInt (fun x => evalTP A x * Complex.exp (evalTP H x))‖ ≤
        MA * ∑' k : ℕ, MH ^ (n + k) / ((n + k).factorial : ℝ) := by
    intro n
    have hsub : circleInt (fun x => evalTP A x * Complex.exp (evalTP H x)) =
        circleInt (fun x => evalTP A x * Complex.exp (evalTP H x) -
          ∑ k ∈ Finset.range n, evalTP A x * (evalTP H x) ^ k / (k.factorial : ℂ)) := by
      have := hpart n
      have hcont1 : Continuous (fun x => evalTP A x * Complex.exp (evalTP H x)) :=
        (continuous_evalTP A).mul (Complex.continuous_exp.comp (continuous_evalTP H))
      have hcont2 : Continuous (fun x => ∑ k ∈ Finset.range n,
          evalTP A x * (evalTP H x) ^ k / (k.factorial : ℂ)) :=
        continuous_finsetSum _ fun k _ =>
          ((continuous_evalTP A).mul ((continuous_evalTP H).pow k)).div_const _
      have hadd := circleInt_add (f := fun x => evalTP A x * Complex.exp (evalTP H x) -
            ∑ k ∈ Finset.range n, evalTP A x * (evalTP H x) ^ k / (k.factorial : ℂ))
          (g := fun x => ∑ k ∈ Finset.range n, evalTP A x * (evalTP H x) ^ k / (k.factorial : ℂ))
          (hcont1.sub hcont2) hcont2
      rw [this, add_zero] at hadd
      have hfn : (fun x => evalTP A x * Complex.exp (evalTP H x) -
            ∑ k ∈ Finset.range n, evalTP A x * (evalTP H x) ^ k / (k.factorial : ℂ) +
            ∑ k ∈ Finset.range n, evalTP A x * (evalTP H x) ^ k / (k.factorial : ℂ)) =
          fun x => evalTP A x * Complex.exp (evalTP H x) := by
        ext x; ring
      rw [hfn] at hadd
      exact hadd
    rw [hsub]
    have hcont : Continuous (fun x => evalTP A x * Complex.exp (evalTP H x) -
        ∑ k ∈ Finset.range n, evalTP A x * (evalTP H x) ^ k / (k.factorial : ℂ)) :=
      ((continuous_evalTP A).mul (Complex.continuous_exp.comp (continuous_evalTP H))).sub
        (continuous_finset_sum _ fun k _ =>
          ((continuous_evalTP A).mul ((continuous_evalTP H).pow k)).div_const _)
    refine (norm_circleInt_le _ hcont).trans ?_
    refine (circleIntR_mono hcont.norm continuous_const (fun x _ => ?_)).trans
      (by rw [circleIntR_const])
    have hexp : HasSum (fun k : ℕ => evalTP H x ^ k / (k.factorial : ℂ))
        (Complex.exp (evalTP H x)) := by
      rw [Complex.exp_eq_exp_ℂ]
      exact NormedSpace.expSeries_div_hasSum_exp (evalTP H x)
    have hrem : HasSum (fun k : ℕ => evalTP H x ^ (n + k) / ((n + k).factorial : ℂ))
        (Complex.exp (evalTP H x) - ∑ k ∈ Finset.range n, evalTP H x ^ k / (k.factorial : ℂ)) := by
      have hshift := (hasSum_nat_add_iff' n).mpr hexp
      simpa [add_comm] using hshift
    have hfactor : evalTP A x * Complex.exp (evalTP H x) -
        ∑ k ∈ Finset.range n, evalTP A x * (evalTP H x) ^ k / (k.factorial : ℂ) =
        evalTP A x * (Complex.exp (evalTP H x) -
          ∑ k ∈ Finset.range n, evalTP H x ^ k / (k.factorial : ℂ)) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hfactor, norm_mul]
    have hsum_real : Summable (fun k : ℕ => MH ^ (n + k) / ((n + k).factorial : ℝ)) := by
      have h0 : Summable (fun k : ℕ => MH ^ k / (k.factorial : ℝ)) :=
        Real.summable_pow_div_factorial MH
      simpa [add_comm] using (summable_nat_add_iff n).mpr h0
    have hle_rem : ‖Complex.exp (evalTP H x) -
        ∑ k ∈ Finset.range n, evalTP H x ^ k / (k.factorial : ℂ)‖ ≤
        ∑' k : ℕ, MH ^ (n + k) / ((n + k).factorial : ℝ) := by
      rw [← hrem.tsum_eq]
      refine (norm_tsum_le_tsum_norm ?_).trans ?_
      · exact hsum_real.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
          rw [norm_div, norm_pow, Complex.norm_natCast]
          gcongr
          exact norm_evalTP_le_l1 H x)
      · exact Summable.tsum_le_tsum (fun k => by
          rw [norm_div, norm_pow, Complex.norm_natCast]
          gcongr
          exact norm_evalTP_le_l1 H x)
          (hsum_real.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
            rw [norm_div, norm_pow, Complex.norm_natCast]
            gcongr
            exact norm_evalTP_le_l1 H x))
          hsum_real
    exact mul_le_mul (norm_evalTP_le_l1 A x) hle_rem (norm_nonneg _) hMA
  have htend : Tendsto (fun n : ℕ => MA * ∑' k : ℕ, MH ^ (n + k) / ((n + k).factorial : ℝ))
      atTop (𝓝 (MA * 0)) := by
    refine tendsto_const_nhds.mul ?_
    have h0 : Summable (fun k : ℕ => MH ^ k / (k.factorial : ℝ)) :=
      Real.summable_pow_div_factorial MH
    have htail := tendsto_sum_nat_add (fun k : ℕ => MH ^ k / (k.factorial : ℝ))
    simpa [add_comm] using htail
  rw [mul_zero] at htend
  have hle0 : ‖circleInt (fun x => evalTP A x * Complex.exp (evalTP H x))‖ ≤ 0 :=
    ge_of_tendsto' htend hdiff
  exact norm_eq_zero.mp (le_antisymm hle0 (norm_nonneg _))

/-! ### Elementary Exponential Inequalities for MPS -/

lemma norm_exp_neg_sub_one_le {z : ℂ} (hz : 0 ≤ z.re) :
    ‖Complex.exp (-z) - 1‖ ≤ ‖z‖ := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ) * z)) (-z * Complex.exp (-(t : ℂ) * z)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => -(s : ℂ) * z) (-z) t := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := t)).neg).mul_const z
      simpa using this
    simpa [mul_comm] using h1.cexp
  have hint : IntervalIntegrable (fun t : ℝ => -z * Complex.exp (-(t : ℂ) * z)) volume 0 1 :=
    (continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.neg).mul continuous_const))).intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [Complex.ofReal_one, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero,
    neg_mul, one_mul] at hftc
  rw [← hftc]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ‖z‖) ?_).trans (by simp)
  intro t ht
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  rw [norm_neg, norm_mul, Complex.norm_exp]
  have hre : (-(↑t * z)).re ≤ 0 := by
    simp only [Complex.neg_re, Complex.re_ofReal_mul]
    nlinarith [ht.1]
  have hexp : Real.exp (-(↑t * z)).re ≤ 1 := Real.exp_le_one_iff.mpr hre
  nlinarith [norm_nonneg z]

lemma self_le_two_mul_one_sub_exp_neg {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ≤ 2 * (1 - Real.exp (-s)) := by
  have hexp_ge : 1 + s + s ^ 2 / 2 ≤ Real.exp s := by
    have h2 := Real.sum_le_exp_of_nonneg hs0 3
    simp [Finset.sum_range_succ, Nat.factorial] at h2
    linarith
  have hpos : 0 < Real.exp s := Real.exp_pos s
  have hmul : (1 - s / 2) * (1 + s + s ^ 2 / 2) = 1 + s / 2 - s ^ 3 / 4 := by ring
  have hge1 : 1 ≤ (1 - s / 2) * (1 + s + s ^ 2 / 2) := by
    rw [hmul]
    have hs3 : s ^ 3 ≤ s := by nlinarith
    nlinarith
  have hge2 : 1 ≤ (1 - s / 2) * Real.exp s :=
    hge1.trans (mul_le_mul_of_nonneg_left hexp_ge (by linarith))
  have hinv : Real.exp (-s) ≤ 1 - s / 2 := by
    rw [Real.exp_neg]
    exact (inv_le_iff_one_le_mul₀ hpos).mpr (by linarith)
  linarith

lemma telescoping_exp_bound (K : ℕ) (s : ℕ → ℝ) (hs0 : ∀ k, 0 ≤ s k) (hs1 : ∀ k, s k ≤ 1) :
    ∑ k ∈ Finset.range K, s k * Real.exp (-∑ j ∈ Finset.Ico (k + 1) K, s j) ≤ 2 := by
  have hstep : ∀ k ∈ Finset.range K,
      s k * Real.exp (-∑ j ∈ Finset.Ico (k + 1) K, s j) ≤
        2 * (Real.exp (-∑ j ∈ Finset.Ico (k + 1) K, s j) -
          Real.exp (-∑ j ∈ Finset.Ico k K, s j)) := by
    intro k hk
    have hklt : k < K := Finset.mem_range.mp hk
    have hsum : ∑ j ∈ Finset.Ico k K, s j = s k + ∑ j ∈ Finset.Ico (k + 1) K, s j := by
      rw [Finset.sum_eq_sum_Ico_succ_bot hklt]
    rw [hsum, neg_add, Real.exp_add]
    have h1 := self_le_two_mul_one_sub_exp_neg (hs0 k) (hs1 k)
    have hepos : 0 < Real.exp (-∑ j ∈ Finset.Ico (k + 1) K, s j) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right h1 hepos.le
    linarith
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  have htele : ∑ k ∈ Finset.range K,
      (Real.exp (-∑ j ∈ Finset.Ico (k + 1) K, s j) -
        Real.exp (-∑ j ∈ Finset.Ico k K, s j)) =
      Real.exp (-∑ j ∈ Finset.Ico K K, s j) - Real.exp (-∑ j ∈ Finset.Ico 0 K, s j) := by
    exact Finset.sum_range_sub (fun k => Real.exp (-∑ j ∈ Finset.Ico k K, s j)) K
  rw [htele]
  simp only [Finset.Ico_self, Finset.sum_empty, neg_zero, Real.exp_zero]
  linarith [Real.exp_pos (-∑ j ∈ Finset.Ico 0 K, s j)]

/-! ### Ordered Littlewood Inequality (McGehee-Pigno-Smith 1981) -/

/-- Block start indices for R = 100: B 0 = 0, B (k+1) = B k + 100 ^ k. -/
def mpsStart : ℕ → ℕ
  | 0 => 0
  | k + 1 => mpsStart k + 100 ^ k

lemma mpsStart_strictMono : StrictMono mpsStart :=
  strictMono_nat_of_lt_succ fun k => by
    simp only [mpsStart]
    exact lt_add_of_pos_right _ (by positivity)

lemma mpsStart_eq (k : ℕ) : 99 * mpsStart k = 100 ^ k - 1 := by
  induction k with
  | zero => simp [mpsStart]
  | succ k ih =>
    simp only [mpsStart, mul_add, ih]
    have h1 : 1 ≤ 100 ^ k := Nat.one_le_pow k 100 (by norm_num)
    have h2 : 100 ^ (k + 1) = 100 ^ k * 100 := pow_succ 100 k
    omega

lemma mpsStart_le_pow (k : ℕ) : mpsStart k ≤ 100 ^ k := by
  have := mpsStart_eq k
  have h1 : 1 ≤ 100 ^ k := Nat.one_le_pow k 100 (by norm_num)
  omega

lemma pow_le_hundred_mul_rank {k i : ℕ} (hi : mpsStart k ≤ i) :
    (100 : ℝ) ^ k ≤ 100 * ((i : ℝ) + 1) := by
  have h := mpsStart_eq k
  have h1 : 100 ^ k ≤ 99 * i + 1 := by omega
  have h2 : (100 : ℝ) ^ k ≤ 99 * (i : ℝ) + 1 := by exact_mod_cast h1
  linarith

/-- Ordered Littlewood L1 lower bound (McGehee-Pigno-Smith 1981):
for strictly increasing frequencies m_0 < ... < m_{s-1} and complex coefficients c_0, ..., c_{s-1},
the normalized L1 norm on [0, 2*pi] is at least (1/400) * sum_{i=0}^{s-1} |c_i| / (i + 1). -/
theorem mps_littlewood {s : ℕ} (m : Fin s → ℤ) (hm : StrictMono m) (c : Fin s → ℂ) :
    (1 / 400 : ℝ) * (∑ i : Fin s, ‖c i‖ / ((i.val : ℝ) + 1)) ≤
      circleIntR (fun x => ‖∑ i : Fin s, c i * eChar (m i) x‖) := by
  classical
  -- Filter out zero coefficients first? Even simpler: keep only indices with c i ≠ 0 by
  -- reducing to nonzero coefficients, or note that if c i = 0 then c i / ‖c i‖ = 0 works directly!
  -- Wait: if we filter to nonzero coefficients, the rank of each nonzero coeff only DECREASES,
  -- so 1/(i'+1) >= 1/(i+1)! Let's prove it directly for arbitrary c by defining
  -- u i = if c i = 0 then 0 else c i / ‖c i‖, because |u i| <= 1 still holds!
  -- Let's check: for c i = 0, the LHS summand is 0 and the RHS contribution is 0!
  -- WAIT: for c i != 0, the block E_k has size <= 100^k, and ‖u i‖ <= 1, so ‖G_k‖_inf <= 1 and
  -- ‖G_k‖_2 <= 100^(-k/2) STILL HOLD without even filtering!
  -- And the main term at i in E_l is 100^(-l) * c i * conj(u i) = 100^(-l) * ‖c i‖!
  -- And the error term at i is bounded by (1/2) * 100^(-l) * ‖c i‖!
  -- OMG! NO FILTERING NEEDED AT ALL!
  let u : Fin s → ℂ := fun i => if c i = 0 then 0 else c i / (‖c i‖ : ℂ)
  have hu_norm : ∀ i : Fin s, ‖u i‖ ≤ 1 := by
    intro i
    dsimp [u]
    split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr h)]
  have hu_mul : ∀ i : Fin s, c i * starRingEnd ℂ (u i) = (‖c i‖ : ℂ) := by
    intro i
    dsimp [u]
    split_ifs with h
    · simp [h]
    · rw [map_div₀, Complex.conj_ofReal, mul_div_assoc', Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      have hne : (‖c i‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
      push_cast
      field_simp [hne]
  -- Choose K large enough that s ≤ mpsStart K (e.g., K = s)
  let K : ℕ := s
  have hsK : s ≤ mpsStart K := by
    have : ∀ n : ℕ, n ≤ mpsStart n := fun n => by
      induction n with
      | zero => simp [mpsStart]
      | succ n ih =>
        simp only [mpsStart]
        have : 1 ≤ 100 ^ n := Nat.one_le_pow n 100 (by norm_num)
        omega
    exact this s
  -- Block index sets E k = {i : Fin s | mpsStart k ≤ i.val ∧ i.val < mpsStart (k + 1)}
  let E : ℕ → Finset (Fin s) := fun k =>
    Finset.univ.filter fun i => mpsStart k ≤ i.val ∧ i.val < mpsStart (k + 1)
  have hE_card : ∀ k, (E k).card ≤ 100 ^ k := by
    intro k
    have hinj : Set.InjOn (fun i : Fin s => i.val) (E k : Set (Fin s)) :=
      fun a _ b _ h => Fin.ext h
    have himg : (E k).image (fun i : Fin s => i.val) ⊆ Finset.Ico (mpsStart k) (mpsStart (k + 1)) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hi).2
    calc (E k).card = ((E k).image (fun i : Fin s => i.val)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Ico (mpsStart k) (mpsStart (k + 1))).card := Finset.card_le_card himg
      _ = mpsStart (k + 1) - mpsStart k := Nat.card_Ico _ _
      _ = 100 ^ k := by simp [mpsStart]
  -- Define G k : TrigPoly
  let G : ℕ → TrigPoly := fun k =>
    ∑ i ∈ E k, Finsupp.single (m i) ((((100 : ℝ) ^ k)⁻¹ : ℝ) * u i)
  have hG_eval : ∀ k x, evalTP (G k) x =
      (((100 : ℝ) ^ k)⁻¹ : ℂ) * ∑ i ∈ E k, u i * eChar (m i) x := by
    intro k x
    dsimp [G]
    rw [evalTP_finset_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [evalTP_single]
    push_cast
    ring
  have hG_inf : ∀ k x, ‖evalTP (G k) x‖ ≤ 1 := by
    intro k x
    rw [hG_eval, norm_mul, norm_inv, norm_pow]
    have hnorm100' : ‖((100 : ℝ) : ℂ)‖ = 100 := by rw [Complex.norm_real]; norm_num
    rw [hnorm100']
    have hsum : ‖∑ i ∈ E k, u i * eChar (m i) x‖ ≤ ((E k).card : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun i _ => ?_).trans
        (by rw [Finset.sum_const, nsmul_eq_mul, mul_one])
      rw [norm_mul, norm_eChar, mul_one]
      exact hu_norm i
    have hcard : ((E k).card : ℝ) ≤ (100 : ℝ) ^ k := by exact_mod_cast hE_card k
    have hpos : (0 : ℝ) < (100 : ℝ) ^ k := by positivity
    calc ((100 : ℝ) ^ k)⁻¹ * ‖∑ i ∈ E k, u i * eChar (m i) x‖
        ≤ ((100 : ℝ) ^ k)⁻¹ * (100 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left (hsum.trans hcard) (by positivity)
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  have hG_apply : ∀ k (j : ℤ), G k j =
      if h : ∃ i ∈ E k, m i = j then
        ((((100 : ℝ) ^ k)⁻¹ : ℝ) : ℂ) * u h.choose
      else 0 := by
    intro k j
    dsimp [G]
    rw [Finsupp.finsetSum_apply]
    split_ifs with h
    · have hi₀ : h.choose ∈ E k := h.choose_spec.1
      have hm₀ : m h.choose = j := h.choose_spec.2
      rw [Finset.sum_eq_single h.choose]
      · simp [hm₀]
      · intro i _ hi
        rw [Finsupp.single_apply]
        split_ifs with heq
        · exact absurd (hm.injective (heq.trans hm₀.symm)) hi
        · rfl
      · intro hn; exact absurd hi₀ hn
    · refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finsupp.single_apply]
      split_ifs with heq
      · exact absurd ⟨i, hi, heq⟩ h
      · rfl
  have hG_l2 : ∀ k, circleIntR (fun x => ‖evalTP (G k) x‖ ^ 2) ≤ (100 : ℝ)⁻¹ ^ k := by
    intro k
    rw [parseval_evalTP]
    have hsupp : (G k).support ⊆ (E k).image m := by
      intro j hj
      rw [Finsupp.mem_support_iff, hG_apply] at hj
      split_ifs at hj with h
      · exact Finset.mem_image.mpr h
      · exact absurd rfl hj
    unfold Finsupp.sum
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsupp (fun _ _ _ => sq_nonneg _)).trans ?_
    rw [Finset.sum_image (fun a _ b _ hab => hm.injective hab)]
    have hterm : ∀ i ∈ E k, ‖G k (m i)‖ ^ 2 ≤ ((100 : ℝ) ^ k)⁻¹ ^ 2 := by
      intro i hi
      have hex : ∃ i' ∈ E k, m i' = m i := ⟨i, hi, rfl⟩
      rw [hG_apply, dif_pos hex]
      have heq : hex.choose = i := hm.injective hex.choose_spec.2
      rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have h1 : ‖u i‖ ≤ 1 := hu_norm i
      have hpos : (0 : ℝ) ≤ ((100 : ℝ) ^ k)⁻¹ := by positivity
      have h2 : (((100 : ℝ) ^ k)⁻¹) * ‖u i‖ ≤ ((100 : ℝ) ^ k)⁻¹ := by nlinarith
      exact sq_le_sq' (by nlinarith [norm_nonneg (u i)]) h2
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((E k).card : ℝ) ≤ (100 : ℝ) ^ k := by exact_mod_cast hE_card k
    have hpos : (0 : ℝ) < (100 : ℝ) ^ k := by positivity
    calc ((E k).card : ℝ) * (((100 : ℝ) ^ k)⁻¹) ^ 2
        ≤ (100 : ℝ) ^ k * (((100 : ℝ) ^ k)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = (100 : ℝ)⁻¹ ^ k := by
          rw [sq, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, inv_pow]
  -- Choose V k and J k for each k : ℕ
  have hexVJ : ∀ k : ℕ, ∃ J : TrigPoly,
      (∀ n ∈ J.support, n ≤ 0) ∧
      (∀ x, ‖evalTP (G k) x‖ ≤ (evalTP J x).re) ∧
      Real.sqrt (circleIntR (fun x => ‖evalTP J x‖ ^ 2)) ≤ 3 * (10 : ℝ)⁻¹ ^ k := by
    intro k
    obtain ⟨V, hVim, hVbound⟩ := exists_trigPoly_approx_norm (G k)
      (ε := (10 : ℝ)⁻¹ ^ k) (by positivity) (hG_inf k)
    refine ⟨projNonpos V, support_projNonpos_nonpos V, ?_, ?_⟩
    · intro x
      rw [evalTP_projNonpos_re hVim]
      exact (hVbound x).1
    · have hVl2 : circleIntR (fun x => ‖evalTP V x‖ ^ 2) ≤ 4 * (100 : ℝ)⁻¹ ^ k := by
        have hpt : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
            ‖evalTP V x‖ ^ 2 ≤ 2 * ‖evalTP (G k) x‖ ^ 2 + 2 * ((10 : ℝ)⁻¹ ^ k) ^ 2 := by
          intro x _
          have hnormV : ‖evalTP V x‖ = (evalTP V x).re := by
            have hre0 : 0 ≤ (evalTP V x).re := (norm_nonneg _).trans (hVbound x).1
            have hEq : evalTP V x = ((evalTP V x).re : ℂ) := Complex.ext rfl (by simp [hVim x])
            conv_lhs => rw [hEq]
            rw [Complex.norm_real, Real.norm_of_nonneg hre0]
          rw [hnormV]
          have hle := (hVbound x).2
          have hnn : 0 ≤ (evalTP V x).re := (norm_nonneg _).trans (hVbound x).1
          nlinarith [sq_nonneg (‖evalTP (G k) x‖ - (10 : ℝ)⁻¹ ^ k)]
        have hGcont2 : Continuous (fun x => 2 * ‖evalTP (G k) x‖ ^ 2) :=
          continuous_const.mul ((continuous_evalTP (G k)).norm.pow 2)
        refine (circleIntR_mono (f := fun x => ‖evalTP V x‖ ^ 2)
          (g := fun x => 2 * ‖evalTP (G k) x‖ ^ 2 + 2 * ((10 : ℝ)⁻¹ ^ k) ^ 2)
          ((continuous_evalTP V).norm.pow 2)
          (hGcont2.add continuous_const) hpt).trans ?_
        rw [circleIntR_add (f := fun x => 2 * ‖evalTP (G k) x‖ ^ 2)
          (g := fun _ => 2 * ((10 : ℝ)⁻¹ ^ k) ^ 2) hGcont2 continuous_const,
          circleIntR_const_mul, circleIntR_const]
        have h10 : ((10 : ℝ)⁻¹ ^ k) ^ 2 = (100 : ℝ)⁻¹ ^ k := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [h10]
        linarith [hG_l2 k]
      have hJl2 : circleIntR (fun x => ‖evalTP (projNonpos V) x‖ ^ 2) ≤ 9 * ((10 : ℝ)⁻¹ ^ k) ^ 2 := by
        have h10 : ((10 : ℝ)⁻¹ ^ k) ^ 2 = (100 : ℝ)⁻¹ ^ k := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [h10]
        have hpos : (0 : ℝ) ≤ (100 : ℝ)⁻¹ ^ k := by positivity
        linarith [l2_projNonpos_le hVim, hVl2]
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      linarith [show (3 * (10 : ℝ)⁻¹ ^ k) ^ 2 = 9 * ((10 : ℝ)⁻¹ ^ k) ^ 2 by ring]
  choose J hJsupp hJre hJl2 using hexVJ
  -- Define W(x) = ∑ k < K, G_k(x) * exp(- ∑ j ∈ Ico (k+1) K, J_j(x))
  let W : ℝ → ℂ := fun x =>
    ∑ k ∈ Finset.range K, evalTP (G k) x *
      Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, evalTP (J j) x)
  have hW_cont : Continuous W :=
    continuous_finset_sum _ fun k _ =>
      (continuous_evalTP (G k)).mul (Complex.continuous_exp.comp
        ((continuous_finset_sum _ fun j _ => continuous_evalTP (J j)).neg))
  have hW_inf : ∀ x, ‖W x‖ ≤ 2 := by
    intro x
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => ?_).trans
      (telescoping_exp_bound K (fun k => ‖evalTP (G k) x‖)
        (fun k => norm_nonneg _) (fun k => hG_inf k x))
    rw [norm_mul, Complex.norm_exp]
    have hre : (-∑ j ∈ Finset.Ico (k + 1) K, evalTP (J j) x).re ≤
        -∑ j ∈ Finset.Ico (k + 1) K, ‖evalTP (G j) x‖ := by
      rw [Complex.neg_re, Complex.re_sum]
      linarith [Finset.sum_le_sum (s := Finset.Ico (k + 1) K) fun j _ => hJre j x]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre) (norm_nonneg _)
  -- Main pairing: Re(circleInt (f * conj W)) ≤ 2 * ‖f‖_1
  let f : ℝ → ℂ := fun x => ∑ i : Fin s, c i * eChar (m i) x
  have hf_cont : Continuous f :=
    continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_eChar (m i))
  have hpair_upper : (circleInt (fun x => f x * starRingEnd ℂ (W x))).re ≤
      2 * circleIntR (fun x => ‖f x‖) := by
    have hWconj : Continuous (fun x => starRingEnd ℂ (W x)) := Complex.continuous_conj.comp hW_cont
    calc (circleInt (fun x => f x * starRingEnd ℂ (W x))).re
        ≤ ‖circleInt (fun x => f x * starRingEnd ℂ (W x))‖ := Complex.re_le_norm _
      _ ≤ circleIntR (fun x => ‖f x * starRingEnd ℂ (W x)‖) :=
          norm_circleInt_le _ (hf_cont.mul hWconj)
      _ ≤ circleIntR (fun x => 2 * ‖f x‖) :=
          circleIntR_mono (hf_cont.mul hWconj).norm (hf_cont.norm.const_mul 2) (fun x _ => by
            rw [norm_mul, Complex.norm_conj]
            nlinarith [hW_inf x, norm_nonneg (f x)])
      _ = 2 * circleIntR (fun x => ‖f x‖) := circleIntR_const_mul 2 _
  -- Evaluate Fourier coefficient of conj W at each m i (with i ∈ E l)
  have hcoeff_lower : ∀ (l : ℕ) (i : Fin s), i ∈ E l → l < K →
      ((1 / 2 : ℝ) * (100 : ℝ)⁻¹ ^ l) * ‖c i‖ ≤
        (circleInt (fun x => c i * eChar (m i) x * starRingEnd ℂ (W x))).re := by
    intro l i hi hlK
    have hexpand : (fun x => eChar (m i) x * starRingEnd ℂ (W x)) =
        fun x => ∑ k ∈ Finset.range K,
          eChar (m i) x * starRingEnd ℂ (evalTP (G k) x) *
            Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x)) := by
      ext x
      dsimp [W]
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, ← Complex.exp_conj, map_neg, map_sum, mul_assoc]
    have hsplit : circleInt (fun x => eChar (m i) x * starRingEnd ℂ (W x)) =
        ∑ k ∈ Finset.range K, circleInt (fun x =>
          eChar (m i) x * starRingEnd ℂ (evalTP (G k) x) *
            Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x))) := by
      rw [hexpand]
      exact circleInt_finset_sum _ _ fun k _ =>
        ((continuous_eChar (m i)).mul (Complex.continuous_conj.comp (continuous_evalTP (G k)))).mul
          (Complex.continuous_exp.comp
            ((continuous_finsetSum _ fun j _ =>
              Complex.continuous_conj.comp (continuous_evalTP (J j))).neg))
    -- For k < l, the term is 0 by positive-frequency vanishing
    have hlt_zero : ∀ k ∈ Finset.range K, k < l →
        circleInt (fun x =>
          eChar (m i) x * starRingEnd ℂ (evalTP (G k) x) *
            Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x))) = 0 := by
      intro k _ hkl
      let A : TrigPoly := mulTP (Finsupp.single (m i) 1) (conjTP (G k))
      let H : TrigPoly := -∑ j ∈ Finset.Ico (k + 1) K, conjTP (J j)
      have hfn : (fun x =>
          eChar (m i) x * starRingEnd ℂ (evalTP (G k) x) *
            Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x))) =
          fun x => evalTP A x * Complex.exp (evalTP H x) := by
        ext x
        dsimp [A, H]
        rw [evalTP_mulTP, evalTP_single, one_mul, evalTP_conjTP, evalTP_neg, evalTP_finset_sum]
        congr 3
        rw [evalTP_finset_sum]
        refine Finset.sum_congr rfl fun j _ => (evalTP_conjTP (J j) x).symm
      rw [hfn]
      refine circleInt_pos_freq_exp_eq_zero A H ?_ ?_
      · intro n hn
        obtain ⟨a, ha, b, hb, rfl⟩ := support_mulTP_subset _ _ n hn
        have ha' : a = m i := by
          have := Finsupp.support_single_subset ha
          exact Finset.mem_singleton.mp this
        obtain ⟨b', hb', rfl⟩ := support_conjTP_subset _ b hb
        rw [Finsupp.mem_support_iff, hG_apply] at hb'
        split_ifs at hb' with hex
        · have hi' : hex.choose ∈ E k := hex.choose_spec.1
          have hmi' : m hex.choose = b' := hex.choose_spec.2
          have hi_lt : hex.choose < i := by
            have h1 := (Finset.mem_filter.mp hi').2.2
            have h2 := (Finset.mem_filter.mp hi).2.1
            have h3 : mpsStart (k + 1) ≤ mpsStart l :=
              mpsStart_strictMono.monotone (by omega)
            exact Fin.lt_def.mpr (by omega)
          have hmlt := hm hi_lt
          omega
        · exact absurd rfl hb'
      · intro n hn
        have hn' : n ∈ (∑ j ∈ Finset.Ico (k + 1) K, conjTP (J j)).support := by
          simpa [H] using hn
        rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at hn'
        obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
        obtain ⟨r, hr, rfl⟩ := support_conjTP_subset _ n (Finsupp.mem_support_iff.mpr hj)
        linarith [hJsupp j r hr]
    -- For k ≥ l, compare with circleInt (eChar (m i) * conj (G k))
    have hmain : ∀ k ∈ Finset.range K,
        circleInt (fun x => eChar (m i) x * starRingEnd ℂ (evalTP (G k) x)) =
          if k = l then ((((100 : ℝ) ^ l)⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (u i) else 0 := by
      intro k _
      have h1 : (fun x => eChar (m i) x * starRingEnd ℂ (evalTP (G k) x)) =
          fun x => evalTP (Finsupp.single (m i) 1) x * starRingEnd ℂ (evalTP (G k) x) := by
        ext x; rw [evalTP_single, one_mul]
      rw [h1, circleInt_evalTP_mul_conj, Finsupp.sum_single_index (by simp), one_mul, hG_apply]
      by_cases hkl : k = l
      · subst hkl
        have hex : ∃ i' ∈ E k, m i' = m i := ⟨i, hi, rfl⟩
        rw [dif_pos hex, if_pos rfl]
        have heq : hex.choose = i := hm.injective hex.choose_spec.2
        rw [heq, map_mul, Complex.conj_ofReal]
      · rw [if_neg hkl]
        have hnex : ¬ ∃ i' ∈ E k, m i' = m i := by
          rintro ⟨i', hi', hmi'⟩
          have heq : i' = i := hm.injective hmi'
          subst heq
          have h1 := (Finset.mem_filter.mp hi).2
          have h2 := (Finset.mem_filter.mp hi').2
          rcases lt_or_gt_of_ne hkl with hlt | hgt
          · have := mpsStart_strictMono.monotone (show k + 1 ≤ l by omega); omega
          · have := mpsStart_strictMono.monotone (show l + 1 ≤ k by omega); omega
        rw [dif_neg hnex, map_zero]
    -- Error bound for each k ≥ l
    have herr_k : ∀ k ∈ Finset.range K,
        ‖circleInt (fun x =>
          eChar (m i) x * starRingEnd ℂ (evalTP (G k) x) *
            (Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x)) - 1))‖ ≤
          (10 : ℝ)⁻¹ ^ k * (∑ j ∈ Finset.Ico (k + 1) K, 3 * (10 : ℝ)⁻¹ ^ j) := by
      intro k _
      let D : ℝ → ℂ := fun x => ∑ j ∈ Finset.Ico (k + 1) K, evalTP (J j) x
      have hD_cont : Continuous D :=
        continuous_finsetSum _ fun j _ => continuous_evalTP (J j)
      have hcont : Continuous (fun x =>
          eChar (m i) x * starRingEnd ℂ (evalTP (G k) x) *
            (Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x)) - 1)) :=
        ((continuous_eChar (m i)).mul (Complex.continuous_conj.comp (continuous_evalTP (G k)))).mul
          ((Complex.continuous_exp.comp
            ((continuous_finsetSum _ fun j _ =>
              Complex.continuous_conj.comp (continuous_evalTP (J j))).neg)).sub
            continuous_const)
      refine (norm_circleInt_le _ hcont).trans ?_
      have hpt : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
          ‖eChar (m i) x * starRingEnd ℂ (evalTP (G k) x) *
            (Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x)) - 1)‖ ≤
            ∑ j ∈ Finset.Ico (k + 1) K, |‖evalTP (G k) x‖ * ‖evalTP (J j) x‖| := by
        intro x _
        rw [norm_mul, norm_mul, norm_eChar, one_mul, Complex.norm_conj]
        have hDconj : -∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x) =
            -(starRingEnd ℂ (D x)) := by
          dsimp [D]; rw [map_sum]
        rw [hDconj]
        have hDre : 0 ≤ (starRingEnd ℂ (D x)).re := by
          rw [Complex.conj_re]
          dsimp [D]
          rw [Complex.re_sum]
          exact Finset.sum_nonneg fun j _ => (norm_nonneg _).trans (hJre j x)
        have hexp_le := norm_exp_neg_sub_one_le hDre
        rw [Complex.norm_conj] at hexp_le
        have hDnorm : ‖D x‖ ≤ ∑ j ∈ Finset.Ico (k + 1) K, ‖evalTP (J j) x‖ := norm_sum_le _ _
        calc ‖evalTP (G k) x‖ * ‖Complex.exp (-starRingEnd ℂ (D x)) - 1‖
            ≤ ‖evalTP (G k) x‖ * ∑ j ∈ Finset.Ico (k + 1) K, ‖evalTP (J j) x‖ :=
              mul_le_mul_of_nonneg_left (hexp_le.trans hDnorm) (norm_nonneg _)
          _ = ∑ j ∈ Finset.Ico (k + 1) K, |‖evalTP (G k) x‖ * ‖evalTP (J j) x‖| := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      refine (circleIntR_mono (f := fun x => ‖eChar (m i) x * starRingEnd ℂ (evalTP (G k) x) *
            (Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x)) - 1)‖)
        (g := fun x => ∑ j ∈ Finset.Ico (k + 1) K, |‖evalTP (G k) x‖ * ‖evalTP (J j) x‖|)
        hcont.norm
        (continuous_finsetSum _ fun j _ =>
          ((continuous_evalTP (G k)).norm.mul (continuous_evalTP (J j)).norm).abs) hpt).trans ?_
      have hsum_int : circleIntR (fun x => ∑ j ∈ Finset.Ico (k + 1) K,
            |‖evalTP (G k) x‖ * ‖evalTP (J j) x‖|) =
          ∑ j ∈ Finset.Ico (k + 1) K,
            circleIntR (fun x => |‖evalTP (G k) x‖ * ‖evalTP (J j) x‖|) := by
        unfold circleIntR
        have hint : ∀ j ∈ Finset.Ico (k + 1) K,
            IntervalIntegrable (fun x => |‖evalTP (G k) x‖ * ‖evalTP (J j) x‖|) volume 0 (2 * Real.pi) :=
          fun j _ => (((continuous_evalTP (G k)).norm.mul (continuous_evalTP (J j)).norm).abs).intervalIntegrable
            0 (2 * Real.pi)
        rw [intervalIntegral.integral_finsetSum hint, Finset.mul_sum]
      rw [hsum_int, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have hcs := circleIntR_cauchy_schwarz (continuous_evalTP (G k)).norm (continuous_evalTP (J j)).norm
      have hGsq : Real.sqrt (circleIntR (fun x => ‖evalTP (G k) x‖ ^ 2)) ≤ (10 : ℝ)⁻¹ ^ k := by
        refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
        have h10 : ((10 : ℝ)⁻¹ ^ k) ^ 2 = (100 : ℝ)⁻¹ ^ k := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [h10]
        exact hG_l2 k
      exact hcs.trans (mul_le_mul hGsq (hJl2 j) (Real.sqrt_nonneg _) (by positivity))
    -- Geometric series sum over k ≥ l
    have herr_sum : ∑ k ∈ Finset.Ico l K,
        (10 : ℝ)⁻¹ ^ k * (∑ j ∈ Finset.Ico (k + 1) K, 3 * (10 : ℝ)⁻¹ ^ j) ≤
        (1 / 2 : ℝ) * (100 : ℝ)⁻¹ ^ l := by
      have hinner : ∀ k, ∑ j ∈ Finset.Ico (k + 1) K, 3 * (10 : ℝ)⁻¹ ^ j ≤
          (1 / 3 : ℝ) * (10 : ℝ)⁻¹ ^ k := by
        intro k
        rw [← Finset.mul_sum]
        have hgeom : ∑ j ∈ Finset.Ico (k + 1) K, (10 : ℝ)⁻¹ ^ j ≤
            (1 / 9 : ℝ) * (10 : ℝ)⁻¹ ^ k := by
          by_cases hkK : k + 1 ≤ K
          · have hshift : ∑ j ∈ Finset.Ico (k + 1) K, (10 : ℝ)⁻¹ ^ j =
                (10 : ℝ)⁻¹ ^ (k + 1) * ∑ t ∈ Finset.range (K - (k + 1)), (10 : ℝ)⁻¹ ^ t := by
              rw [Finset.mul_sum]
              refine Finset.sum_nbij (fun j => j - (k + 1)) ?_ ?_ ?_ ?_
              · intro j hj
                simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
              · intro a ha b hb hab
                simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
                dsimp only at hab; omega
              · intro t ht
                simp only [Finset.mem_coe, Finset.mem_range] at ht
                exact ⟨t + (k + 1), Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨by omega, by omega⟩),
                  by dsimp only; omega⟩
              · intro j hj
                simp only [Finset.mem_Ico] at hj
                rw [← pow_add, show k + 1 + (j - (k + 1)) = j by omega]
            rw [hshift, geom_sum_eq (by norm_num : (10 : ℝ)⁻¹ ≠ 1)]
            have h1 : ((10 : ℝ)⁻¹ ^ (K - (k + 1)) - 1) / ((10 : ℝ)⁻¹ - 1) ≤ 10 / 9 := by
              have hnn : 0 ≤ (10 : ℝ)⁻¹ ^ (K - (k + 1)) := by positivity
              linarith [show ((10 : ℝ)⁻¹ ^ (K - (k + 1)) - 1) / ((10 : ℝ)⁻¹ - 1) =
                (1 - (10 : ℝ)⁻¹ ^ (K - (k + 1))) * (10 / 9) by ring]
            calc (10 : ℝ)⁻¹ ^ (k + 1) * (((10 : ℝ)⁻¹ ^ (K - (k + 1)) - 1) / ((10 : ℝ)⁻¹ - 1))
                ≤ (10 : ℝ)⁻¹ ^ (k + 1) * (10 / 9) :=
                  mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = (1 / 9 : ℝ) * (10 : ℝ)⁻¹ ^ k := by rw [pow_succ]; ring
          · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
            positivity
        linarith
      refine (Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (hinner k) (by positivity)).trans ?_
      have hterm2 : ∀ k, (10 : ℝ)⁻¹ ^ k * ((1 / 3 : ℝ) * (10 : ℝ)⁻¹ ^ k) =
          (1 / 3 : ℝ) * (100 : ℝ)⁻¹ ^ k := by
        intro k
        have h10 : (10 : ℝ)⁻¹ ^ k * (10 : ℝ)⁻¹ ^ k = (100 : ℝ)⁻¹ ^ k := by
          rw [← mul_pow]; norm_num
        linarith
      simp_rw [hterm2, ← Finset.mul_sum]
      have hgeom2 : ∑ k ∈ Finset.Ico l K, (100 : ℝ)⁻¹ ^ k ≤
          (100 / 99 : ℝ) * (100 : ℝ)⁻¹ ^ l := by
        have hshift : ∑ k ∈ Finset.Ico l K, (100 : ℝ)⁻¹ ^ k =
            (100 : ℝ)⁻¹ ^ l * ∑ t ∈ Finset.range (K - l), (100 : ℝ)⁻¹ ^ t := by
          rw [Finset.mul_sum]
          refine Finset.sum_nbij (fun k => k - l) ?_ ?_ ?_ ?_
          · intro k hk
            simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢; omega
          · intro a ha b hb hab
            simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
            dsimp only at hab; omega
          · intro t ht
            simp only [Finset.mem_coe, Finset.mem_range] at ht
            exact ⟨t + l, Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨by omega, by omega⟩),
              by dsimp only; omega⟩
          · intro k hk
            simp only [Finset.mem_Ico] at hk
            rw [← pow_add, show l + (k - l) = k by omega]
        rw [hshift, geom_sum_eq (by norm_num : (100 : ℝ)⁻¹ ≠ 1)]
        have h1 : ((100 : ℝ)⁻¹ ^ (K - l) - 1) / ((100 : ℝ)⁻¹ - 1) ≤ 100 / 99 := by
          have hnn : 0 ≤ (100 : ℝ)⁻¹ ^ (K - l) := by positivity
          linarith [show ((100 : ℝ)⁻¹ ^ (K - l) - 1) / ((100 : ℝ)⁻¹ - 1) =
            (1 - (100 : ℝ)⁻¹ ^ (K - l)) * (100 / 99) by ring]
        calc (100 : ℝ)⁻¹ ^ l * (((100 : ℝ)⁻¹ ^ (K - l) - 1) / ((100 : ℝ)⁻¹ - 1))
            ≤ (100 : ℝ)⁻¹ ^ l * (100 / 99) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (100 / 99 : ℝ) * (100 : ℝ)⁻¹ ^ l := by ring
      have hpos : (0 : ℝ) ≤ (100 : ℝ)⁻¹ ^ l := by positivity
      nlinarith
    -- Combine main term + error term
    have hdiff_eq : circleInt (fun x => eChar (m i) x * starRingEnd ℂ (W x)) -
        ((((100 : ℝ) ^ l)⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (u i) =
        ∑ k ∈ Finset.Ico l K, circleInt (fun x =>
          eChar (m i) x * starRingEnd ℂ (evalTP (G k) x) *
            (Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x)) - 1)) := by
      rw [hsplit]
      have hrange : Finset.range K = Finset.range l ∪ Finset.Ico l K := by
        ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.range l) (Finset.Ico l K) := by
        rw [Finset.disjoint_left]; intro k hk1 hk2
        simp only [Finset.mem_range, Finset.mem_Ico] at hk1 hk2; omega
      rw [hrange, Finset.sum_union hdisj]
      have hfirst0 : ∑ k ∈ Finset.range l, circleInt (fun x =>
          eChar (m i) x * starRingEnd ℂ (evalTP (G k) x) *
            Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x))) = 0 :=
        Finset.sum_eq_zero fun k hk =>
          hlt_zero k (Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hk) hlK))
            (Finset.mem_range.mp hk)
      rw [hfirst0, zero_add]
      have hmain_sum : ((((100 : ℝ) ^ l)⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (u i) =
          ∑ k ∈ Finset.Ico l K, circleInt (fun x => eChar (m i) x * starRingEnd ℂ (evalTP (G k) x)) := by
        rw [Finset.sum_eq_single l]
        · rw [hmain l (Finset.mem_range.mpr hlK), if_pos rfl]
        · intro k hk hkl
          rw [hmain k (Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2), if_neg hkl]
        · intro h; exact absurd (Finset.mem_Ico.mpr ⟨le_rfl, hlK⟩) h
      rw [hmain_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hcontA : Continuous (fun x => eChar (m i) x * starRingEnd ℂ (evalTP (G k) x) *
          (Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x)) - 1)) :=
        ((continuous_eChar (m i)).mul (Complex.continuous_conj.comp (continuous_evalTP (G k)))).mul
          ((Complex.continuous_exp.comp
            ((continuous_finsetSum _ fun j _ =>
              Complex.continuous_conj.comp (continuous_evalTP (J j))).neg)).sub
            continuous_const)
      have hcontB : Continuous (fun x => eChar (m i) x * starRingEnd ℂ (evalTP (G k) x)) :=
        (continuous_eChar (m i)).mul (Complex.continuous_conj.comp (continuous_evalTP (G k)))
      have hadd := circleInt_add hcontA hcontB
      have hfn : (fun x =>
          eChar (m i) x * starRingEnd ℂ (evalTP (G k) x) *
            (Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x)) - 1) +
          eChar (m i) x * starRingEnd ℂ (evalTP (G k) x)) =
          fun x => eChar (m i) x * starRingEnd ℂ (evalTP (G k) x) *
            Complex.exp (-∑ j ∈ Finset.Ico (k + 1) K, starRingEnd ℂ (evalTP (J j) x)) := by
        ext x; ring
      rw [hfn] at hadd
      exact (eq_sub_of_add_eq hadd.symm).symm
    have herr_tot : ‖circleInt (fun x => eChar (m i) x * starRingEnd ℂ (W x)) -
        ((((100 : ℝ) ^ l)⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (u i)‖ ≤ (1 / 2 : ℝ) * (100 : ℝ)⁻¹ ^ l := by
      rw [hdiff_eq]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun k hk =>
        herr_k k (Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2)).trans herr_sum
    have hmul_eq : circleInt (fun x => c i * eChar (m i) x * starRingEnd ℂ (W x)) =
        (((100 : ℝ)⁻¹ ^ l * ‖c i‖ : ℝ) : ℂ) +
          c i * (circleInt (fun x => eChar (m i) x * starRingEnd ℂ (W x)) -
            ((((100 : ℝ) ^ l)⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (u i)) := by
      have h1 : (fun x => c i * eChar (m i) x * starRingEnd ℂ (W x)) =
          fun x => c i * (eChar (m i) x * starRingEnd ℂ (W x)) := by ext x; ring
      rw [h1, circleInt_const_mul, mul_sub]
      have h2 : c i * (((((100 : ℝ) ^ l)⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (u i)) =
          (((100 : ℝ)⁻¹ ^ l * ‖c i‖ : ℝ) : ℂ) := by
        rw [show c i * (((((100 : ℝ) ^ l)⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (u i)) =
          ((((100 : ℝ) ^ l)⁻¹ : ℝ) : ℂ) * (c i * starRingEnd ℂ (u i)) by ring, hu_mul, inv_pow]
        push_cast; rfl
      rw [h2]; ring
    rw [hmul_eq, Complex.add_re, Complex.ofReal_re]
    set errZ : ℂ := circleInt (fun x => eChar (m i) x * starRingEnd ℂ (W x)) -
        ((((100 : ℝ) ^ l)⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (u i)
    have hre_err : -(c i * errZ).re ≤ (1 / 2 : ℝ) * (100 : ℝ)⁻¹ ^ l * ‖c i‖ := by
      calc -(c i * errZ).re
          = (-(c i * errZ)).re := by rw [Complex.neg_re]
        _ ≤ ‖-(c i * errZ)‖ := Complex.re_le_norm _
        _ = ‖c i‖ * ‖errZ‖ := by rw [norm_neg, norm_mul]
        _ ≤ ‖c i‖ * ((1 / 2 : ℝ) * (100 : ℝ)⁻¹ ^ l) :=
            mul_le_mul_of_nonneg_left herr_tot (norm_nonneg _)
        _ = (1 / 2 : ℝ) * (100 : ℝ)⁻¹ ^ l * ‖c i‖ := by ring
    linarith
  -- Sum over all i : Fin s (partitioned into blocks E l for l < K)
  have hpart_univ : ∀ i : Fin s, ∃ l < K, i ∈ E l := by
    intro i
    have hiK : i.val < mpsStart K := lt_of_lt_of_le i.isLt hsK
    have hex : ∀ N : ℕ, i.val < mpsStart N →
        ∃ l, l < N ∧ mpsStart l ≤ i.val ∧ i.val < mpsStart (l + 1) := by
      intro N
      induction N with
      | zero => intro h; simp [mpsStart] at h
      | succ N' ih =>
        intro hN
        by_cases hlt : i.val < mpsStart N'
        · obtain ⟨l, hl, h1, h2⟩ := ih hlt
          exact ⟨l, by omega, h1, h2⟩
        · exact ⟨N', by omega, by omega, hN⟩
    obtain ⟨l, hl, h1, h2⟩ := hex K hiK
    exact ⟨l, hl, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩⟩
  have hsum_lower : (1 / 200 : ℝ) * (∑ i : Fin s, ‖c i‖ / ((i.val : ℝ) + 1)) ≤
      (circleInt (fun x => f x * starRingEnd ℂ (W x))).re := by
    have hfn : (fun x => f x * starRingEnd ℂ (W x)) =
        fun x => ∑ i : Fin s, c i * eChar (m i) x * starRingEnd ℂ (W x) := by
      ext x; dsimp [f]; rw [Finset.sum_mul]
    rw [hfn, circleInt_finset_sum Finset.univ
      (fun i x => c i * eChar (m i) x * starRingEnd ℂ (W x))
      (fun i _ => (continuous_const.mul (continuous_eChar (m i))).mul
        (Complex.continuous_conj.comp hW_cont)),
      Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨l, hlK, hi⟩ := hpart_univ i
    have hrank := pow_le_hundred_mul_rank (Finset.mem_filter.mp hi).2.1
    have hinv : (1 / 200 : ℝ) / ((i.val : ℝ) + 1) ≤ (1 / 2 : ℝ) * (100 : ℝ)⁻¹ ^ l := by
      rw [inv_pow]
      have hpos1 : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
      have hpos2 : (0 : ℝ) < (100 : ℝ) ^ l := by positivity
      rw [div_le_iff₀ hpos1]
      have : (1 / 2 : ℝ) * ((100 : ℝ) ^ l)⁻¹ * ((i.val : ℝ) + 1) =
          (1 / 200 : ℝ) * (100 * ((i.val : ℝ) + 1)) / (100 : ℝ) ^ l := by ring
      rw [this, le_div_iff₀ hpos2]
      linarith
    calc (1 / 200 : ℝ) * (‖c i‖ / ((i.val : ℝ) + 1))
        = (1 / 200 : ℝ) / ((i.val : ℝ) + 1) * ‖c i‖ := by ring
      _ ≤ (1 / 2 : ℝ) * (100 : ℝ)⁻¹ ^ l * ‖c i‖ :=
          mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
      _ ≤ (circleInt (fun x => c i * eChar (m i) x * starRingEnd ℂ (W x))).re :=
          hcoeff_lower l i hi hlK
  linarith

/- ### Section 2: Sign-Change Polynomial and Finite Zero Set -/

lemma l1_mulTP_le (p q : TrigPoly) :
    ((mulTP p q).sum fun _ c => ‖c‖) ≤ (p.sum fun _ c => ‖c‖) * (q.sum fun _ c => ‖c‖) := by
  unfold mulTP
  have h1 : ∀ (a : TrigPoly) (b : TrigPoly),
      ((a + b).sum fun _ c => ‖c‖) ≤ (a.sum fun _ c => ‖c‖) + (b.sum fun _ c => ‖c‖) := by
    intro a b
    unfold Finsupp.sum
    have hsub : (a + b).support ⊆ a.support ∪ b.support := Finsupp.support_add
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)).trans ?_
    have hle : ∑ m ∈ a.support ∪ b.support, ‖(a + b) m‖ ≤
        ∑ m ∈ a.support ∪ b.support, (‖a m‖ + ‖b m‖) :=
      Finset.sum_le_sum fun m _ => norm_add_le (a m) (b m)
    refine hle.trans ?_
    rw [Finset.sum_add_distrib]
    have ha : ∑ m ∈ a.support ∪ b.support, ‖a m‖ = ∑ m ∈ a.support, ‖a m‖ := by
      refine (Finset.sum_subset Finset.subset_union_left ?_).symm
      intro m _ hm; simp [Finsupp.notMem_support_iff.mp hm]
    have hb : ∑ m ∈ a.support ∪ b.support, ‖b m‖ = ∑ m ∈ b.support, ‖b m‖ := by
      refine (Finset.sum_subset Finset.subset_union_right ?_).symm
      intro m _ hm; simp [Finsupp.notMem_support_iff.mp hm]
    rw [ha, hb]
  have hfin : ∀ {ι : Type} (s : Finset ι) (f : ι → TrigPoly),
      ((∑ i ∈ s, f i).sum fun _ c => ‖c‖) ≤ ∑ i ∈ s, ((f i).sum fun _ c => ‖c‖) := by
    intro ι s f
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h1 _ _).trans (add_le_add_right ih _)
  change ((∑ m ∈ p.support, q.sum fun n b => Finsupp.single (m + n) (p m * b)).sum fun _ c => ‖c‖) ≤ _
  refine (hfin _ _).trans ?_
  have hinner : ∀ m ∈ p.support,
      ((q.sum fun n b => Finsupp.single (m + n) (p m * b)).sum fun _ c => ‖c‖) ≤
        ‖p m‖ * (q.sum fun _ c => ‖c‖) := by
    intro m _
    rw [Finsupp.sum]
    refine (hfin _ _).trans ?_
    unfold Finsupp.sum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    dsimp only
    have hsing : ((Finsupp.single (m + n) (p m * q n)).sum fun _ c => ‖c‖) = ‖p m * q n‖ :=
      Finsupp.sum_single_index (by simp)
    unfold Finsupp.sum at hsing
    rw [hsing, norm_mul]
  refine (Finset.sum_le_sum hinner).trans ?_
  unfold Finsupp.sum
  rw [← Finset.sum_mul]

/-- The single sign-change factor 2*(cos x - cos t) as a TrigPoly. -/
noncomputable def factorTP (t : ℝ) : TrigPoly :=
  Finsupp.single 1 1 + Finsupp.single 0 (((-2 * Real.cos t : ℝ) : ℂ)) + Finsupp.single (-1) 1

lemma evalTP_factorTP (t x : ℝ) :
    evalTP (factorTP t) x = ((2 * (Real.cos x - Real.cos t) : ℝ) : ℂ) := by
  unfold factorTP
  rw [evalTP_add, evalTP_add, evalTP_single, evalTP_single, evalTP_single, eChar_zero]
  have hcos : eChar 1 x + eChar (-1) x = ((2 * Real.cos x : ℝ) : ℂ) := by
    unfold eChar
    push_cast
    rw [Complex.cos, show Complex.I * 1 * (x : ℂ) = (x : ℂ) * Complex.I by ring,
      show Complex.I * (-1) * (x : ℂ) = -((x : ℂ) * Complex.I) by ring]
    ring
  have : 1 * eChar 1 x + ((-2 * Real.cos t : ℝ) : ℂ) * 1 + 1 * eChar (-1) x =
      (eChar 1 x + eChar (-1) x) + ((-2 * Real.cos t : ℝ) : ℂ) := by ring
  rw [this, hcos]
  push_cast
  ring

lemma support_factorTP (t : ℝ) : ∀ k ∈ (factorTP t).support, -1 ≤ k ∧ k ≤ 1 := by
  intro k hk
  unfold factorTP at hk
  have h1 := Finsupp.support_add hk
  rcases Finset.mem_union.mp h1 with h12 | h3
  · rcases Finset.mem_union.mp (Finsupp.support_add h12) with h1' | h2'
    · have := Finset.mem_singleton.mp (Finsupp.support_single_subset h1'); omega
    · have := Finset.mem_singleton.mp (Finsupp.support_single_subset h2'); omega
  · have := Finset.mem_singleton.mp (Finsupp.support_single_subset h3); omega

lemma factorTP_top (t : ℝ) : factorTP t 1 = 1 := by
  simp [factorTP, Finsupp.single_apply]

lemma factorTP_real (t : ℝ) (k : ℤ) : (factorTP t k).im = 0 := by
  simp [factorTP, Finsupp.single_apply]
  split_ifs <;> simp

lemma l1_factorTP_le (t : ℝ) : ((factorTP t).sum fun _ c => ‖c‖) ≤ 4 := by
  unfold factorTP
  have h1 : ∀ (a b : TrigPoly),
      ((a + b).sum fun _ c => ‖c‖) ≤ (a.sum fun _ c => ‖c‖) + (b.sum fun _ c => ‖c‖) := by
    intro a b
    unfold Finsupp.sum
    refine (Finset.sum_le_sum_of_subset_of_nonneg Finsupp.support_add
      (fun _ _ _ => norm_nonneg _)).trans ?_
    refine (Finset.sum_le_sum fun m _ => norm_add_le (a m) (b m)).trans ?_
    rw [Finset.sum_add_distrib]
    have ha : ∑ m ∈ a.support ∪ b.support, ‖a m‖ = ∑ m ∈ a.support, ‖a m‖ :=
      (Finset.sum_subset Finset.subset_union_left fun m _ hm => by
        simp [Finsupp.notMem_support_iff.mp hm]).symm
    have hb : ∑ m ∈ a.support ∪ b.support, ‖b m‖ = ∑ m ∈ b.support, ‖b m‖ :=
      (Finset.sum_subset Finset.subset_union_right fun m _ hm => by
        simp [Finsupp.notMem_support_iff.mp hm]).symm
    rw [ha, hb]
  refine (h1 _ _).trans ?_
  refine (add_le_add_left (h1 _ _) _).trans ?_
  have hs1 : ((Finsupp.single (1 : ℤ) (1 : ℂ)).sum fun _ c => ‖c‖) = 1 := by
    rw [Finsupp.sum_single_index (by simp), norm_one]
  have hs0 : ((Finsupp.single (0 : ℤ) (((-2 * Real.cos t : ℝ) : ℂ))).sum fun _ c => ‖c‖) =
      2 * |Real.cos t| := by
    rw [Finsupp.sum_single_index (by simp), Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hsm1 : ((Finsupp.single (-1 : ℤ) (1 : ℂ)).sum fun _ c => ‖c‖) = 1 := by
    rw [Finsupp.sum_single_index (by simp), norm_one]
  rw [hs1, hs0, hsm1]
  linarith [Real.abs_cos_le_one t]

/-- Product of d sign-change factors as a TrigPoly, built by induction on a Finset of angles. -/
lemma exists_sign_poly_tp {ι : Type*} (s : Finset ι) (t : ι → ℝ) :
    ∃ T : TrigPoly,
      (∀ x, evalTP T x = ((∏ i ∈ s, (2 * (Real.cos x - Real.cos (t i))) : ℝ) : ℂ)) ∧
      (∀ k ∈ T.support, -(s.card : ℤ) ≤ k ∧ k ≤ (s.card : ℤ)) ∧
      T (s.card : ℤ) = 1 ∧
      (∀ k : ℤ, (T k).im = 0) ∧
      (T.sum fun _ c => ‖c‖) ≤ (4 : ℝ) ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Finsupp.single 0 1, ?_, ?_, ?_, ?_, ?_⟩
    · intro x; simp [evalTP_single, eChar_zero]
    · intro k hk
      have := Finset.mem_singleton.mp (Finsupp.support_single_subset hk); omega
    · simp
    · intro k; simp [Finsupp.single_apply]; split_ifs <;> simp
    · simp [Finsupp.sum_single_index]
  | insert a s ha ih =>
    obtain ⟨T, hTev, hTsupp, hTtop, hTreal, hTl1⟩ := ih
    let T' : TrigPoly := mulTP T (factorTP (t a))
    have hcard : ((insert a s).card : ℤ) = (s.card : ℤ) + 1 := by
      rw [Finset.card_insert_of_notMem ha]; push_cast; rfl
    refine ⟨T', ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      rw [evalTP_mulTP, hTev, evalTP_factorTP, Finset.prod_insert ha]
      push_cast; ring
    · intro k hk
      obtain ⟨m, hm, n, hn, rfl⟩ := support_mulTP_subset _ _ k hk
      have h1 := hTsupp m hm
      have h2 := support_factorTP (t a) n hn
      omega
    · rw [hcard]
      unfold T' mulTP
      rw [Finsupp.sum, Finsupp.finsetSum_apply]
      have hterm : ∀ m ∈ T.support,
          ((factorTP (t a)).sum fun n b => Finsupp.single (m + n) (T m * b)) ((s.card : ℤ) + 1) =
            if m = (s.card : ℤ) then 1 else 0 := by
        intro m hm
        rw [Finsupp.sum, Finsupp.finsetSum_apply]
        have hmle := (hTsupp m hm).2
        split_ifs with hmeq
        · subst hmeq
          have h1mem : (1 : ℤ) ∈ (factorTP (t a)).support := by
            rw [Finsupp.mem_support_iff, factorTP_top]; exact one_ne_zero
          rw [Finset.sum_eq_single 1]
          · rw [Finsupp.single_eq_same, hTtop, factorTP_top, one_mul]
          · intro n _ hn1
            rw [Finsupp.single_apply, if_neg (by omega)]
          · intro hn; exact absurd h1mem hn
        · refine Finset.sum_eq_zero fun n hn => ?_
          have hnle := (support_factorTP (t a) n hn).2
          rw [Finsupp.single_apply, if_neg (by omega)]
      have htop_mem : (s.card : ℤ) ∈ T.support := by
        rw [Finsupp.mem_support_iff, hTtop]; exact one_ne_zero
      rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single (s.card : ℤ)]
      · simp
      · intro m _ hm; simp [hm]
      · intro hn; exact absurd htop_mem hn
    · intro k
      unfold T' mulTP
      rw [Finsupp.sum, Finsupp.finsetSum_apply, Complex.im_sum]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [Finsupp.sum, Finsupp.finsetSum_apply, Complex.im_sum]
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [Finsupp.single_apply]
      split_ifs
      · rw [Complex.mul_im, hTreal m, factorTP_real (t a) n]; ring
      · simp
    · rw [Finset.card_insert_of_notMem ha, pow_succ]
      exact (l1_mulTP_le T (factorTP (t a))).trans
        (mul_le_mul hTl1 (l1_factorTP_le (t a)) (Finsupp.sum_nonneg fun _ _ => norm_nonneg _)
          (by positivity))

/-- Finiteness of zeros in [0, 1) and extraction of sign-change angles in (0, pi). -/
lemma cosine_sum_sign_changes (S : Finset ℕ) (b : ℕ → ℕ) (n : ℕ)
    (hsum : ∑ k ∈ S, b k = n) (hn : 1 ≤ n) :
    let g : ℝ → ℝ := fun x => ∑ k ∈ S, (b k : ℝ) * Real.cos ((k : ℝ) * x)
    let Zfull : Set ℝ := {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) 1 ∧ g (2 * Real.pi * θ) = 0}
    Zfull.Finite ∧
    ∃ (d : ℕ) (t : Fin d → ℝ),
      StrictMono t ∧
      (∀ i, 0 < t i ∧ t i < Real.pi) ∧
      d ≤ Zfull.ncard ∧
      (∀ x : ℝ, 0 ≤ g x * ∏ i : Fin d, (2 * (Real.cos x - Real.cos (t i)))) ∧
      (∀ (i : Fin (d + 1)),
        let a : ℝ := if h : i.val = 0 then 0 else t ⟨i.val - 1, by omega⟩
        let c : ℝ := if h : i.val = d then Real.pi else t ⟨i.val, by omega⟩
        a < c ∧ ((∀ x ∈ Set.Icc a c, 0 ≤ g x) ∨ (∀ x ∈ Set.Icc a c, g x ≤ 0))) := by
  classical
  intro g Zfull
  -- Step 1: Zfull is finite via algebraic polynomial P(e^{ix})
  let M : ℕ := S.sup id
  let P : Polynomial ℂ :=
    ∑ k ∈ S, ((b k : ℝ) : ℂ) • (Polynomial.X ^ (M + k) + Polynomial.X ^ (M - k))
  have hP_eval : ∀ x : ℝ, P.eval (eChar 1 x) = eChar (M : ℤ) x * ((2 * g x : ℝ) : ℂ) := by
    intro x
    dsimp [P, g]
    rw [Polynomial.eval_finset_sum]
    simp_rw [Polynomial.eval_smul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      smul_eq_mul]
    rw [show ((2 * ∑ k ∈ S, (b k : ℝ) * Real.cos ((k : ℝ) * x) : ℝ) : ℂ) =
      ∑ k ∈ S, ((b k : ℝ) : ℂ) * ((2 * Real.cos ((k : ℝ) * x) : ℝ) : ℂ) by
      push_cast; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkM : k ≤ M := Finset.le_sup (f := id) hk
    have hpow : ∀ m : ℕ, (eChar 1 x) ^ m = eChar (m : ℤ) x := by
      intro m
      induction m with
      | zero => simp [eChar_zero]
      | succ m ih =>
        rw [pow_succ, ih, ← eChar_add, Nat.cast_succ]
    rw [hpow (M + k), hpow (M - k)]
    have hadd1 : eChar ((M + k : ℕ) : ℤ) x = eChar (M : ℤ) x * eChar (k : ℤ) x := by
      rw [Nat.cast_add, eChar_add]
    have hadd2 : eChar ((M - k : ℕ) : ℤ) x = eChar (M : ℤ) x * eChar (-(k : ℤ)) x := by
      rw [← eChar_add]; congr 1; omega
    have hcos : eChar (k : ℤ) x + eChar (-(k : ℤ)) x = ((2 * Real.cos ((k : ℝ) * x) : ℝ) : ℂ) := by
      unfold eChar
      push_cast
      rw [Complex.cos]
      have h1 : Complex.I * (k : ℂ) * (x : ℂ) = ((k : ℂ) * (x : ℂ)) * Complex.I := by ring
      have h2 : Complex.I * -(k : ℂ) * (x : ℂ) = -(((k : ℂ) * (x : ℂ)) * Complex.I) := by ring
      rw [h1, h2]
      ring
    rw [hadd1, hadd2]
    calc ((b k : ℝ) : ℂ) * (eChar (M : ℤ) x * eChar (k : ℤ) x + eChar (M : ℤ) x * eChar (-(k : ℤ)) x)
        = eChar (M : ℤ) x * (((b k : ℝ) : ℂ) * (eChar (k : ℤ) x + eChar (-(k : ℤ)) x)) := by ring
      _ = eChar (M : ℤ) x * (((b k : ℝ) : ℂ) * ((2 * Real.cos ((k : ℝ) * x) : ℝ) : ℂ)) := by rw [hcos]
  have hP_ne : P ≠ 0 := by
    intro h0
    have hev := hP_eval 0
    rw [h0, Polynomial.eval_zero] at hev
    have he0 : eChar (M : ℤ) 0 = 1 := by simp [eChar]
    rw [he0, one_mul] at hev
    have hg0 : g 0 = (n : ℝ) := by
      dsimp [g]; simp [← hsum]
    rw [hg0] at hev
    have hnpos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
    have hEq0 : (2 * (n : ℝ) : ℝ) = 0 := Complex.ofReal_injective hev.symm
    linarith
  have hZfull_fin : Zfull.Finite := by
    have hmap : Set.MapsTo (fun θ : ℝ => eChar 1 (2 * Real.pi * θ)) Zfull
        (P.roots.toFinset : Set ℂ) := by
      intro θ hθ
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP_ne, Polynomial.IsRoot.def,
        hP_eval, hθ.2]
      simp
    have hinj : Set.InjOn (fun θ : ℝ => eChar 1 (2 * Real.pi * θ)) Zfull := by
      intro θ₁ hθ₁ θ₂ hθ₂ heq
      dsimp only [eChar] at heq
      have h1 : Complex.I * (1 : ℤ) * ((2 * Real.pi * θ₁ : ℝ) : ℂ) =
          (θ₁ : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
      have h2 : Complex.I * (1 : ℤ) * ((2 * Real.pi * θ₂ : ℝ) : ℂ) =
          (θ₂ : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
      rw [h1, h2] at heq
      rw [Complex.exp_eq_exp_iff_exists_int] at heq
      obtain ⟨k, hk⟩ := heq
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
        exact_mod_cast Real.pi_ne_zero
      have hsub : ((θ₁ - θ₂ : ℝ) : ℂ) * (2 * Real.pi * Complex.I) =
          (k : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; linear_combination hk
      have hdiff : ((θ₁ - θ₂ : ℝ) : ℂ) = (k : ℂ) := mul_right_cancel₀ hpi hsub
      have hdiffR : θ₁ - θ₂ = (k : ℝ) := by
        have := congrArg Complex.re hdiff
        simpa using this
      have hlt1 : |θ₁ - θ₂| < 1 := by
        rw [abs_lt]
        constructor <;> linarith [hθ₁.1.1, hθ₁.1.2, hθ₂.1.1, hθ₂.1.2]
      rw [hdiffR] at hlt1
      have hk0 : k = 0 := by
        have hklt : |k| < 1 := by exact_mod_cast hlt1
        rw [abs_lt] at hklt
        omega
      rw [hk0, Int.cast_zero] at hdiffR
      linarith
    exact ((Finset.finite_toSet _).subset hmap.image_subset).of_finite_image hinj
  -- Step 2: Z₀ = {t ∈ (0, pi) | g t = 0} is finite and Z₀.ncard ≤ Zfull.ncard
  let Z₀ : Set ℝ := {t : ℝ | t ∈ Set.Ioo (0 : ℝ) Real.pi ∧ g t = 0}
  have hZ0_maps : Set.MapsTo (fun t : ℝ => t / (2 * Real.pi)) Z₀ Zfull := by
    intro t ht
    have hpi : 0 < Real.pi := Real.pi_pos
    have ht0 : 0 < t := ht.1.1
    refine ⟨⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one (by positivity)]; linarith [ht.1.2]
    · have : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
      rw [this]; exact ht.2
  have hZ0_inj : Set.InjOn (fun t : ℝ => t / (2 * Real.pi)) Z₀ := by
    intro a _ b _ h
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact (div_left_inj' hpi).mp h
  have hZ0_fin : Z₀.Finite := (hZfull_fin.subset hZ0_maps.image_subset).of_finite_image hZ0_inj
  have hZ0_ncard : Z₀.ncard ≤ Zfull.ncard := by
    have h1 := hZ0_inj.ncard_image
    have h2 : (fun t : ℝ => t / (2 * Real.pi)) '' Z₀ ⊆ Zfull := hZ0_maps.image_subset
    rw [← h1]
    exact Set.ncard_le_ncard h2 hZfull_fin
  -- Step 3: Sort Z₀ into 0 = e 0 < z 0 < ... < z (m-1) < e (m+1) = pi
  let zFin : Finset ℝ := hZ0_fin.toFinset
  let m : ℕ := zFin.card
  let z : Fin m ↪o ℝ := zFin.orderEmbOfFin rfl
  have hz_mem : ∀ i : Fin m, z i ∈ Z₀ := fun i =>
    hZ0_fin.mem_toFinset.mp (Finset.orderEmbOfFin_mem zFin rfl i)
  let e : Fin (m + 2) → ℝ := fun k =>
    if h0 : k.val = 0 then 0
    else if h1 : k.val = m + 1 then Real.pi
    else z ⟨k.val - 1, by omega⟩
  have he_strict : StrictMono e := by
    intro a b hab
    rw [Fin.lt_def] at hab
    dsimp only [e]
    split_ifs with ha0 ha1 hb0 hb1
    · omega
    · exact Real.pi_pos
    · exact (hz_mem _).1.1
    · omega
    · omega
    · omega
    · omega
    · exact (hz_mem _).1.2
    · exact z.strictMono (Fin.lt_def.mpr (by dsimp only; omega))
  have hg_cont : Continuous g :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  -- No zeros of g on (e j, e (j+1))
  have hno_zero : ∀ (j : Fin (m + 1)) (x : ℝ), e ⟨j.val, by omega⟩ < x → x < e ⟨j.val + 1, by omega⟩ →
      g x ≠ 0 := by
    intro j x hlo hhi hgx
    have hx_mem : x ∈ Z₀ := by
      refine ⟨⟨?_, ?_⟩, hgx⟩
      · have h0 : e ⟨0, by omega⟩ ≤ e ⟨j.val, by omega⟩ :=
          he_strict.monotone (Fin.le_def.mpr (Nat.zero_le _))
        simp only [e, dite_true] at h0
        linarith
      · have h1 : e ⟨j.val + 1, by omega⟩ ≤ e ⟨m + 1, by omega⟩ :=
          he_strict.monotone (Fin.le_def.mpr (by dsimp only; omega))
        simp only [e, show m + 1 ≠ 0 by omega, dite_false, dite_true] at h1
        linarith
    have hx_zFin : x ∈ zFin := hZ0_fin.mem_toFinset.mpr hx_mem
    obtain ⟨i, hi⟩ : ∃ i : Fin m, z i = x := by
      have hrng := Finset.range_orderEmbOfFin zFin rfl
      have : x ∈ Set.range z := by rw [hrng]; exact hx_zFin
      exact this
    have hei : e ⟨i.val + 1, by omega⟩ = x := by
      simp only [e, show i.val + 1 ≠ 0 by omega, show i.val + 1 ≠ m + 1 by omega, dite_false]
      have hfin : (⟨i.val + 1 - 1, by omega⟩ : Fin m) = i := Fin.ext (by dsimp only; omega)
      rw [hfin]; exact hi
    by_cases hij : i.val + 1 ≤ j.val
    · have := he_strict.monotone (Fin.le_def.mpr hij : (⟨i.val + 1, by omega⟩ : Fin (m + 2)) ≤ ⟨j.val, by omega⟩)
      linarith
    · have hji : j.val + 1 ≤ i.val + 1 := by omega
      have := he_strict.monotone (Fin.le_def.mpr hji : (⟨j.val + 1, by omega⟩ : Fin (m + 2)) ≤ ⟨i.val + 1, by omega⟩)
      linarith
  -- Constant sign σ j : Bool on (e j, e (j+1))
  let σ : Fin (m + 1) → Bool := fun j =>
    decide (0 < g ((e ⟨j.val, by omega⟩ + e ⟨j.val + 1, by omega⟩) / 2))
  have hsign : ∀ (j : Fin (m + 1)) (x : ℝ),
      e ⟨j.val, by omega⟩ < x → x < e ⟨j.val + 1, by omega⟩ →
      (if σ j then 0 < g x else g x < 0) := by
    intro j x hlo hhi
    have hlt_e : e ⟨j.val, by omega⟩ < e ⟨j.val + 1, by omega⟩ :=
      he_strict (Fin.lt_def.mpr (by dsimp only; omega))
    let mid : ℝ := (e ⟨j.val, by omega⟩ + e ⟨j.val + 1, by omega⟩) / 2
    have hmid_lo : e ⟨j.val, by omega⟩ < mid := by dsimp [mid]; linarith
    have hmid_hi : mid < e ⟨j.val + 1, by omega⟩ := by dsimp [mid]; linarith
    have hmid_ne : g mid ≠ 0 := hno_zero j mid hmid_lo hmid_hi
    have hx_ne : g x ≠ 0 := hno_zero j x hlo hhi
    have hsame : (0 < g mid) ↔ (0 < g x) := by
      constructor
      · intro hmp
        by_contra hxn
        have hxn' : g x < 0 := lt_of_le_of_ne (not_lt.mp hxn) hx_ne
        rcases le_total mid x with hmx | hxm
        · have h0mem : (0 : ℝ) ∈ Set.Icc (g x) (g mid) := ⟨hxn'.le, hmp.le⟩
          obtain ⟨c, hc, hgc⟩ := intermediate_value_Icc' hmx hg_cont.continuousOn h0mem
          exact hno_zero j c (lt_of_lt_of_le hmid_lo hc.1) (lt_of_le_of_lt hc.2 hhi) hgc
        · have h0mem : (0 : ℝ) ∈ Set.Icc (g x) (g mid) := ⟨hxn'.le, hmp.le⟩
          obtain ⟨c, hc, hgc⟩ := intermediate_value_Icc hxm hg_cont.continuousOn h0mem
          exact hno_zero j c (lt_of_lt_of_le hlo hc.1) (lt_of_le_of_lt hc.2 hmid_hi) hgc
      · intro hxp
        by_contra hmn
        have hmn' : g mid < 0 := lt_of_le_of_ne (not_lt.mp hmn) hmid_ne
        rcases le_total mid x with hmx | hxm
        · have h0mem : (0 : ℝ) ∈ Set.Icc (g mid) (g x) := ⟨hmn'.le, hxp.le⟩
          obtain ⟨c, hc, hgc⟩ := intermediate_value_Icc hmx hg_cont.continuousOn h0mem
          exact hno_zero j c (lt_of_lt_of_le hmid_lo hc.1) (lt_of_le_of_lt hc.2 hhi) hgc
        · have h0mem : (0 : ℝ) ∈ Set.Icc (g mid) (g x) := ⟨hmn'.le, hxp.le⟩
          obtain ⟨c, hc, hgc⟩ := intermediate_value_Icc' hxm hg_cont.continuousOn h0mem
          exact hno_zero j c (lt_of_lt_of_le hlo hc.1) (lt_of_le_of_lt hc.2 hmid_hi) hgc
    by_cases h : 0 < g mid
    · have hσ : σ j = true := decide_eq_true h
      rw [if_pos hσ]; exact hsame.mp h
    · have hσ : σ j = false := decide_eq_false h
      rw [if_neg (by rw [hσ]; exact Bool.false_ne_true)]
      exact lt_of_le_of_ne (not_lt.mp (fun hx => h (hsame.mpr hx))) hx_ne
  -- σ 0 = true because g 0 = n > 0
  have hσ0 : σ ⟨0, by omega⟩ = true := by
    have hg0 : 0 < g 0 := by
      have : g 0 = (n : ℝ) := by dsimp [g]; simp [← hsum]
      rw [this]; positivity
    have hlt0 : (0 : ℝ) < e ⟨1, by omega⟩ := by
      have := he_strict (Fin.lt_def.mpr (by dsimp only; omega) :
        (⟨0, by omega⟩ : Fin (m + 2)) < ⟨1, by omega⟩)
      simpa [e] using this
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hg_cont.continuousAt (g 0) hg0
    let x₀ := min (e ⟨1, by omega⟩ / 2) (δ / 2)
    have hx0_pos : 0 < x₀ := lt_min (by linarith) (by linarith)
    have hx0_lt : x₀ < e ⟨1, by omega⟩ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hx0_dist : dist x₀ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx0_pos]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hgx0 : 0 < g x₀ := by
      have := hδ hx0_dist
      rw [Real.dist_eq, abs_lt] at this
      linarith
    have hs := hsign ⟨0, by omega⟩ x₀ (by simpa [e] using hx0_pos) hx0_lt
    cases h : σ ⟨0, by omega⟩
    · rw [h] at hs; simp at hs; linarith
    · rfl
  -- Select sign-change indices scIdx ⊆ Fin m
  let scIdx : Finset (Fin m) :=
    Finset.univ.filter fun i => σ ⟨i.val, by omega⟩ ≠ σ ⟨i.val + 1, by omega⟩
  let d : ℕ := scIdx.card
  let scEmb : Fin d ↪o Fin m := scIdx.orderEmbOfFin rfl
  let t : Fin d → ℝ := fun i => z (scEmb i)
  have ht_strict : StrictMono t := fun a b hab => z.strictMono (scEmb.strictMono hab)
  have ht_mem : ∀ i : Fin d, 0 < t i ∧ t i < Real.pi := fun i => (hz_mem (scEmb i)).1
  have hd_le : d ≤ Zfull.ncard := by
    calc d = scIdx.card := rfl
      _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ _
      _ = m := by simp
      _ = Z₀.ncard := by
          rw [show m = zFin.card from rfl, ← Set.ncard_coe_finset zFin]
          congr 1; exact hZ0_fin.coe_toFinset
      _ ≤ Zfull.ncard := hZ0_ncard
  -- Parity lemma: count of sign changes before j matches whether σ j = true
  have hparity : ∀ (j : Fin (m + 1)),
      Even (scIdx.filter (fun i : Fin m => i.val < j.val)).card ↔ σ j = true := by
    intro j
    obtain ⟨jv, hjv⟩ := j
    induction jv with
    | zero =>
      have hemp : scIdx.filter (fun i : Fin m => i.val < 0) = ∅ := by
        ext i; simp
      rw [hemp, Finset.card_empty, hσ0]
      simp
    | succ k ih =>
      have hk : k < m := by omega
      have hsplit : scIdx.filter (fun i : Fin m => i.val < k + 1) =
          (scIdx.filter (fun i : Fin m => i.val < k)) ∪
          (scIdx.filter (fun i : Fin m => i.val = k)) := by
        ext i; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro ⟨hi, hlt⟩
          by_cases h : i.val = k
          · exact Or.inr ⟨hi, h⟩
          · exact Or.inl ⟨hi, by omega⟩
        · rintro (⟨hi, hlt⟩ | ⟨hi, heq⟩)
          · exact ⟨hi, by omega⟩
          · exact ⟨hi, by omega⟩
      have hdisj : Disjoint (scIdx.filter (fun i : Fin m => i.val < k))
          (scIdx.filter (fun i : Fin m => i.val = k)) := by
        rw [Finset.disjoint_left]; intro i h1 h2
        simp only [Finset.mem_filter] at h1 h2; omega
      rw [hsplit, Finset.card_union_of_disjoint hdisj]
      have hih := ih (by omega)
      by_cases hch : σ ⟨k, by omega⟩ ≠ σ ⟨k + 1, hjv⟩
      · have hsing : scIdx.filter (fun i : Fin m => i.val = k) = {⟨k, hk⟩} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_singleton, scIdx, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨_, heq⟩; exact Fin.ext heq
          · rintro rfl; exact ⟨hch, rfl⟩
        rw [hsing, Finset.card_singleton, Nat.even_add_one, hih]
        cases h1 : σ ⟨k, by omega⟩ <;> cases h2 : σ ⟨k + 1, hjv⟩ <;> simp_all
      · push Not at hch
        have hemp : scIdx.filter (fun i : Fin m => i.val = k) = ∅ := by
          ext i
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, scIdx,
            Finset.mem_univ, true_and]
          intro hne heq
          have : i = ⟨k, hk⟩ := Fin.ext heq
          subst this
          exact hne hch
        rw [hemp, Finset.card_empty, add_zero, hih, hch]
  -- Nonnegativity of g x * T x on [0, pi]
  have hprod_nonneg_Icc : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
      0 ≤ g x * ∏ i : Fin d, (2 * (Real.cos x - Real.cos (t i))) := by
    -- First show it on every open subinterval (e j, e (j+1))
    have hopen : ∀ (j : Fin (m + 1)) (x : ℝ),
        e ⟨j.val, by omega⟩ < x → x < e ⟨j.val + 1, by omega⟩ →
        0 < g x * ∏ i : Fin d, (2 * (Real.cos x - Real.cos (t i))) := by
      intro j x hlo hhi
      have hx0 : 0 < x := by
        have h0 := he_strict.monotone (Fin.le_def.mpr (Nat.zero_le j.val) :
          (⟨0, by omega⟩ : Fin (m + 2)) ≤ ⟨j.val, by omega⟩)
        simp only [e, dite_true] at h0; linarith
      have hxpi : x < Real.pi := by
        have h1 := he_strict.monotone (Fin.le_def.mpr (by omega : j.val + 1 ≤ m + 1) :
          (⟨j.val + 1, by omega⟩ : Fin (m + 2)) ≤ ⟨m + 1, by omega⟩)
        simp only [e, show m + 1 ≠ 0 by omega, dite_false, dite_true] at h1; linarith
      -- Rewrite product over Fin d as product over scIdx
      have hprod_eq : (∏ i : Fin d, (2 * (Real.cos x - Real.cos (t i)))) =
          ∏ r ∈ scIdx, (2 * (Real.cos x - Real.cos (z r))) := by
        refine Finset.prod_bij (fun (i : Fin d) _ => scEmb i) ?_ ?_ ?_ ?_
        · intro i _; exact Finset.orderEmbOfFin_mem scIdx rfl i
        · intro a _ b _ h; exact scEmb.injective h
        · intro r hr
          have hrng := Finset.range_orderEmbOfFin scIdx rfl
          have : r ∈ Set.range scEmb := by rw [hrng]; exact hr
          obtain ⟨i, rfl⟩ := this
          exact ⟨i, Finset.mem_univ _, rfl⟩
        · intro i _; rfl
      rw [hprod_eq]
      let scL := scIdx.filter (fun r : Fin m => r.val < j.val)
      let scR := scIdx.filter (fun r : Fin m => ¬ r.val < j.val)
      have hpart : scIdx = scL ∪ scR := (Finset.filter_union_filter_not_eq _ _).symm
      have hdisj : Disjoint scL scR := Finset.disjoint_filter_filter_not _ _ _
      rw [hpart, Finset.prod_union hdisj]
      have hR_pos : 0 < ∏ r ∈ scR, (2 * (Real.cos x - Real.cos (z r))) := by
        refine Finset.prod_pos fun r hr => ?_
        have hrge : j.val ≤ r.val := by
          have := (Finset.mem_filter.mp hr).2; omega
        have hxr : x < z r := by
          have h1 : e ⟨j.val + 1, by omega⟩ ≤ e ⟨r.val + 1, by omega⟩ :=
            he_strict.monotone (Fin.le_def.mpr (by dsimp only; omega))
          have h2 : e ⟨r.val + 1, by omega⟩ = z r := by
            simp only [e, show r.val + 1 ≠ 0 by omega, show r.val + 1 ≠ m + 1 by omega, dite_false]
            exact congrArg z (Fin.ext (by dsimp only; omega))
          linarith
        have hcos := Real.strictAntiOn_cos ⟨hx0.le, hxpi.le⟩
          ⟨(hz_mem r).1.1.le, (hz_mem r).1.2.le⟩ hxr
        linarith
      have hL_sgn : (∏ r ∈ scL, (2 * (Real.cos x - Real.cos (z r)))) =
          (-1 : ℝ) ^ scL.card * ∏ r ∈ scL, (2 * (Real.cos (z r) - Real.cos x)) := by
        rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun r _ => by ring
      have hL_pos : 0 < ∏ r ∈ scL, (2 * (Real.cos (z r) - Real.cos x)) := by
        refine Finset.prod_pos fun r hr => ?_
        have hrlt : r.val + 1 ≤ j.val := by
          have := (Finset.mem_filter.mp hr).2; omega
        have hrx : z r < x := by
          have h1 : e ⟨r.val + 1, by omega⟩ ≤ e ⟨j.val, by omega⟩ :=
            he_strict.monotone (Fin.le_def.mpr hrlt)
          have h2 : e ⟨r.val + 1, by omega⟩ = z r := by
            simp only [e, show r.val + 1 ≠ 0 by omega, show r.val + 1 ≠ m + 1 by omega, dite_false]
            exact congrArg z (Fin.ext (by dsimp only; omega))
          linarith
        have hcos := Real.strictAntiOn_cos ⟨(hz_mem r).1.1.le, (hz_mem r).1.2.le⟩
          ⟨hx0.le, hxpi.le⟩ hrx
        linarith
      rw [hL_sgn]
      have hgs := hsign j x hlo hhi
      have hpar := hparity j
      cases hσ : σ j
      · rw [hσ] at hgs hpar
        simp only [Bool.false_eq_true, iff_false] at hpar
        have hodd : Odd scL.card := Nat.not_even_iff_odd.mp hpar
        rw [hodd.neg_one_pow]
        simp only [Bool.false_eq_true, ite_false] at hgs
        have hmul : 0 < (-g x) * ((∏ r ∈ scL, (2 * (Real.cos (z r) - Real.cos x))) *
            (∏ r ∈ scR, (2 * (Real.cos x - Real.cos (z r))))) :=
          mul_pos (by linarith) (mul_pos hL_pos hR_pos)
        linarith
      · rw [hσ] at hgs hpar
        simp only [iff_true] at hpar
        rw [hpar.neg_one_pow]
        simp only [ite_true] at hgs
        have hmul : 0 < g x * ((∏ r ∈ scL, (2 * (Real.cos (z r) - Real.cos x))) *
            (∏ r ∈ scR, (2 * (Real.cos x - Real.cos (z r))))) :=
          mul_pos hgs (mul_pos hL_pos hR_pos)
        linarith
    intro x hx
    -- Check if x = 0, x = pi, x ∈ Z₀, or x ∈ (e j, e (j+1))
    by_cases hx0 : x = 0
    · subst hx0
      have hg0 : 0 ≤ g 0 := by
        have : g 0 = (n : ℝ) := by dsimp [g]; simp [← hsum]
        rw [this]; positivity
      refine mul_nonneg hg0 (Finset.prod_nonneg fun i _ => ?_)
      rw [Real.cos_zero]
      linarith [Real.cos_le_one (t i)]
    · by_cases hxpi : x = Real.pi
      · subst hxpi
        -- By continuity from the left on (e m, pi)
        let F : ℝ → ℝ := fun y => g y * ∏ i : Fin d, (2 * (Real.cos y - Real.cos (t i)))
        have hFcont : Continuous F :=
          hg_cont.mul (continuous_finset_prod _ fun i _ =>
            continuous_const.mul (Real.continuous_cos.sub continuous_const))
        have hlt : e ⟨m, by omega⟩ < Real.pi := by
          have := he_strict (Fin.lt_def.mpr (by dsimp only; omega) :
            (⟨m, by omega⟩ : Fin (m + 2)) < ⟨m + 1, by omega⟩)
          simpa [e, show m + 1 ≠ 0 by omega] using this
        have hev : ∀ᶠ y in 𝓝[<] Real.pi, 0 ≤ F y := by
          filter_upwards [Ioo_mem_nhdsLT hlt] with y hy
          exact (hopen ⟨m, by omega⟩ y hy.1 (by simpa [e, show m + 1 ≠ 0 by omega] using hy.2)).le
        exact ge_of_tendsto (hFcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev
      · by_cases hgx : g x = 0
        · simp [hgx]
        · -- x ∈ (0, pi) and g x ≠ 0, so x is in some (e j, e (j+1))
          have hmem_Ioo : x ∈ Set.Ioo (0 : ℝ) Real.pi :=
            ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hxpi⟩
          -- Find largest j ≤ m with e j < x
          have hexj : ∃ j : Fin (m + 1), e ⟨j.val, by omega⟩ < x ∧ x < e ⟨j.val + 1, by omega⟩ := by
            have hS : (Finset.univ.filter (fun k : Fin (m + 2) => e k < x)).Nonempty :=
              ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [e] using hmem_Ioo.1⟩⟩
            let j0 := (Finset.univ.filter (fun k : Fin (m + 2) => e k < x)).max' hS
            have hj0_lt : e j0 < x := (Finset.mem_filter.mp (Finset.max'_mem _ hS)).2
            have hj0_ne : j0.val ≠ m + 1 := by
              intro h
              have : e j0 = Real.pi := by
                dsimp only [e]; rw [dif_neg (by omega), dif_pos h]
              linarith [hmem_Ioo.2]
            have hj0_le : j0.val < m + 1 := by omega
            refine ⟨⟨j0.val, hj0_le⟩, hj0_lt, ?_⟩
            have hnot : ¬ e ⟨j0.val + 1, by omega⟩ < x := by
              intro hlt'
              have hle' := Finset.le_max' (Finset.univ.filter (fun k : Fin (m + 2) => e k < x))
                ⟨j0.val + 1, by omega⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt'⟩)
              have hle'' : j0.val + 1 ≤ j0.val := Fin.le_def.mp hle'
              omega
            have hne' : e ⟨j0.val + 1, by omega⟩ ≠ x := by
              intro heq
              by_cases htop : j0.val + 1 = m + 1
              · have : e ⟨j0.val + 1, by omega⟩ = Real.pi := by
                  dsimp only [e]; rw [dif_neg (by omega), dif_pos htop]
                linarith [hmem_Ioo.2]
              · have : e ⟨j0.val + 1, by omega⟩ = z ⟨j0.val, by omega⟩ := by
                  dsimp only [e]; rw [dif_neg (by omega), dif_neg htop]
                  exact congrArg z (Fin.ext (by dsimp only; omega))
                rw [this] at heq
                exact hgx (heq ▸ (hz_mem ⟨j0.val, by omega⟩).2)
            exact lt_of_le_of_ne (not_lt.mp hnot) hne'.symm
          obtain ⟨j, hlo, hhi⟩ := hexj
          exact (hopen j x hlo hhi).le
  -- Extend nonnegativity from [0, pi] to all x : ℝ by evenness and 2*pi periodicity
  have hprod_nonneg : ∀ x : ℝ, 0 ≤ g x * ∏ i : Fin d, (2 * (Real.cos x - Real.cos (t i))) := by
    intro x
    let F : ℝ → ℝ := fun y => g y * ∏ i : Fin d, (2 * (Real.cos y - Real.cos (t i)))
    have hFeven : ∀ y, F (-y) = F y := by
      intro y
      dsimp [F, g]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => by rw [mul_neg, Real.cos_neg]
      · refine Finset.prod_congr rfl fun i _ => by rw [Real.cos_neg]
    have hFper : ∀ y (k : ℤ), F (y + k * (2 * Real.pi)) = F y := by
      intro y k
      dsimp [F, g]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        have harg : (j : ℝ) * (y + (k : ℝ) * (2 * Real.pi)) =
            (j : ℝ) * y + ((j * k : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
        rw [harg, Real.cos_add_int_mul_two_pi]
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [Real.cos_add_int_mul_two_pi]
    let k : ℤ := ⌊x / (2 * Real.pi)⌋
    let y : ℝ := x - (k : ℝ) * (2 * Real.pi)
    have hy0 : 0 ≤ y := by
      have h1 : (k : ℝ) ≤ x / (2 * Real.pi) := Int.floor_le _
      have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp h1
      dsimp [y]; linarith
    have hy2 : y < 2 * Real.pi := by
      have h1 : x / (2 * Real.pi) < (k : ℝ) + 1 := Int.lt_floor_add_one _
      have h2 := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp h1
      dsimp [y]; linarith
    have hFx : F x = F y := by
      have hx : x = y + (k : ℝ) * (2 * Real.pi) := by dsimp [y]; ring
      rw [hx, hFper]
    change 0 ≤ F x
    rw [hFx]
    by_cases hypi : y ≤ Real.pi
    · exact hprod_nonneg_Icc y ⟨hy0, hypi⟩
    · have hy' : 2 * Real.pi - y ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by linarith, by linarith⟩
      have hFy : F y = F (2 * Real.pi - y) := by
        rw [← hFeven (2 * Real.pi - y)]
        have : -(2 * Real.pi - y) = y + ((-1 : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
        rw [this, hFper]
      rw [hFy]
      exact hprod_nonneg_Icc _ hy'
  -- Constant sign of g on each [a_i, c_i] between consecutive sign changes
  refine ⟨hZfull_fin, d, t, ht_strict, ht_mem, hd_le, hprod_nonneg, ?_⟩
  intro i
  let a : ℝ := if h : i.val = 0 then 0 else t ⟨i.val - 1, by omega⟩
  let c : ℝ := if h : i.val = d then Real.pi else t ⟨i.val, by omega⟩
  have hac : a < c := by
    dsimp only [a, c]
    split_ifs with h1 h2
    · exact Real.pi_pos
    · exact (ht_mem _).1
    · exact (ht_mem _).2
    · exact ht_strict (Fin.lt_def.mpr (by dsimp only; omega))
  refine ⟨hac, ?_⟩
  -- For x ∈ (a, c), the sign-change product T(x) has strictly constant sign (-1)^i.val!
  have hT_sgn : ∀ x ∈ Set.Ioo a c,
      if Even i.val then 0 < ∏ r : Fin d, (2 * (Real.cos x - Real.cos (t r)))
      else ∏ r : Fin d, (2 * (Real.cos x - Real.cos (t r))) < 0 := by
    intro x hx
    have hx0 : 0 < x := by
      have ha0 : 0 ≤ a := by
        dsimp only [a]; split_ifs
        · exact le_rfl
        · exact (ht_mem _).1.le
      linarith [hx.1]
    have hxpi : x < Real.pi := by
      have hcpi : c ≤ Real.pi := by
        dsimp only [c]; split_ifs
        · exact le_rfl
        · exact (ht_mem _).2.le
      linarith [hx.2]
    let Lset := Finset.univ.filter (fun r : Fin d => r.val < i.val)
    let Rset := Finset.univ.filter (fun r : Fin d => ¬ r.val < i.val)
    have hLcard : Lset.card = i.val := by
      have hbij : Lset.card = (Finset.range i.val).card := by
        refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
        · intro r hr; exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2
        · intro r1 _ r2 _ h; exact Fin.ext h
        · intro k hk
          have hk' : k < i.val := Finset.mem_range.mp hk
          exact ⟨⟨k, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩, rfl⟩
      rw [hbij, Finset.card_range]
    have hpart : (Finset.univ : Finset (Fin d)) = Lset ∪ Rset :=
      (Finset.filter_union_filter_not_eq _ _).symm
    have hdisj : Disjoint Lset Rset := Finset.disjoint_filter_filter_not _ _ _
    rw [hpart, Finset.prod_union hdisj]
    have hRpos : 0 < ∏ r ∈ Rset, (2 * (Real.cos x - Real.cos (t r))) := by
      refine Finset.prod_pos fun r hr => ?_
      have hri : i.val ≤ r.val := by have := (Finset.mem_filter.mp hr).2; omega
      have hxr : x < t r := by
        have hid : i.val ≠ d := by omega
        have hc : c = t ⟨i.val, by omega⟩ := by simp [c, hid]
        have hle : t ⟨i.val, by omega⟩ ≤ t r := ht_strict.monotone (Fin.le_def.mpr hri)
        linarith [hx.2]
      have hcos := Real.strictAntiOn_cos ⟨hx0.le, hxpi.le⟩
        ⟨(ht_mem r).1.le, (ht_mem r).2.le⟩ hxr
      linarith
    have hLsgn : (∏ r ∈ Lset, (2 * (Real.cos x - Real.cos (t r)))) =
        (-1 : ℝ) ^ i.val * ∏ r ∈ Lset, (2 * (Real.cos (t r) - Real.cos x)) := by
      rw [← hLcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun r _ => by ring
    have hLpos : 0 < ∏ r ∈ Lset, (2 * (Real.cos (t r) - Real.cos x)) := by
      refine Finset.prod_pos fun r hr => ?_
      have hri : r.val < i.val := (Finset.mem_filter.mp hr).2
      have hrx : t r < x := by
        have hi0 : i.val ≠ 0 := by omega
        have ha : a = t ⟨i.val - 1, by omega⟩ := by simp [a, hi0]
        have hle : t r ≤ t ⟨i.val - 1, by omega⟩ := ht_strict.monotone (Fin.le_def.mpr (by dsimp only; omega))
        linarith [hx.1]
      have hcos := Real.strictAntiOn_cos ⟨(ht_mem r).1.le, (ht_mem r).2.le⟩
        ⟨hx0.le, hxpi.le⟩ hrx
      linarith
    rw [hLsgn]
    split_ifs with hev
    · rw [hev.neg_one_pow, one_mul]; exact mul_pos hLpos hRpos
    · rw [(Nat.not_even_iff_odd.mp hev).neg_one_pow]; nlinarith [mul_pos hLpos hRpos]
  by_cases hev : Even i.val
  · left
    have hopen_nn : ∀ x ∈ Set.Ioo a c, 0 ≤ g x := by
      intro x hx
      have hT := hT_sgn x hx
      rw [if_pos hev] at hT
      have hprod := hprod_nonneg x
      nlinarith
    intro x hx
    by_cases hxa : x = a
    · subst hxa
      have hev_nhds : ∀ᶠ y in 𝓝[>] a, 0 ≤ g y := by
        filter_upwards [Ioo_mem_nhdsGT hac] with y hy
        exact hopen_nn y hy
      exact ge_of_tendsto (hg_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev_nhds
    · by_cases hxc : x = c
      · subst hxc
        have hev_nhds : ∀ᶠ y in 𝓝[<] c, 0 ≤ g y := by
          filter_upwards [Ioo_mem_nhdsLT hac] with y hy
          exact hopen_nn y hy
        exact ge_of_tendsto (hg_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev_nhds
      · exact hopen_nn x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxc⟩
  · right
    have hopen_np : ∀ x ∈ Set.Ioo a c, g x ≤ 0 := by
      intro x hx
      have hT := hT_sgn x hx
      rw [if_neg hev] at hT
      have hprod := hprod_nonneg x
      nlinarith
    intro x hx
    by_cases hxa : x = a
    · subst hxa
      have hev_nhds : ∀ᶠ y in 𝓝[>] a, g y ≤ 0 := by
        filter_upwards [Ioo_mem_nhdsGT hac] with y hy
        exact hopen_np y hy
      exact le_of_tendsto (hg_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev_nhds
    · by_cases hxc : x = c
      · subst hxc
        have hev_nhds : ∀ᶠ y in 𝓝[<] c, g y ≤ 0 := by
          filter_upwards [Ioo_mem_nhdsLT hac] with y hy
          exact hopen_np y hy
        exact le_of_tendsto (hg_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev_nhds
      · exact hopen_np x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxc⟩

/- ### Section 3: Cramer Rank Bound, Finite-State Periodicity, Cyclotomic Order Bound -/

/-- Hadamard-style naive determinant bound: if every entry of an m x m integer matrix
has abs ≤ 8, then |det M| ≤ m! * 8^m. -/
lemma abs_det_le_factorial_mul_pow {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ)
    (hM : ∀ i j, |M i j| ≤ 8) :
    (|M.det| : ℝ) ≤ (m.factorial : ℝ) * (8 : ℝ) ^ m := by
  rw [Matrix.det_apply]
  simp only [Units.smul_def, zsmul_eq_mul]
  have h1 : (|(∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin m, M (σ i) i : ℤ)| : ℝ) ≤
      ∑ σ : Equiv.Perm (Fin m), (|(Equiv.Perm.sign σ : ℤ) * ∏ i : Fin m, M (σ i) i| : ℝ) := by
    have hint : |∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin m, M (σ i) i| ≤
        ∑ σ : Equiv.Perm (Fin m), |(Equiv.Perm.sign σ : ℤ) * ∏ i : Fin m, M (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    exact_mod_cast hint
  refine h1.trans ?_
  have hterm : ∀ σ : Equiv.Perm (Fin m),
      (|(Equiv.Perm.sign σ : ℤ) * ∏ i : Fin m, M (σ i) i| : ℝ) ≤ (8 : ℝ) ^ m := by
    intro σ
    have hsgn : |(Equiv.Perm.sign σ : ℤ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    have hprod : |∏ i : Fin m, M (σ i) i| ≤ (8 : ℤ) ^ m := by
      rw [Finset.abs_prod]
      calc ∏ i : Fin m, |M (σ i) i|
          ≤ ∏ _i : Fin m, (8 : ℤ) := Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hM _ _)
        _ = (8 : ℤ) ^ m := by simp
    have hmul : |(Equiv.Perm.sign σ : ℤ) * ∏ i : Fin m, M (σ i) i| ≤ (8 : ℤ) ^ m := by
      rw [abs_mul, hsgn, one_mul]; exact hprod
    exact_mod_cast hmul
  refine (Finset.sum_le_sum fun σ _ => hterm σ).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- If an integer matrix W of size r x r with entries in [-8, 8] satisfies |W * u|_k < δ
for a real vector u with u 0 = 1 and δ = 1/(2 * r! * 8^r), then det W = 0. -/
lemma det_eq_zero_of_small_mulVec {r : ℕ} (hr : 1 ≤ r)
    (W : Matrix (Fin r) (Fin r) ℤ) (hW : ∀ i j, |W i j| ≤ 8)
    (u : Fin r → ℝ) (hu0 : u ⟨0, by omega⟩ = 1)
    (hsmall : ∀ k : Fin r, |∑ s : Fin r, (W k s : ℝ) * u s| < (2 * (r.factorial : ℝ) * (8 : ℝ) ^ r)⁻¹) :
    W.det = 0 := by
  by_contra hne
  have hdet_ge : (1 : ℝ) ≤ (|W.det| : ℝ) := by
    have : 1 ≤ |W.det| := Int.one_le_abs hne
    exact_mod_cast this
  let WR : Matrix (Fin r) (Fin r) ℝ := W.map (Int.cast : ℤ → ℝ)
  have hadj := Matrix.adjugate_mul WR
  have hvec : (WR.adjugate.mulVec (WR.mulVec u)) ⟨0, by omega⟩ = WR.det * u ⟨0, by omega⟩ := by
    rw [Matrix.mulVec_mulVec, hadj, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [hu0, mul_one] at hvec
  have hdet_eq : WR.det = (W.det : ℝ) := by
    simpa [WR] using (RingHom.map_det (Int.castRingHom ℝ) W).symm
  have hadj_eq : ∀ k : Fin r, WR.adjugate ⟨0, by omega⟩ k = (W.adjugate ⟨0, by omega⟩ k : ℝ) := by
    intro k
    simpa [WR] using congrFun (congrFun (RingHom.map_adjugate (Int.castRingHom ℝ) W).symm ⟨0, by omega⟩) k
  have hadj_bound : ∀ k : Fin r, (|W.adjugate ⟨0, by omega⟩ k| : ℝ) ≤
      ((r - 1).factorial : ℝ) * (8 : ℝ) ^ (r - 1) := by
    intro k
    rw [Matrix.adjugate_apply, Matrix.det_apply]
    -- Bound each entry of W.adjugate directly via submatrix of size r - 1
    -- Actually Matrix.adjugate_apply gives (W.updateRow k (Pi.single 0 1)).det!
    -- Even simpler: use Matrix.adjugate_apply -> det of updateRow k (Pi.single 0 1), where
    -- row k has 1 at col 0 and 0 elsewhere, so only perms with σ k = 0 survive: (r-1)! of them!
    have hperm_count :
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin r) => σ ⟨0, by omega⟩ = k)).card = (r - 1).factorial := by
      have hcard_all : Fintype.card (Equiv.Perm (Fin r)) = r.factorial := by
        rw [Fintype.card_perm, Fintype.card_fin]
      -- Use equivalence between {σ | σ 0 = k} and Perm {j : Fin r // j ≠ 0}
      -- Or sum over all k : Fin r of the card = r! and all fibers have the same card!
      have hfib : ∀ k₁ k₂ : Fin r,
          (Finset.univ.filter (fun σ : Equiv.Perm (Fin r) => σ ⟨0, by omega⟩ = k₁)).card =
          (Finset.univ.filter (fun σ : Equiv.Perm (Fin r) => σ ⟨0, by omega⟩ = k₂)).card := by
        intro k₁ k₂
        refine Finset.card_bij (fun σ _ => Equiv.swap k₁ k₂ * σ) ?_ ?_ ?_
        · intro σ hσ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
          simp [Equiv.Perm.mul_apply, hσ]
        · intro a _ b _ hab
          exact mul_left_cancel hab
        · intro τ hτ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
          refine ⟨Equiv.swap k₁ k₂ * τ, ?_, by simp [← mul_assoc]⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply, hτ,
            Equiv.swap_apply_right]
      have hsum_fib : ∑ j : Fin r,
          (Finset.univ.filter (fun σ : Equiv.Perm (Fin r) => σ ⟨0, by omega⟩ = j)).card =
          r.factorial := by
        rw [← hcard_all, ← Finset.card_univ]
        exact (Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)).symm
      have hconst : ∑ j : Fin r,
          (Finset.univ.filter (fun σ : Equiv.Perm (Fin r) => σ ⟨0, by omega⟩ = j)).card =
          r * (Finset.univ.filter (fun σ : Equiv.Perm (Fin r) => σ ⟨0, by omega⟩ = k)).card := by
        rw [Finset.sum_congr rfl (fun j _ => hfib j k), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
      rw [hconst] at hsum_fib
      have hfac : r.factorial = r * (r - 1).factorial := by
        cases r with
        | zero => omega
        | succ r' => simp [Nat.factorial_succ]
      rw [hfac] at hsum_fib
      exact Nat.eq_of_mul_eq_mul_left (by omega) hsum_fib
    -- Now bound the sum over σ in Matrix.det_apply for updateRow k (Pi.single 0 1)
    let Mk : Matrix (Fin r) (Fin r) ℤ := W.updateRow k (Pi.single ⟨0, by omega⟩ 1)
    have hsum_le : (|∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℤ) *
          ∏ i : Fin r, Mk (σ i) i| : ℝ) ≤
        ((r - 1).factorial : ℝ) * (8 : ℝ) ^ (r - 1) := by
      have h1 : (|∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℤ) *
            ∏ i : Fin r, Mk (σ i) i| : ℝ) ≤
          ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin r) => σ ⟨0, by omega⟩ = k),
            (|(Equiv.Perm.sign σ : ℤ) * ∏ i : Fin r, Mk (σ i) i| : ℝ) := by
        have hzero : ∀ σ : Equiv.Perm (Fin r), σ ⟨0, by omega⟩ ≠ k →
            (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin r, Mk (σ i) i = 0 := by
          intro σ hne
          have hfac0 : Mk (σ (σ⁻¹ k)) (σ⁻¹ k) = 0 := by
            have hinv : σ (σ⁻¹ k) = k := Equiv.apply_symm_apply σ k
            rw [hinv]
            dsimp [Mk]
            rw [Matrix.updateRow_self]
            have hne' : σ⁻¹ k ≠ ⟨0, by omega⟩ := fun h => hne (by rw [← h, hinv])
            exact Pi.single_eq_of_ne hne' _
          rw [Finset.prod_eq_zero (f := fun i => Mk (σ i) i) (Finset.mem_univ (σ⁻¹ k)) hfac0, mul_zero]
        have hsub : ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin r, Mk (σ i) i =
            ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin r) => σ ⟨0, by omega⟩ = k),
              (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin r, Mk (σ i) i := by
          symm
          refine Finset.sum_subset (Finset.filter_subset _ _) fun σ _ hσ => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
          exact hzero σ hσ
        have habs_int : |∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin r, Mk (σ i) i| ≤
            ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin r) => σ ⟨0, by omega⟩ = k),
              |(Equiv.Perm.sign σ : ℤ) * ∏ i : Fin r, Mk (σ i) i| := by
          rw [hsub]; exact Finset.abs_sum_le_sum_abs _ _
        exact_mod_cast habs_int
      refine h1.trans ?_
      have hterm : ∀ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin r) => σ ⟨0, by omega⟩ = k),
          (|(Equiv.Perm.sign σ : ℤ) * ∏ i : Fin r, Mk (σ i) i| : ℝ) ≤ (8 : ℝ) ^ (r - 1) := by
        intro σ hσ
        have hσ0 : σ ⟨0, by omega⟩ = k := (Finset.mem_filter.mp hσ).2
        have hsgn : |(Equiv.Perm.sign σ : ℤ)| = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        have hprod : |∏ i : Fin r, Mk (σ i) i| ≤ (8 : ℤ) ^ (r - 1) := by
          let z0 : Fin r := ⟨0, by omega⟩
          rw [Finset.abs_prod, ← Finset.mul_prod_erase Finset.univ (fun i => |Mk (σ i) i|) (Finset.mem_univ z0)]
          have h0val : |Mk (σ z0) z0| = 1 := by
            dsimp [Mk, z0]
            rw [hσ0, Matrix.updateRow_self, Pi.single_eq_same]; norm_num
          rw [h0val, one_mul]
          calc ∏ i ∈ Finset.univ.erase z0, |Mk (σ i) i|
              ≤ ∏ _i ∈ Finset.univ.erase z0, (8 : ℤ) := by
                refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i hi => ?_
                have hine : σ i ≠ k := fun h => (Finset.mem_erase.mp hi).1 (σ.injective (h.trans hσ0.symm))
                dsimp [Mk]
                rw [Matrix.updateRow_ne hine]
                exact hW (σ i) i
            _ = (8 : ℤ) ^ (r - 1) := by
                rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
                  Finset.card_univ, Fintype.card_fin]
        have hmul : |(Equiv.Perm.sign σ : ℤ) * ∏ i : Fin r, Mk (σ i) i| ≤ (8 : ℤ) ^ (r - 1) := by
          rw [abs_mul, hsgn, one_mul]; exact hprod
        exact_mod_cast hmul
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, hperm_count, nsmul_eq_mul]
    simp only [Units.smul_def, zsmul_eq_mul]
    have habs_cast : (|(∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin r, Mk (σ i) i : ℤ)| : ℝ) =
        |∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((∏ i : Fin r, Mk (σ i) i : ℤ) : ℝ)| := by
      push_cast; rfl
    exact habs_cast.trans_le hsum_le
  -- Now bound |W.det| using hvec
  have hdet_upper : (|W.det| : ℝ) < 1 := by
    have hEq : (W.det : ℝ) = ∑ k : Fin r, (W.adjugate ⟨0, by omega⟩ k : ℝ) *
        (∑ s : Fin r, (W k s : ℝ) * u s) := by
      rw [← hdet_eq, ← hvec]
      simp only [Matrix.mulVec, dotProduct, hadj_eq, WR, Matrix.map_apply]
    have habs : (|W.det| : ℝ) = |(W.det : ℝ)| := by exact_mod_cast rfl
    rw [habs, hEq]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_lt ?_
    have hterm_lt : ∀ k : Fin r,
        |(W.adjugate ⟨0, by omega⟩ k : ℝ) * (∑ s : Fin r, (W k s : ℝ) * u s)| <
          ((r - 1).factorial : ℝ) * (8 : ℝ) ^ (r - 1) * (2 * (r.factorial : ℝ) * (8 : ℝ) ^ r)⁻¹ +
          (2 * (r : ℝ))⁻¹ := by
      -- Even cleaner: since r ≥ 1, use strict inequality directly!
      intro k
      rw [abs_mul]
      have h1 : |(W.adjugate ⟨0, by omega⟩ k : ℝ)| ≤ ((r - 1).factorial : ℝ) * (8 : ℝ) ^ (r - 1) := by
        exact_mod_cast hadj_bound k
      have h2 := hsmall k
      have h3 : |(W.adjugate ⟨0, by omega⟩ k : ℝ)| * |∑ s : Fin r, (W k s : ℝ) * u s| ≤
          ((r - 1).factorial : ℝ) * (8 : ℝ) ^ (r - 1) * (2 * (r.factorial : ℝ) * (8 : ℝ) ^ r)⁻¹ :=
        mul_le_mul h1 h2.le (abs_nonneg _) (by positivity)
      have hpos : (0 : ℝ) < (2 * (r : ℝ))⁻¹ := by positivity
      linarith
    have hsum_lt : ∑ k : Fin r, |(W.adjugate ⟨0, by omega⟩ k : ℝ) * (∑ s : Fin r, (W k s : ℝ) * u s)| <
        ∑ _k : Fin r, (((r - 1).factorial : ℝ) * (8 : ℝ) ^ (r - 1) *
          (2 * (r.factorial : ℝ) * (8 : ℝ) ^ r)⁻¹ + (2 * (r : ℝ))⁻¹) :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩) (fun k _ => hterm_lt k)
    refine hsum_lt.trans_le ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add]
    have hfac : (r.factorial : ℝ) = (r : ℝ) * ((r - 1).factorial : ℝ) := by
      cases r with
      | zero => omega
      | succ r' => push_cast [Nat.factorial_succ]; ring
    have hpow8 : (8 : ℝ) ^ r = 8 * (8 : ℝ) ^ (r - 1) := by
      cases r with
      | zero => omega
      | succ r' => simp [pow_succ, mul_comm]
    have hrpos : (0 : ℝ) < r := by positivity
    have hfacpos : (0 : ℝ) < ((r - 1).factorial : ℝ) := by positivity
    have h8pos : (0 : ℝ) < (8 : ℝ) ^ (r - 1) := by positivity
    have hfirst : (r : ℝ) * (((r - 1).factorial : ℝ) * (8 : ℝ) ^ (r - 1) *
        (2 * (r.factorial : ℝ) * (8 : ℝ) ^ r)⁻¹) = 1 / 16 := by
      rw [hfac, hpow8]
      field_simp [hrpos.ne', hfacpos.ne', h8pos.ne']
      ring
    have hsecond : (r : ℝ) * (2 * (r : ℝ))⁻¹ = 1 / 2 := by
      field_simp [hrpos.ne']
    rw [hfirst, hsecond]
    norm_num
  linarith

/-- If every r x r submatrix of rows w j (j ∈ I) has det 0, there is a nonzero rational vector c
orthogonal to all rows w j (j ∈ I). -/
lemma exists_rational_annihilator {r : ℕ} (hr : 1 ≤ r) (I : Finset ℤ) (w : ℤ → Fin r → ℤ)
    (hdet : ∀ f : Fin r → ℤ, (∀ k, f k ∈ I) → (Matrix.of fun k s => w (f k) s).det = 0) :
    ∃ c : Fin r → ℚ, c ≠ 0 ∧ ∀ j ∈ I, ∑ s : Fin r, c s * (w j s : ℚ) = 0 := by
  classical
  let v : ℤ → (Fin r → ℚ) := fun j s => (w j s : ℚ)
  let S : Submodule ℚ (Fin r → ℚ) := Submodule.span ℚ (v '' (I : Set ℤ))
  have hlt : Module.finrank ℚ S < r := by
    by_contra hge
    push Not at hge
    have htop : S = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      have hle := Submodule.finrank_le S
      rw [Module.finrank_pi, Fintype.card_fin] at hle ⊢
      omega
    -- Extract a basis of S = ⊤ from the spanning set v '' I
    obtain ⟨b, hb_sub, hb_span, hb_li⟩ := exists_linearIndependent ℚ (v '' (I : Set ℤ))
    have hfin : b.Finite := ((Finset.finite_toSet I).image v).subset hb_sub
    letI : Fintype b := hfin.fintype
    have hb_card : Fintype.card b = r := by
      have hbasis : Module.Basis b ℚ (Fin r → ℚ) :=
        Module.Basis.mk hb_li (by rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hb_span, ← htop])
      have hcr := Module.finrank_eq_card_basis hbasis
      rw [Module.finrank_pi, Fintype.card_fin] at hcr
      exact hcr.symm
    let e : Fin r ≃ b := (Fintype.equivFinOfCardEq hb_card).symm
    have hchoose : ∀ k : Fin r, ∃ j ∈ I, v j = (e k).val := fun k => hb_sub (e k).2
    choose f hfI hfv using hchoose
    let M : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun k s => w (f k) s
    let MQ : Matrix (Fin r) (Fin r) ℚ := M.map (Int.cast : ℤ → ℚ)
    have hMQ_li : LinearIndependent ℚ (fun k : Fin r => MQ k) := by
      have hEq : (fun k : Fin r => MQ k) = fun k => (e k).val := by
        ext k s
        have := congrFun (hfv k) s
        simpa [MQ, M, v] using this
      rw [hEq]
      exact hb_li.comp e e.injective
    have hMQ_det : MQ.det ≠ 0 := by
      have hunit : IsUnit MQ := (Matrix.linearIndependent_rows_iff_isUnit (A := MQ)).mp hMQ_li
      exact ((Matrix.isUnit_iff_isUnit_det MQ).mp hunit).ne_zero
    have hM0 : M.det = 0 := hdet f hfI
    have hMQ0 : MQ.det = 0 := by
      have hmap : MQ.det = (Int.castRingHom ℚ) M.det := by
        simpa [MQ] using (RingHom.map_det (Int.castRingHom ℚ) M).symm
      rw [hmap, hM0, map_zero]
    exact hMQ_det hMQ0
  have hne_top : S ≠ ⊤ := by
    intro h
    rw [h, finrank_top, Module.finrank_pi, Fintype.card_fin] at hlt
    omega
  obtain ⟨φ, hφ_ne, hφ_S⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne_top)
  let c : Fin r → ℚ := fun s => φ (Pi.single s 1)
  refine ⟨c, ?_, ?_⟩
  · intro hc
    apply hφ_ne
    refine LinearMap.ext fun x => ?_
    have hx : x = ∑ s : Fin r, x s • Pi.single s (1 : ℚ) := by
      ext t; simp [Finset.sum_apply, Pi.single_apply]
    rw [hx, map_sum]
    simp only [LinearMap.zero_apply, map_smul, smul_eq_mul]
    refine Finset.sum_eq_zero fun s _ => ?_
    have : c s = 0 := congrFun hc s
    simp [c, this]
  · intro j hj
    have hvS : v j ∈ S := Submodule.subset_span ⟨j, hj, rfl⟩
    have h0 : φ (v j) = 0 := hφ_S hvS
    have hvx : v j = ∑ s : Fin r, (w j s : ℚ) • Pi.single s (1 : ℚ) := by
      ext t; simp [v, Finset.sum_apply, Pi.single_apply]
    rw [hvx, map_sum] at h0
    simp only [map_smul, smul_eq_mul] at h0
    simpa [c, mul_comm] using h0

/-- Root-of-unity order bound: if a primitive q-th root of unity in C is a root of a nonzero
rational polynomial of degree ≤ r, then q divides (2 * r)!. -/
lemma order_dvd_factorial_of_isRoot_rat {q r : ℕ} (hq : 0 < q) (ω : ℂ)
    (hprim : IsPrimitiveRoot ω q) (Q : Polynomial ℚ) (hQ0 : Q ≠ 0) (hQdeg : Q.natDegree ≤ r)
    (hroot : Polynomial.aeval ω Q = 0) :
    q ∣ (2 * r).factorial := by
  -- cyclotomic q ℚ is irreducible and has ω as a root, so it divides Q
  have hcyc_root : Polynomial.aeval ω (Polynomial.cyclotomic q ℚ) = 0 := by
    have h1 := hprim.isRoot_cyclotomic hq
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact h1
  have hcyc_irr : Irreducible (Polynomial.cyclotomic q ℚ) := Polynomial.cyclotomic.irreducible_rat hq
  have hmin_dvd_Q : minpoly ℚ ω ∣ Q := minpoly.dvd ℚ ω hroot
  have hmin_dvd_cyc : minpoly ℚ ω ∣ Polynomial.cyclotomic q ℚ := minpoly.dvd ℚ ω hcyc_root
  have hmin_nu : ¬ IsUnit (minpoly ℚ ω) := by
    intro hu
    have hdeg0 : (minpoly ℚ ω).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hint : IsIntegral ℚ ω :=
      ⟨Polynomial.cyclotomic q ℚ, Polynomial.cyclotomic.monic q ℚ, hcyc_root⟩
    have hne : minpoly ℚ ω ≠ 0 := minpoly.ne_zero hint
    have h0 := minpoly.aeval ℚ ω
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, Polynomial.aeval_C] at h0
    have hc0 : (minpoly ℚ ω).coeff 0 = 0 := (RingHom.injective (algebraMap ℚ ℂ)) (by simpa using h0)
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, hc0, map_zero] at hne
    exact hne rfl
  have hcyc_dvd_Q : Polynomial.cyclotomic q ℚ ∣ Q := by
    obtain ⟨u, hu⟩ := hmin_dvd_cyc
    rcases hcyc_irr.isUnit_or_isUnit hu with h1 | h2
    · exact absurd h1 hmin_nu
    · obtain ⟨v, hv⟩ := h2.exists_right_inv
      have hdiv : Polynomial.cyclotomic q ℚ ∣ minpoly ℚ ω := ⟨v, by rw [hu, mul_assoc, hv, mul_one]⟩
      exact hdiv.trans hmin_dvd_Q
  have htot_le : Nat.totient q ≤ r := by
    have hdeg_le := Polynomial.natDegree_le_of_dvd hcyc_dvd_Q hQ0
    rw [Polynomial.natDegree_cyclotomic] at hdeg_le
    exact hdeg_le.trans hQdeg
  -- For each prime factor p of q, p^a ≤ 2 * totient(p^a) ≤ 2 * totient(q) ≤ 2 * r, so p^a ∣ (2r)!
  have hprod : q = ∏ p ∈ q.primeFactors, p ^ (q.factorization p) :=
    (Nat.prod_factorization_pow_eq_self hq.ne').symm
  rw [hprod]
  have hdvd_each : ∀ p ∈ q.primeFactors, p ^ (q.factorization p) ∣ (2 * r).factorial := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have ha_pos : 1 ≤ q.factorization p := Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp (by simpa [Nat.support_factorization] using hp))
    have hpow_dvd : p ^ (q.factorization p) ∣ q := Nat.ordProj_dvd q p
    have htot_dvd : Nat.totient (p ^ (q.factorization p)) ∣ Nat.totient q :=
      Nat.totient_dvd_of_dvd hpow_dvd
    have htot_pow : Nat.totient (p ^ (q.factorization p)) = p ^ (q.factorization p - 1) * (p - 1) :=
      Nat.totient_prime_pow hpp ha_pos
    have htot_q_pos : 0 < Nat.totient q := Nat.totient_pos.mpr hq
    have hle1 : p ^ (q.factorization p - 1) * (p - 1) ≤ r := by
      rw [← htot_pow]
      exact (Nat.le_of_dvd htot_q_pos htot_dvd).trans htot_le
    have hpow_le : p ^ (q.factorization p) ≤ 2 * r := by
      have hp2 : 2 ≤ p := hpp.two_le
      have hdecomp : p ^ (q.factorization p) = p ^ (q.factorization p - 1) * p := by
        conv_lhs => rw [show q.factorization p = (q.factorization p - 1) + 1 by omega, pow_succ]
      rw [hdecomp]
      have : p ≤ 2 * (p - 1) := by omega
      nlinarith [Nat.one_le_pow (q.factorization p - 1) p hpp.pos]
    exact Nat.dvd_factorial (pow_pos hpp.pos _) hpow_le
  have hprod_dvd : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      (∀ p ∈ s, p ^ (q.factorization p) ∣ (2 * r).factorial) →
      (∏ p ∈ s, p ^ (q.factorization p)) ∣ (2 * r).factorial := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ _; simp
    | insert a s ha ih =>
      intro hpr hd
      rw [Finset.prod_insert ha]
      have ha_pr := hpr a (Finset.mem_insert_self a s)
      have hs_pr : ∀ p ∈ s, p.Prime := fun p hp => hpr p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime (a ^ (q.factorization a)) (∏ p ∈ s, p ^ (q.factorization p)) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have hne : a ≠ p := fun h => ha (h ▸ hp)
        exact ((Nat.coprime_primes ha_pr (hs_pr p hp)).mpr hne).pow _ _
      exact hcop.mul_dvd_of_dvd_of_dvd (hd a (Finset.mem_insert_self a s))
        (ih hs_pr fun p hp => hd p (Finset.mem_insert_of_mem hp))
  exact hprod_dvd q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) hdvd_each

/-- A T0-periodic integer sequence satisfying a rational linear recurrence of order ≤ r
is actually (2*r)!-periodic. -/
lemma periodic_factorial_of_recurrence {T₀ r : ℕ} (hT0 : 0 < T₀) (h : ℕ) (hhr : h ≤ r)
    (b : ℤ → ℤ) (hper : ∀ j : ℤ, b (j + (T₀ : ℤ)) = b j)
    (c : Fin (h + 1) → ℚ) (hcu : c ⟨h, by omega⟩ ≠ 0)
    (hrec : ∀ j : ℤ, ∑ s : Fin (h + 1), c s * (b (j + (s.val : ℤ)) : ℚ) = 0) :
    ∀ j : ℤ, b (j + ((2 * r).factorial : ℤ)) = b j := by
  let P : ℕ := (2 * r).factorial
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (T₀ : ℂ))
  have hζ_pow : ζ ^ T₀ = 1 := by
    dsimp [ζ]
    rw [← Complex.exp_nat_mul]
    have hT0c : (T₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT0.ne'
    have : (T₀ : ℂ) * (2 * Real.pi * Complex.I / (T₀ : ℂ)) = 2 * Real.pi * Complex.I := by
      field_simp [hT0c]
    rw [this]
    exact Complex.exp_two_pi_mul_I
  have hζ_ne : ζ ≠ 0 := Complex.exp_ne_zero _
  -- Finite DFT coefficients
  let bhat : Fin T₀ → ℂ := fun k =>
    (T₀ : ℂ)⁻¹ * ∑ t : Fin T₀, (b (t.val : ℤ) : ℂ) * (ζ ^ k.val)⁻¹ ^ t.val
  -- Orthogonality of roots of unity
  have horth : ∀ (a : ℤ),
      (∑ k : Fin T₀, (ζ ^ k.val) ^ a) = if (T₀ : ℤ) ∣ a then (T₀ : ℂ) else 0 := by
    intro a
    have hterm : ∀ k : Fin T₀, (ζ ^ k.val) ^ a = (ζ ^ a) ^ k.val := by
      intro k
      rw [← zpow_natCast ζ k.val, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    simp_rw [hterm]
    split_ifs with hdvd
    · obtain ⟨q, rfl⟩ := hdvd
      have h1 : ζ ^ ((T₀ : ℤ) * q) = 1 := by
        rw [zpow_mul, zpow_natCast, hζ_pow, one_zpow]
      simp [h1]
    · have hne1 : ζ ^ a ≠ 1 := by
        intro heq
        dsimp [ζ] at heq
        rw [← Complex.exp_int_mul, Complex.exp_eq_one_iff] at heq
        obtain ⟨q, hq⟩ := heq
        have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
          refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
          exact_mod_cast Real.pi_ne_zero
        have hT0c : (T₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT0.ne'
        have h1 : (a : ℂ) * (2 * Real.pi * Complex.I) = ((T₀ : ℂ) * (q : ℂ)) * (2 * Real.pi * Complex.I) := by
          have := congrArg (fun z => (T₀ : ℂ) * z) hq
          have h2 : (T₀ : ℂ) * ((a : ℂ) * (2 * Real.pi * Complex.I / (T₀ : ℂ))) =
              (a : ℂ) * (2 * Real.pi * Complex.I) := by field_simp [hT0c]
          rw [h2] at this
          linear_combination this
        have h2 : (a : ℂ) = (T₀ : ℂ) * (q : ℂ) := mul_right_cancel₀ hpi h1
        have h3 : a = (T₀ : ℤ) * q := by exact_mod_cast h2
        exact hdvd ⟨q, h3⟩
      rw [Fin.sum_univ_eq_sum_range (fun k => (ζ ^ a) ^ k), geom_sum_eq hne1]
      have hpow0 : (ζ ^ a) ^ T₀ = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ_pow, one_zpow]
      rw [hpow0, sub_self, zero_div]
  -- DFT inversion: for every j : ℤ, (b j : ℂ) = ∑ k, bhat k * (ζ ^ k.val) ^ j
  have hdft_inv : ∀ j : ℤ, (b j : ℂ) = ∑ k : Fin T₀, bhat k * (ζ ^ k.val) ^ j := by
    intro j
    have hT0c : (T₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT0.ne'
    dsimp [bhat]
    simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hinner : ∀ t : Fin T₀,
        ∑ k : Fin T₀, (b (t.val : ℤ) : ℂ) * ((ζ ^ k.val)⁻¹ ^ t.val * (ζ ^ k.val) ^ j) =
          (b (t.val : ℤ) : ℂ) * if (T₀ : ℤ) ∣ (j - (t.val : ℤ)) then (T₀ : ℂ) else 0 := by
      intro t
      rw [← Finset.mul_sum]
      congr 1
      have hterm : ∀ k : Fin T₀, (ζ ^ k.val)⁻¹ ^ t.val * (ζ ^ k.val) ^ j =
          (ζ ^ k.val) ^ (j - (t.val : ℤ)) := by
        intro k
        rw [inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (pow_ne_zero k.val hζ_ne)]
        congr 1; ring
      simp_rw [hterm]
      exact horth (j - (t.val : ℤ))
    simp_rw [mul_assoc]
    rw [Finset.sum_congr rfl fun t _ => hinner t]
    let r0 : Fin T₀ := ⟨(j % (T₀ : ℤ)).toNat, by
      have h1 := Int.emod_nonneg j (Int.natCast_ne_zero.mpr hT0.ne')
      have h2 := Int.emod_lt_of_pos j (Int.natCast_pos.mpr hT0)
      omega⟩
    have hr0_mod : (r0.val : ℤ) = j % (T₀ : ℤ) := by
      have h1 := Int.emod_nonneg j (Int.natCast_ne_zero.mpr hT0.ne')
      exact Int.toNat_of_nonneg h1
    have hr0_dvd : (T₀ : ℤ) ∣ (j - (r0.val : ℤ)) := by
      rw [hr0_mod]
      exact ⟨j / (T₀ : ℤ), by linarith [Int.mul_ediv_add_emod j (T₀ : ℤ)]⟩
    rw [Finset.sum_eq_single r0]
    · rw [if_pos hr0_dvd]
      have hbj : b j = b (r0.val : ℤ) := by
        obtain ⟨q, hq⟩ := hr0_dvd
        have hj : j = (r0.val : ℤ) + q * (T₀ : ℤ) := by linarith
        rw [hj]
        have hper_mul : ∀ m : ℤ, b ((r0.val : ℤ) + m * (T₀ : ℤ)) = b (r0.val : ℤ) := by
          intro m
          induction m using Int.induction_on with
          | zero => rw [zero_mul, add_zero]
          | succ n ih =>
            rw [show (r0.val : ℤ) + ((n : ℤ) + 1) * (T₀ : ℤ) =
              ((r0.val : ℤ) + (n : ℤ) * (T₀ : ℤ)) + (T₀ : ℤ) by ring, hper, ih]
          | pred n ih =>
            have h1 := hper ((r0.val : ℤ) + (-(n : ℤ) - 1) * (T₀ : ℤ))
            rw [show (r0.val : ℤ) + (-(n : ℤ) - 1) * (T₀ : ℤ) + (T₀ : ℤ) =
              (r0.val : ℤ) + (-(n : ℤ)) * (T₀ : ℤ) by ring] at h1
            exact h1.symm.trans ih
        exact hper_mul q
      rw [hbj]
      field_simp [hT0c]
    · intro t _ htr
      have hndvd : ¬ (T₀ : ℤ) ∣ (j - (t.val : ℤ)) := by
        intro hdvd
        have hd2 : (T₀ : ℤ) ∣ ((t.val : ℤ) - (r0.val : ℤ)) := by
          have : (t.val : ℤ) - (r0.val : ℤ) = (j - (r0.val : ℤ)) - (j - (t.val : ℤ)) := by ring
          rw [this]; exact dvd_sub hr0_dvd hdvd
        obtain ⟨q, hq⟩ := hd2
        have hlt1 : (t.val : ℤ) < (T₀ : ℤ) := by exact_mod_cast t.isLt
        have hlt2 : (r0.val : ℤ) < (T₀ : ℤ) := by exact_mod_cast r0.isLt
        have hq0 : q = 0 := by nlinarith
        rw [hq0, mul_zero] at hq
        have heq : t.val = r0.val := by omega
        exact htr (Fin.ext heq)
      rw [if_neg hndvd, mul_zero]
    · intro h; exact absurd (Finset.mem_univ r0) h
  -- Characteristic polynomial Q ∈ ℚ[X]
  let Q : Polynomial ℚ := ∑ s : Fin (h + 1), Polynomial.C (c s) * Polynomial.X ^ s.val
  have hQ_coeff : ∀ i : ℕ, Q.coeff i = if hi : i < h + 1 then c ⟨i, hi⟩ else 0 := by
    intro i
    dsimp [Q]
    rw [Polynomial.finset_sum_coeff]
    split_ifs with hi
    · rw [Finset.sum_eq_single ⟨i, hi⟩]
      · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      · intro s _ hs
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, show i ≠ s.val from fun he => hs (Fin.ext he.symm)]
      · intro hn; exact absurd (Finset.mem_univ _) hn
    · refine Finset.sum_eq_zero fun s _ => ?_
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, show i ≠ s.val by omega]
  have hQ_ne : Q ≠ 0 := by
    intro h0
    have := hQ_coeff h
    rw [h0, Polynomial.coeff_zero, dif_pos (by omega)] at this
    exact hcu this.symm
  have hQ_deg : Q.natDegree ≤ r := by
    refine le_trans ?_ hhr
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [hQ_coeff, dif_neg (by omega)]
  -- For each k with bhat k ≠ 0, ω = ζ^k is a root of Q, hence ω^P = 1
  have hpowP : ∀ k : Fin T₀, bhat k ≠ 0 → (ζ ^ k.val) ^ P = 1 := by
    intro k hk
    have hroot : Polynomial.aeval (ζ ^ k.val) Q = 0 := by
      -- Multiply recurrence at j = t by (ζ^k)⁻¹^t and sum over t : Fin T₀
      have hsum0 : ∑ t : Fin T₀, (∑ s : Fin (h + 1), ((c s : ℝ) : ℂ) * (b ((t.val : ℤ) + (s.val : ℤ)) : ℂ)) *
          (ζ ^ k.val)⁻¹ ^ t.val = 0 := by
        refine Finset.sum_eq_zero fun t _ => ?_
        have hrt := hrec (t.val : ℤ)
        have hrtC : (∑ s : Fin (h + 1), ((c s : ℝ) : ℂ) * (b ((t.val : ℤ) + (s.val : ℤ)) : ℂ)) = 0 := by
          have := congrArg (Rat.cast (K := ℂ)) hrt
          rw [Rat.cast_sum, Rat.cast_zero] at this
          rw [← this]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Rat.cast_mul, Rat.cast_intCast, Complex.ofReal_ratCast]
        rw [hrtC, zero_mul]
      have hcalc : (T₀ : ℂ) * (bhat k * Polynomial.aeval (ζ ^ k.val) Q) = 0 := by
        rw [← hsum0]
        dsimp [Q, bhat]
        rw [map_sum]
        simp_rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
        have hT0c : (T₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT0.ne'
        rw [show (T₀ : ℂ) * ((T₀ : ℂ)⁻¹ * (∑ t : Fin T₀, (b (t.val : ℤ) : ℂ) * (ζ ^ k.val)⁻¹ ^ t.val) *
            ∑ x : Fin (h + 1), algebraMap ℚ ℂ (c x) * (ζ ^ k.val) ^ x.val) =
          ((T₀ : ℂ) * (T₀ : ℂ)⁻¹) * ((∑ t : Fin T₀, (b (t.val : ℤ) : ℂ) * (ζ ^ k.val)⁻¹ ^ t.val) *
            ∑ x : Fin (h + 1), algebraMap ℚ ℂ (c x) * (ζ ^ k.val) ^ x.val) by ring,
          mul_inv_cancel₀ hT0c, one_mul, Finset.mul_sum]
        conv_rhs =>
          arg 2; ext t
          rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
        -- Shift index t ↦ (t + s) mod T₀
        let shift : Fin T₀ ≃ Fin T₀ :=
          { toFun := fun t => ⟨(t.val + s.val) % T₀, Nat.mod_lt _ hT0⟩
            invFun := fun u => ⟨(u.val + (T₀ - s.val % T₀)) % T₀, Nat.mod_lt _ hT0⟩
            left_inv := fun t => by
              ext; dsimp only
              have hmod : (t.val + s.val) % T₀ + (T₀ - s.val % T₀) ≡ t.val + s.val + (T₀ - s.val % T₀) [MOD T₀] :=
                (Nat.mod_modEq _ _).add_right _
              have hle : s.val % T₀ ≤ T₀ := (Nat.mod_lt _ hT0).le
              have h1 : (t.val + s.val + (T₀ - s.val % T₀)) % T₀ = t.val % T₀ := by
                have hdiv := Nat.div_add_mod s.val T₀
                have hmul : s.val + (T₀ - s.val % T₀) = (s.val / T₀ + 1) * T₀ := by
                  rw [add_mul, one_mul, mul_comm (s.val / T₀) T₀]
                  omega
                rw [add_assoc, hmul, Nat.add_mul_mod_self_right]
              rw [Nat.ModEq] at hmod
              rw [hmod, h1, Nat.mod_eq_of_lt t.isLt]
            right_inv := fun u => by
              ext; dsimp only
              have hmod : (u.val + (T₀ - s.val % T₀)) % T₀ + s.val ≡ u.val + (T₀ - s.val % T₀) + s.val [MOD T₀] :=
                (Nat.mod_modEq _ _).add_right _
              have hle : s.val % T₀ ≤ T₀ := (Nat.mod_lt _ hT0).le
              have h1 : (u.val + (T₀ - s.val % T₀) + s.val) % T₀ = u.val % T₀ := by
                have hdiv := Nat.div_add_mod s.val T₀
                have hmul : (T₀ - s.val % T₀) + s.val = (s.val / T₀ + 1) * T₀ := by
                  rw [add_mul, one_mul, mul_comm (s.val / T₀) T₀]
                  omega
                rw [add_assoc, hmul, Nat.add_mul_mod_self_right]
              rw [Nat.ModEq] at hmod
              rw [hmod, h1, Nat.mod_eq_of_lt u.isLt] }
        rw [← Equiv.sum_comp shift]
        refine Finset.sum_congr rfl fun t _ => ?_
        have hb_shift : b ((shift t).val : ℤ) = b ((t.val : ℤ) + (s.val : ℤ)) := by
          dsimp only [shift]
          have hq : T₀ * ((t.val + s.val) / T₀) + (t.val + s.val) % T₀ = t.val + s.val :=
            Nat.div_add_mod (t.val + s.val) T₀
          have hEq : ((t.val : ℤ) + (s.val : ℤ)) = (((t.val + s.val) % T₀ : ℕ) : ℤ) +
              (((t.val + s.val) / T₀ : ℕ) : ℤ) * (T₀ : ℤ) := by
            have hqZ : (T₀ : ℤ) * (((t.val + s.val) / T₀ : ℕ) : ℤ) +
                (((t.val + s.val) % T₀ : ℕ) : ℤ) = (t.val : ℤ) + (s.val : ℤ) := by
              exact_mod_cast hq
            linarith
          have hper_nat : ∀ (a : ℤ) (m : ℕ), b (a + (m : ℤ) * (T₀ : ℤ)) = b a := by
            intro a m
            induction m with
            | zero => rw [Nat.cast_zero, zero_mul, add_zero]
            | succ m ih =>
              rw [show a + ((m + 1 : ℕ) : ℤ) * (T₀ : ℤ) = (a + (m : ℤ) * (T₀ : ℤ)) + (T₀ : ℤ) by push_cast; ring,
                hper, ih]
          conv_rhs => rw [hEq]
          exact (hper_nat _ _).symm
        have hζ_shift : (ζ ^ k.val)⁻¹ ^ (shift t).val * (ζ ^ k.val) ^ s.val =
            (ζ ^ k.val)⁻¹ ^ t.val := by
          have hord : (ζ ^ k.val) ^ T₀ = 1 := by
            rw [← pow_mul, mul_comm, pow_mul, hζ_pow, one_pow]
          have hinv_ord : (ζ ^ k.val)⁻¹ ^ T₀ = 1 := by
            rw [inv_pow, hord, inv_one]
          have hq := Nat.div_add_mod (t.val + s.val) T₀
          have hmul1 : (ζ ^ k.val)⁻¹ ^ (shift t).val = (ζ ^ k.val)⁻¹ ^ (t.val + s.val) := by
            dsimp [shift]
            conv_rhs => rw [← hq, pow_add, pow_mul, hinv_ord, one_pow, one_mul]
          rw [hmul1, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ (pow_ne_zero k.val hζ_ne),
            one_pow, mul_one]
        rw [hb_shift]
        have hcast : algebraMap ℚ ℂ (c s) = ((c s : ℝ) : ℂ) := by
          simp [Rat.cast_def]
        rw [hcast]
        calc (b ((t.val : ℤ) + (s.val : ℤ)) : ℂ) * (ζ ^ k.val)⁻¹ ^ (shift t).val *
              (((c s : ℝ) : ℂ) * (ζ ^ k.val) ^ s.val)
            = ((c s : ℝ) : ℂ) * (b ((t.val : ℤ) + (s.val : ℤ)) : ℂ) *
              ((ζ ^ k.val)⁻¹ ^ (shift t).val * (ζ ^ k.val) ^ s.val) := by ring
          _ = ((c s : ℝ) : ℂ) * (b ((t.val : ℤ) + (s.val : ℤ)) : ℂ) * (ζ ^ k.val)⁻¹ ^ t.val := by
              rw [hζ_shift]
      have hT0c : (T₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hT0.ne'
      exact mul_left_cancel₀ hk (mul_left_cancel₀ hT0c (by simpa using hcalc))
    let ω : ℂ := ζ ^ k.val
    have hω_fin : IsOfFinOrder ω := by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨T₀, hT0, by dsimp [ω]; rw [← pow_mul, mul_comm, pow_mul, hζ_pow, one_pow]⟩
    let q := orderOf ω
    have hq_pos : 0 < q := orderOf_pos_iff.mpr hω_fin
    have hprim : IsPrimitiveRoot ω q := IsPrimitiveRoot.orderOf ω
    have hdvd : q ∣ P := order_dvd_factorial_of_isRoot_rat hq_pos ω hprim Q hQ_ne hQ_deg hroot
    obtain ⟨m, hm⟩ := hdvd
    rw [hm, pow_mul, pow_orderOf_eq_one, one_pow]
  -- Conclude b (j + P) = b j for all j : ℤ
  intro j
  have hC : (b (j + (P : ℤ)) : ℂ) = (b j : ℂ) := by
    rw [hdft_inv (j + (P : ℤ)), hdft_inv j]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : bhat k = 0
    · simp [hk]
    · rw [zpow_add₀ (pow_ne_zero k.val hζ_ne), zpow_natCast, hpowP k hk, mul_one]
  exact Int.cast_injective hC

/-- Key structural lemma (Section 2): if |v_j| < δ on [A, B], then at most L indices in [A, B]
have β_j ≠ 0, and at most L indices in [A, B] have v_j ≠ 0. -/
lemma small_interval_bound (d : ℕ) (p : ℤ → ℤ) (hp0 : ∀ j, 0 ≤ p j) (hp4 : ∀ j, p j ≤ 4)
    (u : ℤ → ℝ) (hu_supp : ∀ l : ℤ, ¬ (- (d : ℤ) ≤ l ∧ l ≤ (d : ℤ)) → u l = 0)
    (hud : u (d : ℤ) = 1) :
    let r := 2 * d + 1
    let P := (2 * r).factorial
    let β : ℤ → ℤ := fun j => p (j - (P : ℤ)) - 2 * p j + p (j + (P : ℤ))
    let v : ℤ → ℝ := fun j => ∑ l ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), u l * (β (j - l) : ℝ)
    let δ : ℝ := (2 * (r.factorial : ℝ) * (8 : ℝ) ^ r)⁻¹
    let L : ℕ := 17 ^ r + 4 * r + 10 * P + 10
    ∀ (A B : ℤ), (∀ j ∈ Finset.Icc A B, |v j| < δ) →
      ((Finset.Icc A B).filter (fun j => β j ≠ 0)).card ≤ L ∧
      ((Finset.Icc A B).filter (fun j => v j ≠ 0)).card ≤ L := by
  classical
  intro r P β v δ L A B hsmall
  have hr1 : 1 ≤ r := by omega
  have hβ8 : ∀ j : ℤ, |β j| ≤ 8 := by
    intro j
    have h1 := hp0 (j - P); have h2 := hp4 (j - P)
    have h3 := hp0 j; have h4 := hp4 j
    have h5 := hp0 (j + P); have h6 := hp4 (j + P)
    dsimp [β]; rw [abs_le]; constructor <;> omega
  by_cases hshort : (Finset.Icc A B).card ≤ 17 ^ r
  · constructor
    · exact (Finset.card_filter_le _ _).trans (hshort.trans (by omega))
    · exact (Finset.card_filter_le _ _).trans (hshort.trans (by omega))
  -- Apply Cramer rank bound to rows w j s = β (j + s - d)
  let w : ℤ → Fin r → ℤ := fun j s => β (j + (s.val : ℤ) - (d : ℤ))
  let uVec : Fin r → ℝ := fun s => u ((d : ℤ) - (s.val : ℤ))
  have hdet0 : ∀ f : Fin r → ℤ, (∀ k, f k ∈ Finset.Icc A B) →
      (Matrix.of fun k s => w (f k) s).det = 0 := by
    intro f hf
    refine det_eq_zero_of_small_mulVec hr1 (Matrix.of fun k s => w (f k) s)
      (fun k s => hβ8 _) uVec (by simp [uVec, hud]) ?_
    intro k
    have hsum_eq : ∑ s : Fin r, (w (f k) s : ℝ) * uVec s = v (f k) := by
      dsimp [w, uVec, v]
      refine Finset.sum_bij (fun (s : Fin r) _ => (d : ℤ) - (s.val : ℤ)) ?_ ?_ ?_ ?_
      · intro s _; simp only [Finset.mem_Icc]; omega
      · intro a _ b _ h; exact Fin.ext (by omega)
      · intro l hl
        simp only [Finset.mem_Icc] at hl
        refine ⟨⟨(d - l).toNat, by omega⟩, Finset.mem_univ _, by dsimp only; omega⟩
      · intro s _
        rw [mul_comm]
        congr 2; ring
    simpa only [Matrix.of_apply, hsum_eq] using hsmall (f k) (hf k)
  obtain ⟨c, hc_ne, hc_orth⟩ := exists_rational_annihilator hr1 (Finset.Icc A B) w hdet0
  -- Trim zero ends of c to [l0, u0]
  have hsupp_ne : (Finset.univ.filter (fun s : Fin r => c s ≠ 0)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hc_ne
    ext s
    have : s ∉ Finset.univ.filter (fun s : Fin r => c s ≠ 0) := by rw [hemp]; simp
    simpa using this
  let l0 : Fin r := (Finset.univ.filter (fun s : Fin r => c s ≠ 0)).min' hsupp_ne
  let u0 : Fin r := (Finset.univ.filter (fun s : Fin r => c s ≠ 0)).max' hsupp_ne
  have hl0_ne : c l0 ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hsupp_ne)).2
  have hu0_ne : c u0 ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem _ hsupp_ne)).2
  have hl0_le_u0 : l0.val ≤ u0.val := Fin.le_def.mp (Finset.min'_le _ u0 (Finset.max'_mem _ hsupp_ne))
  have hc_zero_out : ∀ s : Fin r, s.val < l0.val ∨ u0.val < s.val → c s = 0 := by
    intro s hs
    by_contra hne
    have hmem : s ∈ Finset.univ.filter (fun s : Fin r => c s ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    have h1 := Fin.le_def.mp (Finset.min'_le _ s hmem)
    have h2 := Fin.le_def.mp (Finset.le_max' _ s hmem)
    omega
  let h : ℕ := u0.val - l0.val
  have hhr : h ≤ r := by omega
  let cTrim : Fin (h + 1) → ℚ := fun t => c ⟨l0.val + t.val, by omega⟩
  have hcTrim_l : cTrim ⟨0, by omega⟩ ≠ 0 := by simpa [cTrim] using hl0_ne
  have hcTrim_u : cTrim ⟨h, by omega⟩ ≠ 0 := by
    have : (⟨l0.val + h, by omega⟩ : Fin r) = u0 := Fin.ext (by dsimp only; omega)
    simpa [cTrim, this] using hu0_ne
  have hrec_I : ∀ j ∈ Finset.Icc A B,
      ∑ t : Fin (h + 1), cTrim t * (β (j + (l0.val : ℤ) - (d : ℤ) + (t.val : ℤ)) : ℚ) = 0 := by
    intro j hj
    have h0 := hc_orth j hj
    rw [← h0]
    symm
    have hsub : ∑ s : Fin r, c s * (w j s : ℚ) =
        ∑ s ∈ Finset.univ.filter (fun s : Fin r => l0.val ≤ s.val ∧ s.val ≤ u0.val),
          c s * (w j s : ℚ) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun s _ hs => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rw [hc_zero_out s (by omega), zero_mul]
    rw [hsub]
    refine Finset.sum_bij (fun (s : Fin r) hs => ⟨s.val - l0.val, by
        have := (Finset.mem_filter.mp hs).2; omega⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hval := congrArg Fin.val hab
      dsimp only at hval
      exact Fin.ext (by omega)
    · intro t _
      refine ⟨⟨l0.val + t.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by dsimp only; omega, by dsimp only; omega⟩,
        Fin.ext (by dsimp only; omega)⟩
    · intro s hs
      have hs' := (Finset.mem_filter.mp hs).2
      dsimp only [cTrim, w]
      have h1 : (⟨l0.val + (s.val - l0.val), by omega⟩ : Fin r) = s := Fin.ext (by dsimp only; omega)
      rw [h1]
      congr 3; omega
  -- Case h = 0: β vanishes on [A + l0 - d, B + l0 - d]
  by_cases hh0 : h = 0
  · have hβ0 : ∀ j ∈ Finset.Icc (A + (d : ℤ)) (B - (d : ℤ)), β j = 0 := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      have hrec' := hrec_I (j + (d : ℤ) - (l0.val : ℤ)) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hsum1 : ∑ t : Fin (h + 1), cTrim t *
            (β (j + (d : ℤ) - (l0.val : ℤ) + (l0.val : ℤ) - (d : ℤ) + (t.val : ℤ)) : ℚ) =
          cTrim ⟨0, by omega⟩ * (β j : ℚ) := by
        rw [Finset.sum_eq_single ⟨0, by omega⟩]
        · congr 2; ring
        · intro t _ ht; exfalso; apply ht; exact Fin.ext (by omega)
        · intro hn; exact absurd (Finset.mem_univ _) hn
      rw [hsum1] at hrec'
      have hq0 : (β j : ℚ) = 0 := (mul_eq_zero.mp hrec').resolve_left hcTrim_l
      exact Int.cast_injective hq0
    have hv0 : ∀ j ∈ Finset.Icc (A + 2 * (d : ℤ)) (B - 2 * (d : ℤ)), v j = 0 := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      dsimp [v]
      refine Finset.sum_eq_zero fun l hl => ?_
      simp only [Finset.mem_Icc] at hl
      rw [hβ0 (j - l) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]; simp
    have hcard_out : ∀ (k : ℕ),
        ((Finset.Icc A B).filter (fun j => j < A + (k : ℤ) ∨ B - (k : ℤ) < j)).card ≤ 2 * k := by
      intro k
      have hsub : (Finset.Icc A B).filter (fun j => j < A + (k : ℤ) ∨ B - (k : ℤ) < j) ⊆
          Finset.Ico A (A + (k : ℤ)) ∪ Finset.Ioc (B - (k : ℤ)) B := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico,
          Finset.mem_Ioc] at hj ⊢
        rcases hj.2 with h1 | h2
        · exact Or.inl ⟨hj.1.1, h1⟩
        · exact Or.inr ⟨h2, hj.1.2⟩
      refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
      rw [Int.card_Ico, Int.card_Ioc]
      omega
    have hL4r : 4 * r ≤ L := by
      dsimp only [L]
      exact Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    have hleL1 : 2 * d ≤ L := by omega
    have hleL2 : 2 * (2 * d) ≤ L := by omega
    exact ⟨(Finset.card_le_card (s := (Finset.Icc A B).filter (fun j => β j ≠ 0))
      (t := (Finset.Icc A B).filter (fun j => j < A + (d : ℤ) ∨ B - (d : ℤ) < j)) fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
        refine ⟨hj.1, ?_⟩
        by_contra hnot; push Not at hnot
        exact hj.2 (hβ0 j (Finset.mem_Icc.mpr hnot))).trans ((hcard_out d).trans hleL1),
      (Finset.card_le_card (s := (Finset.Icc A B).filter (fun j => v j ≠ 0))
      (t := (Finset.Icc A B).filter (fun j => j < A + ((2 * d : ℕ) : ℤ) ∨ B - ((2 * d : ℕ) : ℤ) < j)) fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
        refine ⟨hj.1, ?_⟩
        by_contra hnot; push Not at hnot
        exact hj.2 (hv0 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))).trans ((hcard_out (2 * d)).trans hleL2)⟩
  -- Case h ≥ 1: Pigeonhole on states of length h in [-8, 8]^h
  have hh_pos : 1 ≤ h := by omega
  let state : ℤ → (Fin h → Fin 17) := fun j t =>
    ⟨(β (j + (l0.val : ℤ) - (d : ℤ) + (t.val : ℤ)) + 8).toNat, by
      have := hβ8 (j + (l0.val : ℤ) - (d : ℤ) + (t.val : ℤ))
      rw [abs_le] at this; omega⟩
  have hcard_big : Fintype.card (Fin h → Fin 17) < (Finset.Icc A B).card := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have hpow : 17 ^ h ≤ 17 ^ r := Nat.pow_le_pow_right (by norm_num) hhr
    omega
  obtain ⟨j₁, hj₁, j₂, hj₂, hne12, hst_eq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (f := state) (s := Finset.Icc A B) (t := Finset.univ)
    (by simpa [Fintype.card_fun] using hcard_big) (fun _ _ => Finset.mem_univ _)
  -- WLOG j₁ < j₂
  have hex_pair : ∃ a b : ℤ, a ∈ Finset.Icc A B ∧ b ∈ Finset.Icc A B ∧ a < b ∧ state a = state b := by
    rcases lt_or_gt_of_ne hne12 with hlt | hgt
    · exact ⟨j₁, j₂, hj₁, hj₂, hlt, hst_eq⟩
    · exact ⟨j₂, j₁, hj₂, hj₁, hgt, hst_eq.symm⟩
  obtain ⟨a, b, haI, hbI, hab, hst_ab⟩ := hex_pair
  have hβ_state_eq : ∀ t : Fin h,
      β (a + (l0.val : ℤ) - (d : ℤ) + (t.val : ℤ)) = β (b + (l0.val : ℤ) - (d : ℤ) + (t.val : ℤ)) := by
    intro t
    have h1 := congrArg Fin.val (congrFun hst_ab t)
    dsimp [state] at h1
    have h2 := hβ8 (a + (l0.val : ℤ) - (d : ℤ) + (t.val : ℤ))
    have h3 := hβ8 (b + (l0.val : ℤ) - (d : ℤ) + (t.val : ℤ))
    rw [abs_le] at h2 h3
    omega
  -- Define T₀ = (b - a).toNat and T₀-periodic sequence betaT
  let T₀ : ℕ := (b - a).toNat
  have hT0_pos : 0 < T₀ := by omega
  have hT0_eq : (T₀ : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  let base : ℤ := a + (l0.val : ℤ) - (d : ℤ)
  let betaT : ℤ → ℤ := fun k => β (base + (k - base) % (T₀ : ℤ))
  have hbetaT_per : ∀ k : ℤ, betaT (k + (T₀ : ℤ)) = betaT k := by
    intro k; dsimp [betaT]
    rw [show k + (T₀ : ℤ) - base = (k - base) + (T₀ : ℤ) by ring, Int.add_emod_right]
  have hbetaT_on_ab : ∀ k : ℤ, base ≤ k → k < base + (T₀ : ℤ) → betaT k = β k := by
    intro k hlo hhi
    dsimp [betaT]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    congr 1; ring
  -- Show betaT (base + k) = β (base + k) for all 0 ≤ k < T₀ + h by strong induction on k
  have hbetaT_block : ∀ k : ℕ, k < T₀ + h → betaT (base + (k : ℤ)) = β (base + (k : ℤ)) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      by_cases hkT : k < T₀
      · exact hbetaT_on_ab (base + (k : ℤ)) (by omega) (by omega)
      · have ht : k - T₀ < h := by omega
        have h1 := hβ_state_eq ⟨k - T₀, ht⟩
        have h2 : a + (l0.val : ℤ) - (d : ℤ) + ((k - T₀ : ℕ) : ℤ) = base + ((k - T₀ : ℕ) : ℤ) := rfl
        have h3 : b + (l0.val : ℤ) - (d : ℤ) + ((k - T₀ : ℕ) : ℤ) = base + (k : ℤ) := by
          dsimp [base]; omega
        rw [h2, h3] at h1
        rw [← h1, ← ih (k - T₀) (by omega) (by omega)]
        have h4 : base + (k : ℤ) = (base + ((k - T₀ : ℕ) : ℤ)) + (T₀ : ℤ) := by omega
        rw [h4, hbetaT_per]
  -- betaT satisfies the recurrence everywhere on ℤ
  have hbetaT_rec : ∀ j : ℤ, ∑ t : Fin (h + 1), cTrim t * (betaT (j + (t.val : ℤ)) : ℚ) = 0 := by
    intro j
    let r0 : ℕ := ((j - base) % (T₀ : ℤ)).toNat
    have hr0_lt : r0 < T₀ := by
      have h1 := Int.emod_nonneg (j - base) (Int.natCast_ne_zero.mpr hT0_pos.ne')
      have h2 := Int.emod_lt_of_pos (j - base) (Int.natCast_pos.mpr hT0_pos)
      omega
    have hr0_eq : (r0 : ℤ) = (j - base) % (T₀ : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg (j - base) (Int.natCast_ne_zero.mpr hT0_pos.ne'))
    have hper_mul : ∀ (x m : ℤ), betaT (x + m * (T₀ : ℤ)) = betaT x := by
      intro x m
      induction m using Int.induction_on with
      | zero => simp
      | succ n ih =>
        rw [show x + ((n : ℤ) + 1) * (T₀ : ℤ) = (x + (n : ℤ) * (T₀ : ℤ)) + (T₀ : ℤ) by ring,
          hbetaT_per, ih]
      | pred n ih =>
        have h1 := hbetaT_per (x + (-(n : ℤ) - 1) * (T₀ : ℤ))
        rw [show x + (-(n : ℤ) - 1) * (T₀ : ℤ) + (T₀ : ℤ) = x + (-(n : ℤ)) * (T₀ : ℤ) by ring] at h1
        exact h1.symm.trans ih
    have hj_shift : ∀ t : Fin (h + 1), betaT (j + (t.val : ℤ)) = betaT (base + ((r0 + t.val : ℕ) : ℤ)) := by
      intro t
      have hdiv := Int.mul_ediv_add_emod (j - base) (T₀ : ℤ)
      have hEq : j + (t.val : ℤ) = (base + ((r0 + t.val : ℕ) : ℤ)) + ((j - base) / (T₀ : ℤ)) * (T₀ : ℤ) := by
        push_cast; linarith [hr0_eq]
      rw [hEq, hper_mul]
    have haI' := Finset.mem_Icc.mp haI
    have hbI' := Finset.mem_Icc.mp hbI
    have hrec_a := hrec_I (a + (r0 : ℤ)) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [← hrec_a]
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 2
    rw [hj_shift t, hbetaT_block (r0 + t.val) (by omega)]
    congr 1; dsimp [base]; push_cast; ring
  -- Apply cyclotomic order bound: betaT is P-periodic!
  have hbetaT_P : ∀ j : ℤ, betaT (j + (P : ℤ)) = betaT j :=
    periodic_factorial_of_recurrence hT0_pos h hhr betaT hbetaT_per cTrim hcTrim_u hbetaT_rec
  -- Show β k = betaT k for all k ∈ [A + l0 - d, B + u0 - d]
  have hβ_eq_fwd : ∀ m : ℕ, base + (m : ℤ) ≤ B + (u0.val : ℤ) - (d : ℤ) →
      β (base + (m : ℤ)) = betaT (base + (m : ℤ)) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro hm
      by_cases hmh : m < h
      · exact (hbetaT_block m (by omega)).symm
      · let j0 : ℤ := a + ((m - h : ℕ) : ℤ)
        have haI' := Finset.mem_Icc.mp haI
        have hbI' := Finset.mem_Icc.mp hbI
        have hj0I : j0 ∈ Finset.Icc A B := by
          simp only [Finset.mem_Icc, j0]; dsimp [base] at hm; omega
        have h1 := hrec_I j0 hj0I
        have h2 := hbetaT_rec (base + ((m - h : ℕ) : ℤ))
        have hbase_j0 : j0 + (l0.val : ℤ) - (d : ℤ) = base + ((m - h : ℕ) : ℤ) := by
          dsimp [j0, base]; ring
        rw [hbase_j0] at h1
        have hsub : ∑ t : Fin (h + 1), cTrim t *
            ((β (base + ((m - h : ℕ) : ℤ) + (t.val : ℤ)) : ℚ) -
             (betaT (base + ((m - h : ℕ) : ℤ) + (t.val : ℤ)) : ℚ)) = 0 := by
          simp_rw [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_self]
        rw [Finset.sum_eq_single ⟨h, by omega⟩] at hsub
        · have hidx : base + ((m - h : ℕ) : ℤ) + (h : ℤ) = base + (m : ℤ) := by omega
          rw [hidx] at hsub
          have hdiff0 : (β (base + (m : ℤ)) : ℚ) - (betaT (base + (m : ℤ)) : ℚ) = 0 :=
            (mul_eq_zero.mp hsub).resolve_left hcTrim_u
          exact Int.cast_injective (sub_eq_zero.mp hdiff0)
        · intro t _ ht
          have hlt : t.val < h := by
            have := t.isLt
            have hne : t.val ≠ h := fun he => ht (Fin.ext he)
            omega
          have hidx : base + ((m - h : ℕ) : ℤ) + (t.val : ℤ) = base + ((m - h + t.val : ℕ) : ℤ) := by
            push_cast; ring
          rw [hidx, ih (m - h + t.val) (by omega) (by omega), sub_self, mul_zero]
        · intro hn; exact absurd (Finset.mem_univ _) hn
  have hβ_eq_bwd : ∀ m : ℕ, A + (l0.val : ℤ) - (d : ℤ) ≤ base - (m : ℤ) →
      β (base - (m : ℤ)) = betaT (base - (m : ℤ)) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro hm
      by_cases hm0 : m = 0
      · subst hm0; simpa using (hbetaT_block 0 (by omega)).symm
      · let j0 : ℤ := a - (m : ℤ)
        have haI' := Finset.mem_Icc.mp haI
        have hbI' := Finset.mem_Icc.mp hbI
        have hj0I : j0 ∈ Finset.Icc A B := by
          simp only [Finset.mem_Icc, j0]; dsimp [base] at hm; omega
        have h1 := hrec_I j0 hj0I
        have h2 := hbetaT_rec (base - (m : ℤ))
        have hbase_j0 : j0 + (l0.val : ℤ) - (d : ℤ) = base - (m : ℤ) := by
          dsimp [j0, base]; ring
        rw [hbase_j0] at h1
        have hsub : ∑ t : Fin (h + 1), cTrim t *
            ((β (base - (m : ℤ) + (t.val : ℤ)) : ℚ) -
             (betaT (base - (m : ℤ) + (t.val : ℤ)) : ℚ)) = 0 := by
          simp_rw [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_self]
        rw [Finset.sum_eq_single ⟨0, by omega⟩] at hsub
        · simp only [Nat.cast_zero, add_zero] at hsub
          have hdiff0 : (β (base - (m : ℤ)) : ℚ) - (betaT (base - (m : ℤ)) : ℚ) = 0 :=
            (mul_eq_zero.mp hsub).resolve_left hcTrim_l
          exact Int.cast_injective (sub_eq_zero.mp hdiff0)
        · intro t _ ht
          have htpos : 1 ≤ t.val := by
            have hne : t.val ≠ 0 := fun he => ht (Fin.ext he)
            omega
          by_cases htm : t.val ≤ m
          · have hidx : base - (m : ℤ) + (t.val : ℤ) = base - ((m - t.val : ℕ) : ℤ) := by omega
            rw [hidx, ih (m - t.val) (by omega) (by omega), sub_self, mul_zero]
          · have hidx : base - (m : ℤ) + (t.val : ℤ) = base + ((t.val - m : ℕ) : ℤ) := by omega
            have hleB : base + ((t.val - m : ℕ) : ℤ) ≤ B + (u0.val : ℤ) - (d : ℤ) := by
              dsimp [base]; omega
            rw [hidx, hβ_eq_fwd (t.val - m) hleB, sub_self, mul_zero]
        · intro hn; exact absurd (Finset.mem_univ _) hn
  have hβ_eq_mid : ∀ k ∈ Finset.Icc (A + (d : ℤ)) (B - (d : ℤ)), β k = betaT k := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    by_cases hkb : base ≤ k
    · have hk' : k = base + ((k - base).toNat : ℤ) := by omega
      rw [hk']
      exact hβ_eq_fwd (k - base).toNat (by omega)
    · have hk' : k = base - ((base - k).toNat : ℤ) := by omega
      rw [hk']
      exact hβ_eq_bwd (base - k).toNat (by omega)
  -- Telescoping kill: β j = 0 for all j ∈ [A + d, B - d - 8*P]
  have hβ_kill : ∀ j ∈ Finset.Icc (A + (d : ℤ)) (B - (d : ℤ) - 8 * (P : ℤ)), β j = 0 := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    let α : ℤ → ℤ := fun k => p k - p (k - (P : ℤ))
    have hα4 : ∀ k : ℤ, |α k| ≤ 4 := by
      intro k; dsimp [α]; rw [abs_le]
      have h1 := hp0 k; have h2 := hp4 k; have h3 := hp0 (k - P); have h4 := hp4 (k - P)
      constructor <;> omega
    have hβ_α : ∀ k : ℤ, β k = α (k + (P : ℤ)) - α k := by
      intro k; dsimp [β, α]; ring
    have hper_k : ∀ k : ℕ, betaT (j + (k : ℤ) * (P : ℤ)) = betaT j := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show j + ((k + 1 : ℕ) : ℤ) * (P : ℤ) = (j + (k : ℤ) * (P : ℤ)) + (P : ℤ) by push_cast; ring,
          hbetaT_P, ih]
    have hsum9 : (∑ k ∈ Finset.range 9, β (j + (k : ℤ) * (P : ℤ))) = 9 * β j := by
      have hterm : ∀ k ∈ Finset.range 9, β (j + (k : ℤ) * (P : ℤ)) = β j := by
        intro k hk
        have hk8 : k ≤ 8 := by have := Finset.mem_range.mp hk; omega
        rw [hβ_eq_mid (j + (k : ℤ) * (P : ℤ)) (Finset.mem_Icc.mpr ⟨by nlinarith, by nlinarith⟩),
          hper_k k, ← hβ_eq_mid j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      norm_num
    have htele : (∑ k ∈ Finset.range 9, β (j + (k : ℤ) * (P : ℤ))) = α (j + 9 * (P : ℤ)) - α j := by
      have hterm : ∀ k : ℕ, β (j + (k : ℤ) * (P : ℤ)) =
          α (j + ((k + 1 : ℕ) : ℤ) * (P : ℤ)) - α (j + (k : ℤ) * (P : ℤ)) := by
        intro k; rw [hβ_α]; congr 2; push_cast; ring
      simp_rw [hterm]
      simpa using Finset.sum_range_sub (fun k : ℕ => α (j + (k : ℤ) * (P : ℤ))) 9
    have h1 := hα4 (j + 9 * (P : ℤ))
    have h2 := hα4 j
    rw [abs_le] at h1 h2
    omega
  have hv_kill : ∀ j ∈ Finset.Icc (A + 2 * (d : ℤ)) (B - 2 * (d : ℤ) - 8 * (P : ℤ)), v j = 0 := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    dsimp [v]
    refine Finset.sum_eq_zero fun l hl => ?_
    simp only [Finset.mem_Icc] at hl
    rw [hβ_kill (j - l) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]; simp
  have hcard_out : ∀ (k₁ k₂ : ℕ),
      ((Finset.Icc A B).filter (fun j => j < A + (k₁ : ℤ) ∨ B - (k₂ : ℤ) < j)).card ≤ k₁ + k₂ := by
    intro k₁ k₂
    have hsub : (Finset.Icc A B).filter (fun j => j < A + (k₁ : ℤ) ∨ B - (k₂ : ℤ) < j) ⊆
        Finset.Ico A (A + (k₁ : ℤ)) ∪ Finset.Ioc (B - (k₂ : ℤ)) B := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico,
        Finset.mem_Ioc] at hj ⊢
      rcases hj.2 with h1 | h2
      · exact Or.inl ⟨hj.1.1, h1⟩
      · exact Or.inr ⟨h2, hj.1.2⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    rw [Int.card_Ico, Int.card_Ioc]
    omega
  have hL4r : 4 * r + 10 * P ≤ L := by
    dsimp only [L]
    exact Nat.le_trans (Nat.add_le_add_right (Nat.le_add_left _ _) _) (Nat.le_add_right _ _)
  have hleL1 : d + (d + 8 * P) ≤ L := by omega
  have hleL2 : 2 * d + (2 * d + 8 * P) ≤ L := by omega
  constructor
  · refine (Finset.card_le_card (s := (Finset.Icc A B).filter (fun j => β j ≠ 0))
      (t := (Finset.Icc A B).filter (fun j => j < A + (d : ℤ) ∨ B - ((d + 8 * P : ℕ) : ℤ) < j)) ?_).trans
      ((hcard_out d (d + 8 * P)).trans hleL1)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    refine ⟨hj.1, ?_⟩
    by_contra hnot
    push Not at hnot
    exact hj.2 (hβ_kill j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
  · refine (Finset.card_le_card (s := (Finset.Icc A B).filter (fun j => v j ≠ 0))
      (t := (Finset.Icc A B).filter (fun j => j < A + ((2 * d : ℕ) : ℤ) ∨ B - ((2 * d + 8 * P : ℕ) : ℤ) < j)) ?_).trans
      ((hcard_out (2 * d) (2 * d + 8 * P)).trans hleL2)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    refine ⟨hj.1, ?_⟩
    by_contra hnot
    push Not at hnot
    exact hj.2 (hv_kill j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))

/- ### Section 4: Harmonic Bound, Support Counting, Fejer Multiplier, and Abel Summation -/

lemma log_add_one_le_harmonic (N : ℕ) :
    Real.log ((N : ℝ) + 1) ≤ ∑ i ∈ Finset.range N, ((i : ℝ) + 1)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hstep : Real.log (((N + 1 : ℕ) : ℝ) + 1) - Real.log ((N : ℝ) + 1) ≤ ((N : ℝ) + 1)⁻¹ := by
      rw [← Real.log_div (by positivity) hpos.ne']
      have hdiv : (((N + 1 : ℕ) : ℝ) + 1) / ((N : ℝ) + 1) = 1 + ((N : ℝ) + 1)⁻¹ := by
        push_cast; field_simp [hpos.ne']
      rw [hdiv]
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + ((N : ℝ) + 1)⁻¹ by positivity)]
    linarith

/-- Partial sum of sin(j * x) for j ∈ Icc a b is bounded by 1 / sin(x / 2). -/
lemma abs_sum_sin_le (x : ℝ) (hx0 : 0 < x) (hxpi : x ≤ Real.pi) (a b : ℕ) :
    |∑ j ∈ Finset.Icc a b, Real.sin ((j : ℝ) * x)| ≤ (Real.sin (x / 2))⁻¹ := by
  have hsin_pos : 0 < Real.sin (x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [inv_eq_one_div, le_div_iff₀ hsin_pos]
  by_cases hab : a ≤ b
  · have hmul : (∑ j ∈ Finset.Icc a b, Real.sin ((j : ℝ) * x)) * Real.sin (x / 2) =
        (Real.cos (((a : ℝ) - 1 / 2) * x) - Real.cos (((b : ℝ) + 1 / 2) * x)) / 2 := by
      rw [Finset.sum_mul]
      have hterm : ∀ j : ℕ, Real.sin ((j : ℝ) * x) * Real.sin (x / 2) =
          (Real.cos (((j : ℝ) - 1 / 2) * x) - Real.cos ((((j + 1 : ℕ) : ℝ) - 1 / 2) * x)) / 2 := by
        intro j
        have h1 : (((j + 1 : ℕ) : ℝ) - 1 / 2) * x = (j : ℝ) * x + x / 2 := by push_cast; ring
        have h2 : ((j : ℝ) - 1 / 2) * x = (j : ℝ) * x - x / 2 := by ring
        rw [h1, h2, Real.cos_sub, Real.cos_add]
        ring
      simp_rw [hterm]
      have hshift : ∑ j ∈ Finset.Icc a b,
          (Real.cos (((j : ℝ) - 1 / 2) * x) - Real.cos ((((j + 1 : ℕ) : ℝ) - 1 / 2) * x)) / 2 =
          ∑ k ∈ Finset.range (b + 1 - a),
            (Real.cos ((((a + k : ℕ) : ℝ) - 1 / 2) * x) -
              Real.cos ((((a + k + 1 : ℕ) : ℝ) - 1 / 2) * x)) / 2 := by
        refine Finset.sum_nbij (fun j => j - a) ?_ ?_ ?_ ?_
        · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
        · intro j₁ hj₁ j₂ hj₂ h
          simp only [Finset.mem_coe, Finset.mem_Icc] at hj₁ hj₂
          dsimp only at h; omega
        · intro k hk
          simp only [Finset.mem_coe, Finset.mem_range] at hk
          exact ⟨a + k, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩),
            by dsimp only; omega⟩
        · intro j hj
          simp only [Finset.mem_Icc] at hj
          have : a + (j - a) = j := by omega
          rw [this]
      rw [hshift]
      have htele := Finset.sum_range_sub'
        (fun k : ℕ => Real.cos ((((a + k : ℕ) : ℝ) - 1 / 2) * x) / 2) (b + 1 - a)
      have hsub : ∑ k ∈ Finset.range (b + 1 - a),
          (Real.cos ((((a + k : ℕ) : ℝ) - 1 / 2) * x) -
            Real.cos ((((a + k + 1 : ℕ) : ℝ) - 1 / 2) * x)) / 2 =
          ∑ k ∈ Finset.range (b + 1 - a),
            (Real.cos ((((a + k : ℕ) : ℝ) - 1 / 2) * x) / 2 -
              Real.cos ((((a + (k + 1) : ℕ) : ℝ) - 1 / 2) * x) / 2) := by
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hsub, htele]
      have hba : a + (b + 1 - a) = b + 1 := by omega
      rw [hba, Nat.add_zero]
      push_cast; ring
    have habs : |∑ j ∈ Finset.Icc a b, Real.sin ((j : ℝ) * x)| * Real.sin (x / 2) =
        |(∑ j ∈ Finset.Icc a b, Real.sin ((j : ℝ) * x)) * Real.sin (x / 2)| := by
      rw [abs_mul, abs_of_pos hsin_pos]
    rw [habs, hmul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h1 := Real.abs_cos_le_one (((a : ℝ) - 1 / 2) * x)
    have h2 := Real.abs_cos_le_one (((b : ℝ) + 1 / 2) * x)
    have h3 : |Real.cos (((a : ℝ) - 1 / 2) * x) - Real.cos (((b : ℝ) + 1 / 2) * x)| ≤ 2 := by
      calc |Real.cos _ - Real.cos _|
          ≤ |Real.cos _| + |Real.cos _| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add h1 h2
        _ = 2 := by norm_num
    linarith
  · rw [Finset.Icc_eq_empty hab, Finset.sum_empty, abs_zero, zero_mul]
    norm_num

/-- Abel summation bound: for 0 < x ≤ pi and 1 ≤ a ≤ b, |∑_{j=a}^b sin(j*x)/j| ≤ pi / (a * x). -/
lemma abs_sum_sin_div_le (x : ℝ) (hx0 : 0 < x) (hxpi : x ≤ Real.pi) {a b : ℕ} (ha : 1 ≤ a) :
    |∑ j ∈ Finset.Icc a b, Real.sin ((j : ℝ) * x) / (j : ℝ)| ≤ Real.pi / ((a : ℝ) * x) := by
  have hsin_lower : x / Real.pi ≤ Real.sin (x / 2) := by
    have h := Real.mul_le_sin (by linarith : (0 : ℝ) ≤ x / 2) (by linarith : x / 2 ≤ Real.pi / 2)
    have heq : 2 / Real.pi * (x / 2) = x / Real.pi := by ring
    linarith
  have hsin_pos : 0 < Real.sin (x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hinv_le : (Real.sin (x / 2))⁻¹ ≤ Real.pi / x := by
    rw [inv_le_iff_one_le_mul₀ hsin_pos]
    have hpi : 0 < Real.pi := Real.pi_pos
    have : Real.pi / x * (x / Real.pi) = 1 := by field_simp [hx0.ne', hpi.ne']
    nlinarith [show (0 : ℝ) ≤ Real.pi / x by positivity]
  by_cases hab : a ≤ b
  · let S : ℕ → ℝ := fun k => ∑ j ∈ Finset.Icc a k, Real.sin ((j : ℝ) * x)
    have hS_bound : ∀ k, |S k| ≤ (Real.sin (x / 2))⁻¹ := fun k => abs_sum_sin_le x hx0 hxpi a k
    -- Summation by parts: ∑_{j=a}^b (S j - S (j-1)) / j = S b / b + ∑_{j=a}^{b-1} S j * (1/j - 1/(j+1))
    have hparts : ∑ j ∈ Finset.Icc a b, Real.sin ((j : ℝ) * x) / (j : ℝ) =
        S b / (b : ℝ) + ∑ j ∈ Finset.Ico a b, S j * (((j : ℝ))⁻¹ - ((j + 1 : ℕ) : ℝ)⁻¹) := by
      induction b, hab using Nat.le_induction with
      | base =>
        simp [S]
      | succ k hk ih =>
        rw [Finset.sum_Icc_succ_top (by omega : a ≤ k + 1), ih,
          Finset.sum_Ico_succ_top hk]
        have hSk : S (k + 1) = S k + Real.sin (((k + 1 : ℕ) : ℝ) * x) := by
          dsimp [S]; rw [Finset.sum_Icc_succ_top (by omega : a ≤ k + 1)]
        rw [hSk]
        ring
    rw [hparts]
    have h1 : |S b / (b : ℝ) + ∑ j ∈ Finset.Ico a b, S j * (((j : ℝ))⁻¹ - ((j + 1 : ℕ) : ℝ)⁻¹)| ≤
        |S b| / (b : ℝ) + ∑ j ∈ Finset.Ico a b, |S j| * (((j : ℝ))⁻¹ - ((j + 1 : ℕ) : ℝ)⁻¹) := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_of_pos (show (0 : ℝ) < (b : ℝ) by exact_mod_cast (by omega : 0 < b))]
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        have hjpos : 1 ≤ j := by have := (Finset.mem_Ico.mp hj).1; omega
        have hle : ((j : ℝ)) ≤ ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
        have hpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
        have hdiff_nn : 0 ≤ ((j : ℝ))⁻¹ - ((j + 1 : ℕ) : ℝ)⁻¹ := by linarith [inv_anti₀ hpos hle]
        rw [abs_mul, abs_of_nonneg hdiff_nn]
    have h2 : |S b| / (b : ℝ) + ∑ j ∈ Finset.Ico a b, |S j| * (((j : ℝ))⁻¹ - ((j + 1 : ℕ) : ℝ)⁻¹) ≤
        (Real.sin (x / 2))⁻¹ * (((b : ℝ))⁻¹ + ∑ j ∈ Finset.Ico a b, (((j : ℝ))⁻¹ - ((j + 1 : ℕ) : ℝ)⁻¹)) := by
      rw [mul_add, Finset.mul_sum]
      refine add_le_add ?_ (Finset.sum_le_sum fun j hj => ?_)
      · rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (hS_bound b) (by positivity)
      · have hjpos : 1 ≤ j := by have := (Finset.mem_Ico.mp hj).1; omega
        have hdiff_nn : 0 ≤ ((j : ℝ))⁻¹ - ((j + 1 : ℕ) : ℝ)⁻¹ := by
          have hpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
          have hle : ((j : ℝ)) ≤ ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
          linarith [inv_anti₀ hpos hle]
        exact mul_le_mul_of_nonneg_right (hS_bound j) hdiff_nn
    have htele : ((b : ℝ))⁻¹ + ∑ j ∈ Finset.Ico a b, (((j : ℝ))⁻¹ - ((j + 1 : ℕ) : ℝ)⁻¹) = ((a : ℝ))⁻¹ := by
      clear hparts h1 h2
      induction b, hab using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        rw [Finset.sum_Ico_succ_top hk]
        linarith
    rw [htele] at h2
    calc |S b / (b : ℝ) + ∑ j ∈ Finset.Ico a b, S j * (((j : ℝ))⁻¹ - ((j + 1 : ℕ) : ℝ)⁻¹)|
        ≤ (Real.sin (x / 2))⁻¹ * ((a : ℝ))⁻¹ := h1.trans h2
      _ ≤ (Real.pi / x) * ((a : ℝ))⁻¹ := mul_le_mul_of_nonneg_right hinv_le (by positivity)
      _ = Real.pi / ((a : ℝ) * x) := by ring
  · rw [Finset.Icc_eq_empty hab, Finset.sum_empty, abs_zero]
    positivity

/-- Harmonic sum over an interval Icc a b with 1 ≤ a ≤ b is at most 1 + log (b / a). -/
lemma sum_inv_Icc_le_one_add_log {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Finset.Icc a b, ((j : ℝ))⁻¹ ≤ 1 + Real.log ((b : ℝ) / (a : ℝ)) := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton]
    have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    rw [div_self (by linarith), Real.log_one, add_zero]
    exact inv_le_one_of_one_le₀ haR
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega : a ≤ k + 1)]
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    have hstep : (((k + 1 : ℕ) : ℝ))⁻¹ ≤
        Real.log (((k + 1 : ℕ) : ℝ) / (a : ℝ)) - Real.log ((k : ℝ) / (a : ℝ)) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have hdiv : (((k + 1 : ℕ) : ℝ) / (a : ℝ)) / ((k : ℝ) / (a : ℝ)) =
          ((k + 1 : ℕ) : ℝ) / (k : ℝ) := by field_simp [hapos.ne', hkpos.ne']
      rw [hdiv]
      -- 1 / (k+1) ≤ log ((k+1)/k) ↔ -log(k/(k+1)) ≥ 1/(k+1) ↔ log(k/(k+1)) ≤ -1/(k+1)
      have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k : ℝ) / ((k + 1 : ℕ) : ℝ) by positivity)
      have hneg : Real.log ((k : ℝ) / ((k + 1 : ℕ) : ℝ)) = -Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
        rw [Real.log_div hkpos.ne' (by positivity), Real.log_div (by positivity) hkpos.ne']; ring
      have hsub : (k : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = -(((k + 1 : ℕ) : ℝ))⁻¹ := by
        have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        push_cast at hk1 ⊢; field_simp [hk1]; ring
      rw [hneg, hsub] at hlog
      linarith
    linarith

/-- Splitting a finite interval Icc 1 N at jumps of a function h : ℤ → ℝ with 0 ≤ h j ≤ 4.
If at most K - 1 jumps occur, then ∑_{j=1}^N h j * sin(j*x)/j is bounded by 4 * (2 + log K + pi). -/
lemma piecewise_const_sine_sum_bound (N K : ℕ) (hK : 1 ≤ K) (h : ℤ → ℝ)
    (h0 : ∀ j, 0 ≤ h j) (h4 : ∀ j, h j ≤ 4)
    (hjumps : ((Finset.Icc (2 : ℕ) N).filter (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ))).card + 1 ≤ K)
    (x : ℝ) (hx0 : 0 < x) (hxpi : x ≤ Real.pi) :
    |∑ j ∈ Finset.Icc (1 : ℕ) N, h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ))| ≤
      4 * (2 + Real.log (K : ℝ) + Real.pi) := by
  classical
  let A1 : ℕ := ⌊1 / x⌋₊
  let A2 : ℕ := ⌊(K : ℝ) / x⌋₊
  have hA12 : A1 ≤ A2 := by
    apply Nat.floor_mono
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    exact div_le_div_of_nonneg_right hK1 hx0.le
  -- Partition Icc 1 N into S1 (≤ A1), S2 (A1 < j ≤ A2), S3 (A2 < j)
  let S1 := (Finset.Icc (1 : ℕ) N).filter (fun j => j ≤ A1)
  let S2 := (Finset.Icc (1 : ℕ) N).filter (fun j => A1 < j ∧ j ≤ A2)
  let S3 := (Finset.Icc (1 : ℕ) N).filter (fun j => A2 < j)
  have hpart : Finset.Icc (1 : ℕ) N = S1 ∪ (S2 ∪ S3) := by
    ext j; simp only [Finset.mem_union, Finset.mem_filter, S1, S2, S3]
    constructor
    · intro hj
      by_cases h1 : j ≤ A1
      · exact Or.inl ⟨hj, h1⟩
      · by_cases h2 : j ≤ A2
        · exact Or.inr (Or.inl ⟨hj, by omega, h2⟩)
        · exact Or.inr (Or.inr ⟨hj, by omega⟩)
    · rintro (⟨hj, _⟩ | ⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
  have hd1 : Disjoint S1 (S2 ∪ S3) := by
    rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_union, S1, S2, S3] at h1 h2; omega
  have hd2 : Disjoint S2 S3 := by
    rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_filter, S2, S3] at h1 h2; omega
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2]
  -- Bound S1: each term has |h j * sin(j*x)/j| ≤ 4 * x, and S1.card ≤ A1 ≤ 1/x
  have hS1 : |∑ j ∈ S1, h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ))| ≤ 4 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j ∈ S1, |h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ))| ≤ 4 * x := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
      have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
      rw [abs_mul, abs_div, abs_of_nonneg (h0 _), abs_of_pos hjpos]
      have hsin : |Real.sin ((j : ℝ) * x)| ≤ (j : ℝ) * x := by
        calc |Real.sin ((j : ℝ) * x)| ≤ |(j : ℝ) * x| := Real.abs_sin_le_abs
          _ = (j : ℝ) * x := abs_of_pos (mul_pos hjpos hx0)
      have hdiv : |Real.sin ((j : ℝ) * x)| / (j : ℝ) ≤ x :=
        (div_le_iff₀ hjpos).mpr (by linarith)
      exact mul_le_mul (h4 _) hdiv (by positivity) (by norm_num)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : S1.card ≤ A1 := by
      have hsub : S1 ⊆ Finset.Icc 1 A1 := fun j hj => by
        simp only [S1, Finset.mem_filter, Finset.mem_Icc] at hj ⊢; omega
      exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc]; omega)
    have hA1_le : (A1 : ℝ) ≤ 1 / x := Nat.floor_le (by positivity)
    have hcardR : (S1.card : ℝ) ≤ 1 / x := (by exact_mod_cast hcard : (S1.card : ℝ) ≤ A1).trans hA1_le
    calc (S1.card : ℝ) * (4 * x) ≤ (1 / x) * (4 * x) :=
          mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = 4 := by field_simp [hx0.ne']
  -- Bound S2: ∑_{j ∈ S2} 1/j ≤ 1 + log K
  have hS2 : |∑ j ∈ S2, h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ))| ≤
      4 * (1 + Real.log (K : ℝ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j ∈ S2, |h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ))| ≤ 4 * ((j : ℝ))⁻¹ := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
      have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
      rw [abs_mul, abs_div, abs_of_nonneg (h0 _), abs_of_pos hjpos, div_eq_mul_inv]
      have h1 : |Real.sin ((j : ℝ) * x)| * ((j : ℝ))⁻¹ ≤ ((j : ℝ))⁻¹ := by
        nlinarith [Real.abs_sin_le_one ((j : ℝ) * x), show (0 : ℝ) ≤ ((j : ℝ))⁻¹ by positivity]
      exact mul_le_mul (h4 _) h1 (by positivity) (by norm_num)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    by_cases hS2e : S2 = ∅
    · rw [hS2e, Finset.sum_empty]
      have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      linarith [Real.log_nonneg hK1]
    · have hsub : S2 ⊆ Finset.Icc (A1 + 1) A2 := fun j hj => by
        simp only [S2, Finset.mem_filter, Finset.mem_Icc] at hj ⊢; omega
      have hne : (Finset.Icc (A1 + 1) A2).Nonempty :=
        (Finset.nonempty_iff_ne_empty.mpr hS2e).mono hsub
      have hle12 : A1 + 1 ≤ A2 := by
        obtain ⟨j, hj⟩ := hne; simp only [Finset.mem_Icc] at hj; omega
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans ?_
      refine (sum_inv_Icc_le_one_add_log (by omega) hle12).trans ?_
      have hratio : (A2 : ℝ) / ((A1 + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
        have hA2_le : (A2 : ℝ) ≤ (K : ℝ) / x := Nat.floor_le (by positivity)
        have hA1_gt : 1 / x < ((A1 + 1 : ℕ) : ℝ) := by
          push_cast; exact Nat.lt_floor_add_one (1 / x)
        rw [div_le_iff₀ (by positivity)]
        calc (A2 : ℝ) ≤ (K : ℝ) / x := hA2_le
          _ = (K : ℝ) * (1 / x) := by ring
          _ ≤ (K : ℝ) * ((A1 + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hA1_gt.le (by positivity)
      have hA2_pos : 0 < (A2 : ℝ) := by exact_mod_cast (by omega : 0 < A2)
      linarith [Real.log_le_log (by positivity) hratio]
  -- Bound S3: split Icc (A2 + 1) N at jumps into ≤ K constant blocks
  have hS3 : |∑ j ∈ S3, h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ))| ≤ 4 * Real.pi := by
    have hS3_eq : S3 = Finset.Icc (A2 + 1) N := by
      ext j; simp only [S3, Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hS3_eq]
    -- Induct on the number of jumps in Icc (a + 1) b!
    have hblocks : ∀ (J : ℕ) (a b : ℕ), A2 + 1 ≤ a →
        ((Finset.Icc (a + 1) b).filter (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ))).card ≤ J →
        |∑ j ∈ Finset.Icc a b, h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ))| ≤
          ((J : ℝ) + 1) * (4 * Real.pi / (K : ℝ)) := by
      intro J
      induction J with
      | zero =>
        intro a b ha hcard0
        by_cases hab : a ≤ b
        · have hconst : ∀ j ∈ Finset.Icc a b, h (j : ℤ) = h (a : ℤ) := by
            intro j hj
            simp only [Finset.mem_Icc] at hj
            obtain ⟨hj1, hj2⟩ := hj
            induction j, hj1 using Nat.le_induction with
            | base => rfl
            | succ t ht ih =>
              have hne : ¬ h ((t + 1 : ℕ) : ℤ) ≠ h (t : ℤ) := by
                intro hdiff
                have hmem : t + 1 ∈ (Finset.Icc (a + 1) b).filter
                    (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ)) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hj2⟩, by simpa using hdiff⟩
                have hpos : 0 < ((Finset.Icc (a + 1) b).filter
                    (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ))).card :=
                  Finset.card_pos.mpr ⟨t + 1, hmem⟩
                omega
              push Not at hne
              rw [hne, ih (by omega)]
          have hsum_eq : ∑ j ∈ Finset.Icc a b, h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ)) =
              h (a : ℤ) * ∑ j ∈ Finset.Icc a b, Real.sin ((j : ℝ) * x) / (j : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j hj => by rw [hconst j hj]
          rw [hsum_eq, abs_mul, abs_of_nonneg (h0 _)]
          have habel := abs_sum_sin_div_le x hx0 hxpi (by omega : 1 ≤ a) (b := b)
          have hax : (K : ℝ) < (a : ℝ) * x := by
            have hA2_gt : (K : ℝ) / x < ((A2 + 1 : ℕ) : ℝ) := by
              push_cast; exact Nat.lt_floor_add_one ((K : ℝ) / x)
            have ha_ge : ((A2 + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
            have := (div_lt_iff₀ hx0).mp (lt_of_lt_of_le hA2_gt ha_ge)
            linarith
          have hpi_le : Real.pi / ((a : ℝ) * x) ≤ Real.pi / (K : ℝ) :=
            div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hax.le
          have h1 : h (a : ℤ) * |∑ j ∈ Finset.Icc a b, Real.sin ((j : ℝ) * x) / (j : ℝ)| ≤
              4 * (Real.pi / (K : ℝ)) :=
            mul_le_mul (h4 _) (habel.trans hpi_le) (abs_nonneg _) (by norm_num)
          simpa [mul_div_assoc] using h1
        · rw [Finset.Icc_eq_empty hab, Finset.sum_empty, abs_zero]
          positivity
      | succ J ih =>
        intro a b ha hcard
        let Jset := (Finset.Icc (a + 1) b).filter (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ))
        by_cases hJe : Jset = ∅
        · have h0' : Jset.card ≤ J := by rw [hJe, Finset.card_empty]; omega
          refine (ih a b ha h0').trans ?_
          have hnn : 0 ≤ 4 * Real.pi / (K : ℝ) := by positivity
          push_cast; nlinarith
        · have hJne : Jset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJe
          let c := Jset.min' hJne
          have hc_mem : c ∈ Jset := Finset.min'_mem Jset hJne
          have hc_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hc_mem).1
          have hsplit : Finset.Icc a b = Finset.Icc a (c - 1) ∪ Finset.Icc c b := by
            ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
          have hdisj : Disjoint (Finset.Icc a (c - 1)) (Finset.Icc c b) := by
            rw [Finset.disjoint_left]; intro j h1 h2
            simp only [Finset.mem_Icc] at h1 h2; omega
          rw [hsplit, Finset.sum_union hdisj]
          -- Left piece [a, c-1] has 0 jumps
          have hleft_0 : ((Finset.Icc (a + 1) (c - 1)).filter
              (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ))).card ≤ 0 := by
            rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro j hj hdiff
            simp only [Finset.mem_Icc] at hj
            have hmem : j ∈ Jset := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj.1, by omega⟩, hdiff⟩
            have hle := Finset.min'_le Jset j hmem
            omega
          -- Right piece [c, b] has ≤ J jumps (since c ∉ Icc (c+1) b)
          have hright_J : ((Finset.Icc (c + 1) b).filter
              (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ))).card ≤ J := by
            have hsub : (Finset.Icc (c + 1) b).filter
                (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ)) ⊆ Jset.erase c := by
              intro j hj
              simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase, Jset] at hj ⊢
              exact ⟨by omega, ⟨by omega, hj.1.2⟩, hj.2⟩
            have h1 := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem hc_mem] at h1
            have hJle : Jset.card ≤ J + 1 := hcard
            omega
          -- Use base case (J = 0) on left piece via induction? Even easier: prove base directly or via ih!
          -- Wait: we have `ih` for J, not for 0, so let's use a helper or prove hleft_bound directly!
          have hleft_bound : |∑ j ∈ Finset.Icc a (c - 1), h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ))| ≤
              4 * Real.pi / (K : ℝ) := by
            have hconst : ∀ j ∈ Finset.Icc a (c - 1), h (j : ℤ) = h (a : ℤ) := by
              intro j hj
              simp only [Finset.mem_Icc] at hj
              obtain ⟨hj1, hj2⟩ := hj
              induction j, hj1 using Nat.le_induction with
              | base => rfl
              | succ t ht ih' =>
                have hne : ¬ h ((t + 1 : ℕ) : ℤ) ≠ h (t : ℤ) := by
                  intro hdiff
                  have hmem : t + 1 ∈ (Finset.Icc (a + 1) (c - 1)).filter
                      (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ)) :=
                    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hj2⟩, by simpa using hdiff⟩
                  have hpos : 0 < ((Finset.Icc (a + 1) (c - 1)).filter
                      (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ))).card :=
                    Finset.card_pos.mpr ⟨t + 1, hmem⟩
                  omega
                push Not at hne
                rw [hne, ih' (by omega)]
            have hsum_eq : ∑ j ∈ Finset.Icc a (c - 1), h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ)) =
                h (a : ℤ) * ∑ j ∈ Finset.Icc a (c - 1), Real.sin ((j : ℝ) * x) / (j : ℝ) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j hj => by rw [hconst j hj]
            rw [hsum_eq, abs_mul, abs_of_nonneg (h0 _)]
            have habel := abs_sum_sin_div_le x hx0 hxpi (by omega : 1 ≤ a) (b := c - 1)
            have hax : (K : ℝ) < (a : ℝ) * x := by
              have hA2_gt : (K : ℝ) / x < ((A2 + 1 : ℕ) : ℝ) := by
                push_cast; exact Nat.lt_floor_add_one ((K : ℝ) / x)
              have ha_ge : ((A2 + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
              have := (div_lt_iff₀ hx0).mp (lt_of_lt_of_le hA2_gt ha_ge)
              linarith
            have hpi_le : Real.pi / ((a : ℝ) * x) ≤ Real.pi / (K : ℝ) :=
              div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hax.le
            have h1 : h (a : ℤ) * |∑ j ∈ Finset.Icc a (c - 1), Real.sin ((j : ℝ) * x) / (j : ℝ)| ≤
                4 * (Real.pi / (K : ℝ)) :=
              mul_le_mul (h4 _) (habel.trans hpi_le) (abs_nonneg _) (by norm_num)
            simpa [mul_div_assoc] using h1
          have hright_bound := ih c b (by omega) hright_J
          refine (abs_add_le _ _).trans ?_
          push_cast; linarith
    have hjumps_S3 : ((Finset.Icc (A2 + 1 + 1) N).filter
        (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ))).card ≤ K - 1 := by
      have hsub : (Finset.Icc (A2 + 1 + 1) N).filter
          (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ)) ⊆
          (Finset.Icc 2 N).filter (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ)) := by
        intro j hj; simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢; exact ⟨⟨by omega, hj.1.2⟩, hj.2⟩
      have := Finset.card_le_card hsub
      omega
    have hb := hblocks (K - 1) (A2 + 1) N le_rfl hjumps_S3
    have hKcast : (((K - 1 : ℕ) : ℝ) + 1) = (K : ℝ) := by exact_mod_cast (by omega : K - 1 + 1 = K)
    rw [hKcast] at hb
    have hKpos : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
    have hsimp : (K : ℝ) * (4 * Real.pi / (K : ℝ)) = 4 * Real.pi := by field_simp [hKpos]
    linarith
  calc |∑ j ∈ S1, h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ)) +
        (∑ j ∈ S2, h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ)) +
         ∑ j ∈ S3, h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ)))|
      ≤ |∑ j ∈ S1, _| + |∑ j ∈ S2, _ + ∑ j ∈ S3, _| := abs_add_le _ _
    _ ≤ |∑ j ∈ S1, _| + (|∑ j ∈ S2, _| + |∑ j ∈ S3, _|) := add_le_add_right (abs_add_le _ _) _
    _ ≤ 4 + (4 * (1 + Real.log (K : ℝ)) + 4 * Real.pi) := add_le_add hS1 (add_le_add hS2 hS3)
    _ = 4 * (2 + Real.log (K : ℝ) + Real.pi) := by ring

/-- Counting jumps of h from its second difference β_j / P^2:
if 0 ≤ h j ≤ 4, h(j-1) - 2 h(j) + h(j+1) = β_j / P^2, and P^2 * (h j - h (j-1)) ∈ ℤ,
then at most 4 * P^2 * (m + 1) indices j ∈ Icc 2 N have h j ≠ h (j - 1),
where m = #{j ∈ Icc 1 N | β j ≠ 0}. -/
lemma jumps_le_of_second_diff (N P : ℕ) (hP : 1 ≤ P) (h : ℤ → ℝ) (β : ℤ → ℤ)
    (h0 : ∀ j, 0 ≤ h j) (h4 : ∀ j, h j ≤ 4)
    (hdiff2 : ∀ j : ℤ, h (j - 1) - 2 * h j + h (j + 1) = (β j : ℝ) / ((P : ℝ) ^ 2))
    (hint : ∀ j : ℤ, ∃ z : ℤ, h j = (z : ℝ) / ((P : ℝ) ^ 2)) :
    let m := ((Finset.Icc (1 : ℕ) N).filter (fun j : ℕ => β (j : ℤ) ≠ 0)).card
    ((Finset.Icc (2 : ℕ) N).filter (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ))).card ≤
      4 * P ^ 2 * (m + 1) := by
  classical
  have hbase : ∀ (a b : ℕ), 2 ≤ a →
      ((Finset.Icc a (b - 1)).filter (fun j : ℕ => β (j : ℤ) ≠ 0)).card ≤ 0 →
      ((Finset.Icc a b).filter (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ))).card ≤ 4 * P ^ 2 := by
    intro a b ha hcard0
    by_cases hab : a ≤ b
    · have hd_const : ∀ j ∈ Finset.Icc a b,
          h (j : ℤ) - h ((j - 1 : ℕ) : ℤ) = h (a : ℤ) - h ((a - 1 : ℕ) : ℤ) := by
        intro j hj
        simp only [Finset.mem_Icc] at hj
        obtain ⟨hj1, hj2⟩ := hj
        induction j, hj1 using Nat.le_induction with
        | base => rfl
        | succ t ht ih =>
          have hβt : β (t : ℤ) = 0 := by
            by_contra hne
            have hmem : t ∈ (Finset.Icc a (b - 1)).filter (fun j : ℕ => β (j : ℤ) ≠ 0) :=
              Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ht, by omega⟩, hne⟩
            have hpos : 0 < ((Finset.Icc a (b - 1)).filter (fun j : ℕ => β (j : ℤ) ≠ 0)).card :=
              Finset.card_pos.mpr ⟨t, hmem⟩
            omega
          have h2 := hdiff2 (t : ℤ)
          rw [hβt, Int.cast_zero, zero_div] at h2
          have hcast1 : ((t + 1 : ℕ) : ℤ) = (t : ℤ) + 1 := by push_cast; ring
          have hcast2 : ((t - 1 : ℕ) : ℤ) = (t : ℤ) - 1 := by omega
          have hcast3 : ((t + 1 - 1 : ℕ) : ℤ) = (t : ℤ) := by omega
          rw [hcast1, hcast3, ← ih (by omega), hcast2]
          linarith
      by_cases hc0 : h (a : ℤ) - h ((a - 1 : ℕ) : ℤ) = 0
      · have hemp : (Finset.Icc a b).filter (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro j hj
          have := hd_const j hj
          push Not; linarith
        rw [hemp, Finset.card_empty]; omega
      · obtain ⟨z1, hz1⟩ := hint (a : ℤ)
        obtain ⟨z0, hz0⟩ := hint ((a - 1 : ℕ) : ℤ)
        have hP2_pos : (0 : ℝ) < (P : ℝ) ^ 2 := by positivity
        have hz_ne : z1 - z0 ≠ 0 := by
          intro hzeq
          apply hc0
          rw [hz1, hz0, ← sub_div, show (z1 : ℝ) - (z0 : ℝ) = ((z1 - z0 : ℤ) : ℝ) by push_cast; ring,
            hzeq, Int.cast_zero, zero_div]
        have hc_ge : ((P : ℝ) ^ 2)⁻¹ ≤ |h (a : ℤ) - h ((a - 1 : ℕ) : ℤ)| := by
          rw [hz1, hz0, ← sub_div, abs_div, abs_of_pos hP2_pos, inv_eq_one_div]
          refine div_le_div_of_nonneg_right ?_ hP2_pos.le
          have : (1 : ℤ) ≤ |z1 - z0| := Int.one_le_abs hz_ne
          exact_mod_cast this
        have htele : h (b : ℤ) - h ((a - 1 : ℕ) : ℤ) =
            ((b - a + 1 : ℕ) : ℝ) * (h (a : ℤ) - h ((a - 1 : ℕ) : ℤ)) := by
          have hsum : ∑ j ∈ Finset.Icc a b, (h (j : ℤ) - h ((j - 1 : ℕ) : ℤ)) =
              h (b : ℤ) - h ((a - 1 : ℕ) : ℤ) := by
            clear hd_const hcard0
            induction b, hab using Nat.le_induction with
            | base => simp
            | succ t ht ih =>
              rw [Finset.sum_Icc_succ_top (by omega : a ≤ t + 1), ih]
              have : ((t + 1 - 1 : ℕ) : ℤ) = (t : ℤ) := by omega
              rw [this]; ring
          rw [← hsum, Finset.sum_congr rfl hd_const, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          congr 1; exact_mod_cast (by omega : b + 1 - a = b - a + 1)
        have habs_le4 : |h (b : ℤ) - h ((a - 1 : ℕ) : ℤ)| ≤ 4 := by
          rw [abs_le]; constructor <;> linarith [h0 (b : ℤ), h4 (b : ℤ), h0 ((a - 1 : ℕ) : ℤ), h4 ((a - 1 : ℕ) : ℤ)]
        rw [htele, abs_mul, abs_of_nonneg (by positivity)] at habs_le4
        have hlenR : ((b - a + 1 : ℕ) : ℝ) ≤ 4 * (P : ℝ) ^ 2 := by
          have h1 : ((b - a + 1 : ℕ) : ℝ) * ((P : ℝ) ^ 2)⁻¹ ≤ 4 :=
            (mul_le_mul_of_nonneg_left hc_ge (by positivity)).trans habs_le4
          have h2 := mul_le_mul_of_nonneg_right h1 hP2_pos.le
          rw [mul_assoc, inv_mul_cancel₀ hP2_pos.ne', mul_one] at h2
          exact h2
        have hlen : b - a + 1 ≤ 4 * P ^ 2 := by exact_mod_cast hlenR
        refine (Finset.card_filter_le _ _).trans ?_
        rw [Nat.card_Icc]; omega
    · rw [Finset.Icc_eq_empty hab, Finset.filter_empty, Finset.card_empty]; omega
  have hgen : ∀ (M : ℕ) (a b : ℕ), 2 ≤ a →
      ((Finset.Icc a (b - 1)).filter (fun j : ℕ => β (j : ℤ) ≠ 0)).card ≤ M →
      ((Finset.Icc a b).filter (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ))).card ≤
        4 * P ^ 2 * (M + 1) := by
    intro M
    induction M with
    | zero => intro a b ha hcard0; simpa using hbase a b ha hcard0
    | succ M ih =>
      intro a b ha hcard
      let Bset := (Finset.Icc a (b - 1)).filter (fun j : ℕ => β (j : ℤ) ≠ 0)
      by_cases hBe : Bset = ∅
      · have h0' : Bset.card ≤ M := by rw [hBe, Finset.card_empty]; omega
        exact (ih a b ha h0').trans (by nlinarith)
      · have hBne : Bset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hBe
        let c := Bset.min' hBne
        have hc_mem : c ∈ Bset := Finset.min'_mem Bset hBne
        have hc_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hc_mem).1
        have hsplit : Finset.Icc a b = Finset.Icc a c ∪ Finset.Icc (c + 1) b := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        have hdisj : Disjoint (Finset.Icc a c) (Finset.Icc (c + 1) b) := by
          rw [Finset.disjoint_left]; intro j h1 h2
          simp only [Finset.mem_Icc] at h1 h2; omega
        rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
          (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
        have hleft0 : ((Finset.Icc a (c - 1)).filter (fun j : ℕ => β (j : ℤ) ≠ 0)).card ≤ 0 := by
          rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j hj hne
          simp only [Finset.mem_Icc] at hj
          have hmem : j ∈ Bset := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj.1, by omega⟩, hne⟩
          have hle := Finset.min'_le Bset j hmem
          omega
        have hrightM : ((Finset.Icc (c + 1) (b - 1)).filter (fun j : ℕ => β (j : ℤ) ≠ 0)).card ≤ M := by
          have hsub : (Finset.Icc (c + 1) (b - 1)).filter (fun j : ℕ => β (j : ℤ) ≠ 0) ⊆ Bset.erase c := by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase, Bset] at hj ⊢
            exact ⟨by omega, ⟨by omega, hj.1.2⟩, hj.2⟩
          have h1 := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem hc_mem] at h1
          have hBle : Bset.card ≤ M + 1 := hcard
          omega
        have hleft_le := hbase a c ha hleft0
        have hright_le := ih (c + 1) b (by omega) hrightM
        nlinarith
  have hsub : (Finset.Icc 2 (N - 1)).filter (fun j : ℕ => β (j : ℤ) ≠ 0) ⊆
      (Finset.Icc 1 N).filter (fun j : ℕ => β (j : ℤ) ≠ 0) := by
    intro j hj; simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢; exact ⟨⟨by omega, by omega⟩, hj.2⟩
  exact hgen _ 2 N le_rfl (Finset.card_le_card hsub)

/- ### Section 5: Support Counting, Fejer Multiplier Identity, and Double-Log Inversion -/

/-- Deletion of at most q points from [A, B] leaves at most q + 1 intervals on which a predicate
fails; if each such interval has at most L elements of a set Bsupp, then Bsupp.card ≤ q + (q+1)*L. -/
lemma card_filter_le_of_small_between (L : ℕ) (Pbad Pgood : ℤ → Prop) [DecidablePred Pbad]
    [DecidablePred Pgood]
    (hsmall : ∀ A B : ℤ, (∀ j ∈ Finset.Icc A B, ¬ Pbad j) →
      ((Finset.Icc A B).filter Pgood).card ≤ L) :
    ∀ (q : ℕ) (A B : ℤ), ((Finset.Icc A B).filter Pbad).card ≤ q →
      ((Finset.Icc A B).filter Pgood).card ≤ q + (q + 1) * L := by
  intro q
  induction q with
  | zero =>
    intro A B hq0
    have hno : ∀ j ∈ Finset.Icc A B, ¬ Pbad j := by
      intro j hj hbad
      have hpos : 0 < ((Finset.Icc A B).filter Pbad).card :=
        Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hbad⟩⟩
      omega
    simpa using hsmall A B hno
  | succ q ih =>
    intro A B hq
    let Bad := (Finset.Icc A B).filter Pbad
    by_cases hBe : Bad = ∅
    · have h0 : Bad.card ≤ q := by rw [hBe, Finset.card_empty]; omega
      exact (ih A B h0).trans (by nlinarith)
    · have hBne : Bad.Nonempty := Finset.nonempty_iff_ne_empty.mpr hBe
      let c := Bad.min' hBne
      have hc_mem : c ∈ Bad := Finset.min'_mem Bad hBne
      have hc_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hc_mem).1
      have hsplit : Finset.Icc A B = Finset.Icc A (c - 1) ∪ ({c} ∪ Finset.Icc (c + 1) B) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
      have hd1 : Disjoint (Finset.Icc A (c - 1)) ({c} ∪ Finset.Icc (c + 1) B) := by
        rw [Finset.disjoint_left]; intro j h1 h2
        simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton] at h1 h2; omega
      have hd2 : Disjoint ({c} : Finset ℤ) (Finset.Icc (c + 1) B) := by
        rw [Finset.disjoint_left]; intro j h1 h2
        simp only [Finset.mem_singleton, Finset.mem_Icc] at h1 h2; omega
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
        (hd1.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
        Finset.filter_union, Finset.card_union_of_disjoint
        (hd2.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      have hleft : ((Finset.Icc A (c - 1)).filter Pgood).card ≤ L := by
        refine hsmall A (c - 1) fun j hj hbad => ?_
        simp only [Finset.mem_Icc] at hj
        have hmem : j ∈ Bad := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj.1, by omega⟩, hbad⟩
        have := Finset.min'_le Bad j hmem
        omega
      have hmid : (({c} : Finset ℤ).filter Pgood).card ≤ 1 :=
        (Finset.card_filter_le _ _).trans (by simp)
      have hright_bad : ((Finset.Icc (c + 1) B).filter Pbad).card ≤ q := by
        have hsub : (Finset.Icc (c + 1) B).filter Pbad ⊆ Bad.erase c := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase, Bad] at hj ⊢
          exact ⟨by omega, ⟨by omega, hj.1.2⟩, hj.2⟩
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hc_mem] at h1
        have hBadle : Bad.card ≤ q + 1 := hq
        omega
      have hright := ih (c + 1) B hright_bad
      nlinarith

/-- Fejer kernel identity: |(1/P) * ∑_{s=0}^{P-1} e^{i s x}|^2 = ∑_{j=-P}^P ((P - |j|)/P^2) e^{i j x}. -/
lemma fejer_kernel_eval (P : ℕ) (hP : 1 ≤ P) (x : ℝ) :
    ((‖((P : ℂ)⁻¹ * ∑ s ∈ Finset.range P, eChar (s : ℤ) x)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
        ((((P : ℝ) - (|j| : ℝ)) / (P : ℝ) ^ 2 : ℝ) : ℂ) * eChar j x := by
  have hPpos : (0 : ℝ) < (P : ℝ) := by positivity
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum]
  simp_rw [← eChar_neg]
  have hmul : ((P : ℂ)⁻¹ * ∑ s ∈ Finset.range P, eChar (s : ℤ) x) *
      ((P : ℂ)⁻¹ * ∑ t ∈ Finset.range P, eChar (-(t : ℤ)) x) =
      ((P : ℂ) ^ 2)⁻¹ * ∑ s ∈ Finset.range P, ∑ t ∈ Finset.range P, eChar ((s : ℤ) - (t : ℤ)) x := by
    rw [show ((P : ℂ)⁻¹ * ∑ s ∈ Finset.range P, eChar (s : ℤ) x) *
        ((P : ℂ)⁻¹ * ∑ t ∈ Finset.range P, eChar (-(t : ℤ)) x) =
      ((P : ℂ) ^ 2)⁻¹ * ((∑ s ∈ Finset.range P, eChar (s : ℤ) x) *
        (∑ t ∈ Finset.range P, eChar (-(t : ℤ)) x)) by ring]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← eChar_add, sub_eq_add_neg]
  rw [hmul]
  -- Group pairs (s, t) ∈ range P × range P by j = s - t ∈ Icc (-P) P
  have hgroup : ∑ s ∈ Finset.range P, ∑ t ∈ Finset.range P, eChar ((s : ℤ) - (t : ℤ)) x =
      ∑ j ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), (((P : ℝ) - (|j| : ℝ) : ℝ) : ℂ) * eChar j x := by
    rw [← Finset.sum_product']
    have hmaps : ∀ p ∈ Finset.range P ×ˢ Finset.range P,
        ((p.1 : ℤ) - (p.2 : ℤ)) ∈ Finset.Icc (-(P : ℤ)) (P : ℤ) := by
      intro p hp
      simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hp ⊢
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hconst : ∑ p ∈ (Finset.range P ×ˢ Finset.range P).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = j),
        eChar ((p.1 : ℤ) - (p.2 : ℤ)) x =
        ∑ _p ∈ (Finset.range P ×ˢ Finset.range P).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = j),
          eChar j x :=
      Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
    rw [hconst, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hj_Icc := Finset.mem_Icc.mp hj
    have hcard : ((Finset.range P ×ˢ Finset.range P).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = j)).card =
        P - j.natAbs := by
      by_cases hj0 : 0 ≤ j
      · have hjnat : (j.natAbs : ℤ) = j := Int.natAbs_of_nonneg hj0
        have hbij : ((Finset.range P ×ˢ Finset.range P).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = j)).card =
            (Finset.range (P - j.natAbs)).card := by
          refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
            omega
          · intro p1 hp1 p2 hp2 heq
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp1 hp2
            exact Prod.ext (by omega) heq
          · intro t ht
            simp only [Finset.mem_range] at ht
            refine ⟨(t + j.natAbs, t), ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            omega
        rw [hbij, Finset.card_range]
      · have hjnat : (j.natAbs : ℤ) = -j := Int.ofNat_natAbs_of_nonpos (by omega)
        have hbij : ((Finset.range P ×ˢ Finset.range P).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = j)).card =
            (Finset.range (P - j.natAbs)).card := by
          refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
            omega
          · intro p1 hp1 p2 hp2 heq
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp1 hp2
            exact Prod.ext heq (by omega)
          · intro s hs
            simp only [Finset.mem_range] at hs
            refine ⟨(s, s + j.natAbs), ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            omega
        rw [hbij, Finset.card_range]
    rw [hcard]
    have hle : j.natAbs ≤ P := by omega
    have habs : (|(j : ℝ)|) = (j.natAbs : ℝ) := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs j]
      simp
    rw [habs, Nat.cast_sub hle]
    push_cast; rfl
  rw [hgroup, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

/-- Second discrete difference of the triangular Fejer sequence τ. -/
lemma fejer_second_diff (P : ℕ) (hP : 1 ≤ P) (k : ℤ) :
    let τ : ℤ → ℝ := fun j => if |j| ≤ (P : ℤ) then ((P : ℝ) - ((|j| : ℤ) : ℝ)) / (P : ℝ) ^ 2 else 0
    τ (k - 1) - 2 * τ k + τ (k + 1) =
      ((if k = (P : ℤ) then (1 : ℝ) else 0) + (if k = -(P : ℤ) then (1 : ℝ) else 0) -
        (if k = 0 then (2 : ℝ) else 0)) / (P : ℝ) ^ 2 := by
  intro τ
  dsimp only [τ]
  have hP1 : (1 : ℤ) ≤ (P : ℤ) := by exact_mod_cast hP
  by_cases hk0 : k = 0
  · subst hk0
    have h1 : |(-1 : ℤ)| ≤ (P : ℤ) := by norm_num; omega
    have h2 : |(0 : ℤ)| ≤ (P : ℤ) := by norm_num
    have h3 : |(1 : ℤ)| ≤ (P : ℤ) := by norm_num; omega
    simp only [zero_sub, zero_add, h1, h2, h3, ite_true, show (0 : ℤ) ≠ (P : ℤ) by omega,
      show (0 : ℤ) ≠ -(P : ℤ) by omega, ite_false]
    norm_num
    ring
  · by_cases hkP : k = (P : ℤ)
    · subst hkP
      have h1 : |(P : ℤ) - 1| ≤ (P : ℤ) := by rw [abs_of_nonneg (by omega)]; omega
      have h2 : |(P : ℤ)| ≤ (P : ℤ) := by rw [abs_of_nonneg (by omega)]
      have h3 : ¬ |(P : ℤ) + 1| ≤ (P : ℤ) := by rw [abs_of_nonneg (by omega)]; omega
      simp only [h1, h2, h3, ite_true, ite_false, show (P : ℤ) ≠ -(P : ℤ) by omega,
        show (P : ℤ) ≠ 0 by omega]
      rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (P : ℤ) - 1), abs_of_nonneg (by omega : (0 : ℤ) ≤ (P : ℤ))]
      push_cast; ring
    · by_cases hkNP : k = -(P : ℤ)
      · subst hkNP
        have h1 : ¬ |-(P : ℤ) - 1| ≤ (P : ℤ) := by rw [abs_of_nonpos (by omega)]; omega
        have h2 : |-(P : ℤ)| ≤ (P : ℤ) := by rw [abs_of_nonpos (by omega)]; omega
        have h3 : |-(P : ℤ) + 1| ≤ (P : ℤ) := by rw [abs_of_nonpos (by omega)]; omega
        simp only [h1, h2, h3, ite_true, ite_false, show -(P : ℤ) ≠ (P : ℤ) by omega,
          show -(P : ℤ) ≠ 0 by omega]
        rw [abs_of_nonpos (by omega : -(P : ℤ) ≤ 0), abs_of_nonpos (by omega : -(P : ℤ) + 1 ≤ 0)]
        push_cast; ring
      · simp only [hk0, hkP, hkNP, ite_false]
        by_cases hlt : |k| < (P : ℤ)
        · have h1 : |k - 1| ≤ (P : ℤ) := by rw [abs_lt] at hlt; rw [abs_le]; omega
          have h2 : |k| ≤ (P : ℤ) := le_of_lt hlt
          have h3 : |k + 1| ≤ (P : ℤ) := by rw [abs_lt] at hlt; rw [abs_le]; omega
          simp only [h1, h2, h3, ite_true]
          rcases lt_or_gt_of_ne hk0 with hneg | hpos
          · rw [abs_of_nonpos (by omega : k - 1 ≤ 0), abs_of_nonpos (by omega : k ≤ 0),
              abs_of_nonpos (by omega : k + 1 ≤ 0)]
            push_cast; ring
          · rw [abs_of_nonneg (by omega : 0 ≤ k - 1), abs_of_nonneg (by omega : 0 ≤ k),
              abs_of_nonneg (by omega : 0 ≤ k + 1)]
            push_cast; ring
        · have hgt : (P : ℤ) < |k| := by
            have hne : |k| ≠ (P : ℤ) := by
              intro h; rcases eq_or_eq_neg_of_abs_eq h with h1 | h2
              · exact hkP h1
              · exact hkNP h2
            omega
          have h1 : ¬ |k - 1| ≤ (P : ℤ) ∨ |k - 1| = (P : ℤ) := by
            by_cases h : |k - 1| = (P : ℤ); · exact Or.inr h
            left; intro hle; rw [abs_le] at hle; rcases le_or_gt 0 k with hk | hk
            · rw [abs_of_nonneg hk] at hgt; rw [abs_of_nonneg (by omega)] at h; omega
            · rw [abs_of_neg hk] at hgt; rw [abs_of_neg (by omega)] at h; omega
          have h3 : ¬ |k + 1| ≤ (P : ℤ) ∨ |k + 1| = (P : ℤ) := by
            by_cases h : |k + 1| = (P : ℤ); · exact Or.inr h
            left; intro hle; rw [abs_le] at hle; rcases le_or_gt 0 k with hk | hk
            · rw [abs_of_nonneg hk] at hgt; rw [abs_of_nonneg (by omega)] at h; omega
            · rw [abs_of_neg hk] at hgt; rw [abs_of_neg (by omega)] at h; omega
          have ht1 : (if |k - 1| ≤ (P : ℤ) then ((P : ℝ) - ((|k - 1| : ℤ) : ℝ)) / (P : ℝ) ^ 2 else 0) = 0 := by
            split_ifs with h
            · rcases h1 with hn | heq
              · exact absurd h hn
              · rw [heq]; push_cast; ring
            · rfl
          have ht2 : (if |k| ≤ (P : ℤ) then ((P : ℝ) - ((|k| : ℤ) : ℝ)) / (P : ℝ) ^ 2 else 0) = 0 := by
            rw [if_neg (by omega)]
          have ht3 : (if |k + 1| ≤ (P : ℤ) then ((P : ℝ) - ((|k + 1| : ℤ) : ℝ)) / (P : ℝ) ^ 2 else 0) = 0 := by
            split_ifs with h
            · rcases h3 with hn | heq
              · exact absurd h hn
              · rw [heq]; push_cast; ring
            · rfl
          rw [ht1, ht2, ht3]; ring

/-- Elementary factorial upper bound: k! ≤ k^k for k ≥ 1. -/
lemma factorial_le_pow_self (k : ℕ) : k.factorial ≤ k ^ k := Nat.factorial_le_pow k

set_option maxHeartbeats 800000 in
/-- Pure real algebra: invert the MPS + Fejer + support bounds into (1/108)*X/log X ≤ d. -/
lemma double_log_inversion (n d q m : ℕ) (hn_big : Real.exp (Real.exp 3000) ≤ (n : ℝ))
    (hlog_q :
      let r := 2 * d + 1
      let P := (2 * r).factorial
      let δ : ℝ := (2 * (r.factorial : ℝ) * (8 : ℝ) ^ r)⁻¹
      let B₀ : ℕ := 17 ^ r + 4 * r + 10 * P + 10 + 1
      let U : ℝ := 8 * (4 : ℝ) ^ d
      Real.log ((q : ℝ) + 1) ≤ Real.log (B₀ : ℝ) + 400 * U * (B₀ : ℝ) / δ)
    (hm_le :
      let r := 2 * d + 1
      let P := (2 * r).factorial
      let B₀ : ℕ := 17 ^ r + 4 * r + 10 * P + 10 + 1
      m + 1 ≤ (q + 1) * B₀)
    (hcomb :
      let r := 2 * d + 1
      let P := (2 * r).factorial
      let K : ℕ := 1 + 4 * P ^ 2 * (m + 1)
      (1 / (400 * (P : ℝ) ^ 2)) * Real.log (1 + (n : ℝ) / 2) ≤
        60 * ((d : ℝ) + 1) * (1 + Real.log (K : ℝ))) :
    (1 / 108 : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (Real.log (Real.log (n : ℝ))) ≤ (d : ℝ) := by
  let r : ℕ := 2 * d + 1
  let P : ℕ := (2 * r).factorial
  let δ : ℝ := (2 * (r.factorial : ℝ) * (8 : ℝ) ^ r)⁻¹
  let L : ℕ := 17 ^ r + 4 * r + 10 * P + 10
  let B₀ : ℕ := L + 1
  let U : ℝ := 8 * (4 : ℝ) ^ d
  let K : ℕ := 1 + 4 * P ^ 2 * (m + 1)
  have hr1 : 1 ≤ r := by omega
  have hK1 : 1 ≤ K := by omega
  have he3000 : (3000 : ℝ) < Real.exp 3000 := by linarith [Real.add_one_lt_exp (by norm_num : (3000 : ℝ) ≠ 0)]
  have hn_gt2 : (2 : ℝ) ≤ (n : ℝ) := by
    have h1 : (2 : ℝ) ≤ Real.exp 3000 := by linarith
    have h2 : Real.exp 3000 ≤ Real.exp (Real.exp 3000) := by linarith [Real.add_one_le_exp (Real.exp 3000)]
    linarith
  have hlogn_ge : Real.exp 3000 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hn_big
    rwa [Real.log_exp] at h
  have hlogn_pos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hlogn_ge
  have hX3000 : (3000 : ℝ) ≤ Real.log (Real.log (n : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos _) hlogn_ge
    rwa [Real.log_exp] at h
  let D : ℝ := (1000 * (r : ℝ)) ^ (2 * r)
  have hrR1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hD_ge : (1000000 : ℝ) ≤ D := by
    dsimp [D]
    have h1 : (1000 : ℝ) ^ 2 ≤ (1000 * (r : ℝ)) ^ 2 := by nlinarith
    have h2 : (1000 * (r : ℝ)) ^ 2 ≤ (1000 * (r : ℝ)) ^ (2 * r) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  have hD_pos : 0 < D := by linarith
  have hP_le_D : (P : ℝ) ≤ D := by
    have h1 : P ≤ (2 * r) ^ (2 * r) := factorial_le_pow_self (2 * r)
    have h2 : (P : ℝ) ≤ (2 * (r : ℝ)) ^ (2 * r) := by exact_mod_cast h1
    exact h2.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
  have hδinv_le_D : δ⁻¹ ≤ D := by
    dsimp [δ]
    rw [inv_inv]
    have hfac : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast factorial_le_pow_self r
    have h1 : 2 * (r.factorial : ℝ) * (8 : ℝ) ^ r ≤ 2 * (r : ℝ) ^ r * (8 : ℝ) ^ r := by gcongr
    have h2 : 2 * (r : ℝ) ^ r * (8 : ℝ) ^ r = 2 * (8 * (r : ℝ)) ^ r := by rw [mul_pow]; ring
    have h3 : 2 * (8 * (r : ℝ)) ^ r ≤ (1000 * (r : ℝ)) ^ r := by
      have hpow : (8 * (r : ℝ)) ^ r ≤ (500 * (r : ℝ)) ^ r :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      have h2r : 2 * (500 * (r : ℝ)) ^ r ≤ (1000 * (r : ℝ)) ^ r := by
        have hmul : (1000 * (r : ℝ)) ^ r = 2 ^ r * (500 * (r : ℝ)) ^ r := by rw [← mul_pow]; ring_nf
        rw [hmul]
        have h2le : (2 : ℝ) ≤ 2 ^ r := by
          simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr1
        exact mul_le_mul_of_nonneg_right h2le (by positivity)
      linarith
    have h4 : (1000 * (r : ℝ)) ^ r ≤ (1000 * (r : ℝ)) ^ (2 * r) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  have hU_le_D : U ≤ D := by
    dsimp [U]
    have h1 : (4 : ℝ) ^ d ≤ (4 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : 8 * (4 : ℝ) ^ r ≤ (1000 * (r : ℝ)) ^ r := by
      have hpow : (4 : ℝ) ^ r ≤ (125 * (r : ℝ)) ^ r := pow_le_pow_left₀ (by positivity) (by linarith) _
      have h8 : 8 * (125 * (r : ℝ)) ^ r ≤ (1000 * (r : ℝ)) ^ r := by
        have hmul : (1000 * (r : ℝ)) ^ r = 8 ^ r * (125 * (r : ℝ)) ^ r := by rw [← mul_pow]; ring_nf
        rw [hmul]
        have h8le : (8 : ℝ) ≤ 8 ^ r := by
          simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8) hr1
        exact mul_le_mul_of_nonneg_right h8le (by positivity)
      linarith
    have h3 : (1000 * (r : ℝ)) ^ r ≤ D := pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  have hB0_le_D : (B₀ : ℝ) ≤ D := by
    have h17 : (17 : ℝ) ^ r ≤ (1000 * (r : ℝ)) ^ r := pow_le_pow_left₀ (by norm_num) (by linarith) _
    have h17_2 : (1000 * (r : ℝ)) ^ r ≤ D / 1000 := by
      have hmul : D = (1000 * (r : ℝ)) ^ r * (1000 * (r : ℝ)) ^ r := by
        dsimp [D]; rw [← pow_add, show r + r = 2 * r by omega]
      have hge : (1000 : ℝ) ≤ (1000 * (r : ℝ)) ^ r := by
        have h1 : (1000 : ℝ) ≤ 1000 * (r : ℝ) := by linarith
        exact h1.trans (by simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1000 * (r : ℝ)) hr1)
      rw [le_div_iff₀ (by norm_num), hmul]
      exact mul_le_mul_of_nonneg_left hge (by positivity)
    have hP_le_D100 : (P : ℝ) ≤ D / 100 := by
      have h1 : (P : ℝ) ≤ (2 * (r : ℝ)) ^ (2 * r) := by exact_mod_cast factorial_le_pow_self (2 * r)
      have h2 : (1000 * (r : ℝ)) ^ (2 * r) = 500 ^ (2 * r) * (2 * (r : ℝ)) ^ (2 * r) := by
        rw [← mul_pow]; ring_nf
      have h500 : (100 : ℝ) ≤ 500 ^ (2 * r) := by
        have : (500 : ℝ) ≤ 500 ^ (2 * r) := by
          simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 500) (by omega : 1 ≤ 2 * r)
        linarith
      rw [le_div_iff₀ (by norm_num)]
      dsimp [D]; rw [h2]
      calc (P : ℝ) * 100 ≤ (2 * (r : ℝ)) ^ (2 * r) * 100 := by linarith
        _ ≤ (2 * (r : ℝ)) ^ (2 * r) * 500 ^ (2 * r) := mul_le_mul_of_nonneg_left h500 (by positivity)
        _ = 500 ^ (2 * r) * (2 * (r : ℝ)) ^ (2 * r) := by ring
    have hr_le : (r : ℝ) ≤ D / 1000 := by
      have h1 : (r : ℝ) ≤ (1000 * (r : ℝ)) ^ r := by
        have : (r : ℝ) ≤ 1000 * (r : ℝ) := by linarith
        exact this.trans (by simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1000 * (r : ℝ)) hr1)
      linarith
    have hB0_eq : (B₀ : ℝ) = (17 : ℝ) ^ r + 4 * (r : ℝ) + 10 * (P : ℝ) + 11 := by
      dsimp [B₀, L]; push_cast; ring
    linarith
  have hd1_le_D : ((d : ℝ) + 1) ≤ D := by
    have : (d : ℝ) + 1 ≤ (r : ℝ) := by dsimp [r]; push_cast; linarith
    have hr_le : (r : ℝ) ≤ D := by
      have h1 : (r : ℝ) ≤ 1000 * (r : ℝ) := by linarith
      exact h1.trans (by simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1000 * (r : ℝ)) (by omega : 1 ≤ 2 * r))
    linarith
  have hD4_eq : D ^ 4 = D * D ^ 3 := by ring
  have hD3_ge : (1 : ℝ) ≤ D ^ 3 := one_le_pow₀ (by linarith)
  have hD4_ge : D ^ 3 ≤ D ^ 4 := by nlinarith
  have hlogD_le_D : Real.log D ≤ D := by linarith [Real.log_le_sub_one_of_pos hD_pos]
  have hlog_q_D : Real.log ((q : ℝ) + 1) ≤ 2 * D ^ 4 := by
    have hlogB0 : Real.log (B₀ : ℝ) ≤ D := (Real.log_le_log (by positivity) hB0_le_D).trans hlogD_le_D
    have hterm : 400 * U * (B₀ : ℝ) / δ ≤ 400 * D ^ 3 := by
      rw [div_eq_mul_inv]
      have h1 : U * (B₀ : ℝ) * δ⁻¹ ≤ D * D * D :=
        mul_le_mul (mul_le_mul hU_le_D hB0_le_D (by positivity) hD_pos.le) hδinv_le_D (by positivity) (by positivity)
      linarith [show D * D * D = D ^ 3 by ring]
    have hD_le_D3 : D ≤ D ^ 3 := by
      have : D ^ 1 ≤ D ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
      simpa using this
    have hD3 : 400 * D ^ 3 + D ≤ 2 * D ^ 4 := by nlinarith
    linarith [hlog_q]
  have hlog_m_D : Real.log ((m : ℝ) + 1) ≤ 4 * D ^ 4 := by
    have h1 : Real.log ((m : ℝ) + 1) ≤ Real.log (((q : ℝ) + 1) * (B₀ : ℝ)) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hm_le)
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    have hlogB0 : Real.log (B₀ : ℝ) ≤ D := (Real.log_le_log (by positivity) hB0_le_D).trans hlogD_le_D
    have hD_le : D ≤ 2 * D ^ 4 := by
      have : D ^ 1 ≤ D ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith [show D ^ 1 = D by ring]
    linarith
  have hlog_K_D : Real.log (K : ℝ) ≤ 7 * D ^ 4 := by
    have hK_le : (K : ℝ) ≤ 5 * D ^ 2 * ((m : ℝ) + 1) := by
      have h1 : (K : ℝ) = 1 + 4 * (P : ℝ) ^ 2 * ((m : ℝ) + 1) := by dsimp [K]; push_cast; ring
      have hP2 : (P : ℝ) ^ 2 ≤ D ^ 2 := by nlinarith [show (0 : ℝ) ≤ (P : ℝ) by positivity]
      have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
      have hD2 : (1 : ℝ) ≤ D ^ 2 := one_le_pow₀ (by linarith)
      have h4 : 4 * (P : ℝ) ^ 2 * ((m : ℝ) + 1) ≤ 4 * D ^ 2 * ((m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (Nat.cast_nonneg m) zero_le_one)
      have h1le : (1 : ℝ) ≤ D ^ 2 * ((m : ℝ) + 1) := by nlinarith
      linarith
    have hK_posR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
    have hD2_pos : (0 : ℝ) < D ^ 2 := sq_pos_of_pos (by linarith)
    have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) zero_lt_one
    have h1 : Real.log (K : ℝ) ≤ Real.log (5 * D ^ 2 * ((m : ℝ) + 1)) :=
      Real.log_le_log hK_posR hK_le
    rw [Real.log_mul (mul_pos (by norm_num) hD2_pos).ne' hm1_pos.ne',
      Real.log_mul (by norm_num) hD2_pos.ne', Real.log_pow] at h1
    push_cast at h1
    have hlog5 : Real.log 5 ≤ 5 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)]
    have hD_le : 5 + 2 * D ≤ 3 * D ^ 4 := by
      have : D ^ 1 ≤ D ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith [show D ^ 1 = D by ring]
    linarith
  have hlog_n_D9 : Real.log (n : ℝ) ≤ D ^ 9 := by
    have hP2pos : (0 : ℝ) < 400 * (P : ℝ) ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hcomb hP2pos.le
    rw [show 400 * (P : ℝ) ^ 2 * (1 / (400 * (P : ℝ) ^ 2) * Real.log (1 + (n : ℝ) / 2)) =
      Real.log (1 + (n : ℝ) / 2) by rw [← mul_assoc, mul_one_div_cancel hP2pos.ne', one_mul]] at h1
    have hP2D : (P : ℝ) ^ 2 ≤ D ^ 2 := by nlinarith [show (0 : ℝ) ≤ (P : ℝ) by positivity]
    have hK_pos : 0 ≤ 1 + Real.log (K : ℝ) := by
      have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
      linarith [Real.log_nonneg this]
    have hprod1 : 400 * (P : ℝ) ^ 2 * (60 * ((d : ℝ) + 1) * (1 + Real.log (K : ℝ))) ≤
        400 * D ^ 2 * (60 * D * (1 + 7 * D ^ 4)) := by
      have hA : 400 * (P : ℝ) ^ 2 ≤ 400 * D ^ 2 := by linarith
      have hB : 60 * ((d : ℝ) + 1) * (1 + Real.log (K : ℝ)) ≤ 60 * D * (1 + 7 * D ^ 4) :=
        mul_le_mul (by linarith) (by linarith) hK_pos (by positivity)
      exact mul_le_mul hA hB (by positivity) (by positivity)
    have hD8 : 400 * D ^ 2 * (60 * D * (1 + 7 * D ^ 4)) ≤ D ^ 8 := by
      have h1' : 400 * D ^ 2 * (60 * D * (1 + 7 * D ^ 4)) = 24000 * D ^ 3 + 168000 * D ^ 7 := by ring
      rw [h1']
      have hD3 : D ^ 3 ≤ D ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have hD7pos : 0 < D ^ 7 := by positivity
      have hD8_eq : D ^ 8 = D * D ^ 7 := by ring
      nlinarith
    have hlog_half : Real.log (1 + (n : ℝ) / 2) ≤ D ^ 8 := h1.trans (hprod1.trans hD8)
    have hlog_n_le : Real.log (n : ℝ) ≤ Real.log (1 + (n : ℝ) / 2) + 1 := by
      have hn_le : (n : ℝ) ≤ 2 * (1 + (n : ℝ) / 2) := by linarith
      have h2 := Real.log_le_log (by positivity) hn_le
      rw [Real.log_mul (by norm_num) (by positivity)] at h2
      linarith [Real.log_two_lt_d9]
    have hD9_eq : D ^ 9 = D * D ^ 8 := by ring
    have hD8_ge1 : (1 : ℝ) ≤ D ^ 8 := one_le_pow₀ (by linarith)
    nlinarith
  let X : ℝ := Real.log (Real.log (n : ℝ))
  have hX_le : X ≤ 18 * (r : ℝ) * Real.log (1000 * (r : ℝ)) := by
    have h1 : X ≤ Real.log (D ^ 9) := Real.log_le_log hlogn_pos hlog_n_D9
    rw [Real.log_pow] at h1
    dsimp [D] at h1
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hd_pos : 1 ≤ d := by
    by_contra hd0
    have hd_eq : d = 0 := by omega
    have hr_eq : (r : ℝ) = 1 := by dsimp [r]; rw [hd_eq]; norm_num
    rw [hr_eq, mul_one, mul_one] at hX_le
    have hlog1000 : Real.log (1000 : ℝ) ≤ 10 := by
      have h1000 : (1000 : ℝ) ≤ Real.exp 10 := by
        have h1 : (2 : ℝ) ^ 10 ≤ Real.exp 10 := by
          have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          calc (2 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) this 10
            _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
        linarith [show (1000 : ℝ) ≤ (2 : ℝ) ^ 10 by norm_num]
      calc Real.log (1000 : ℝ) ≤ Real.log (Real.exp 10) := Real.log_le_log (by norm_num) h1000
        _ = 10 := Real.log_exp 10
    linarith
  have hlogX_pos : 0 < Real.log X := Real.log_pos (by linarith)
  by_cases hdX : X ≤ (d : ℝ)
  · have hlogX_ge1 : (1 : ℝ) ≤ Real.log X := by
      have h1 : Real.exp 1 ≤ X := by linarith [Real.exp_one_lt_d9]
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log X := Real.log_le_log (Real.exp_pos 1) h1
    rw [div_le_iff₀ hlogX_pos]
    nlinarith
  · push Not at hdX
    have hr_le3d : (r : ℝ) ≤ 3 * (d : ℝ) := by
      have : r ≤ 3 * d := by dsimp [r]; omega
      exact_mod_cast this
    have hlog_le : Real.log (1000 * (r : ℝ)) ≤ 2 * Real.log X := by
      have h3000X : 1000 * (r : ℝ) ≤ X ^ 2 := by nlinarith
      have h1 := Real.log_le_log (by positivity) h3000X
      rw [Real.log_pow] at h1
      simpa using h1
    have hX_le2 : X ≤ 108 * (d : ℝ) * Real.log X := by
      have h1 : 18 * (r : ℝ) * Real.log (1000 * (r : ℝ)) ≤ 18 * (3 * (d : ℝ)) * (2 * Real.log X) :=
        mul_le_mul (by linarith) hlog_le (Real.log_nonneg (by linarith)) (by positivity)
      linarith
    rw [div_le_iff₀ hlogX_pos]
    linarith

set_option maxHeartbeats 1600000 in
/-- Main quantitative theorem (Bedert Theorem 1.3 for b_k ≤ 2, c = 1/108). -/
theorem green_82_H2_core :
    ∀ (n : ℕ), Real.exp (Real.exp 3000) ≤ (n : ℝ) →
      ∀ (S : Finset ℕ) (b : ℕ → ℕ),
        (∀ k ∈ S, b k ≤ 2) → (∑ k ∈ S, b k) = n →
        ⌊(1 / 108 : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (Real.log (Real.log (n : ℝ)))⌋₊ ≤
          ({θ : ℝ | θ ∈ Set.Ico (0 : ℝ) 1 ∧
            ∑ k ∈ S, (b k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * θ) = 0} : Set ℝ).ncard := by
  classical
  intro n hn_big S b hb2 hsum
  -- Lower bounds on n, log n, log(log n)
  have he3000 : (3000 : ℝ) < Real.exp 3000 := by linarith [Real.add_one_lt_exp (by norm_num : (3000 : ℝ) ≠ 0)]
  have hn_gt2 : (2 : ℝ) ≤ (n : ℝ) := by
    have h1 : (2 : ℝ) ≤ Real.exp 3000 := by linarith
    have h2 : Real.exp 3000 ≤ Real.exp (Real.exp 3000) := by
      linarith [Real.add_one_le_exp (Real.exp 3000)]
    linarith
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  have hlogn_ge : Real.exp 3000 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hn_big
    rwa [Real.log_exp] at h
  have hlogn_pos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hlogn_ge
  have hX3000 : (3000 : ℝ) ≤ Real.log (Real.log (n : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos _) hlogn_ge
    rwa [Real.log_exp] at h
  -- Extract sign changes of g(x) = ∑ k ∈ S, b k * cos(k * x)
  let g : ℝ → ℝ := fun x => ∑ k ∈ S, (b k : ℝ) * Real.cos ((k : ℝ) * x)
  obtain ⟨hZfull_fin, d, t, ht_strict, ht_mem, hd_le, hprod_nonneg, hsign_Icc⟩ :=
    cosine_sum_sign_changes S b n hsum hn1
  have hZeq : ({θ : ℝ | θ ∈ Set.Ico (0 : ℝ) 1 ∧
        ∑ k ∈ S, (b k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * θ) = 0} : Set ℝ) =
      {θ : ℝ | θ ∈ Set.Ico (0 : ℝ) 1 ∧ g (2 * Real.pi * θ) = 0} := by
    ext θ; simp only [Set.mem_setOf_eq, g]
    refine and_congr_right fun _ => ?_
    have : (∑ k ∈ S, (b k : ℝ) * Real.cos (2 * Real.pi * (k : ℝ) * θ)) =
        ∑ k ∈ S, (b k : ℝ) * Real.cos ((k : ℝ) * (2 * Real.pi * θ)) :=
      Finset.sum_congr rfl fun k _ => by ring_nf
    rw [this]
  rw [hZeq]
  -- Define r, P, M, p, β, T, u, v, δ, L, B₀, U
  let r : ℕ := 2 * d + 1
  let P : ℕ := (2 * r).factorial
  have hr1 : 1 ≤ r := by omega
  have hP1 : 1 ≤ P := Nat.factorial_pos _
  let M : ℕ := S.sup id
  let p : ℤ → ℤ := fun j =>
    if j = 0 then (if 0 ∈ S then 2 * (b 0 : ℤ) else 0)
    else if j.natAbs ∈ S then (b j.natAbs : ℤ) else 0
  have hp0 : ∀ j, 0 ≤ p j := by
    intro j; dsimp [p]; split_ifs <;> positivity
  have hp4 : ∀ j, p j ≤ 4 := by
    intro j; dsimp [p]
    split_ifs with h0 h0S hS
    · have := hb2 0 h0S; omega
    · norm_num
    · have := hb2 j.natAbs hS; omega
    · norm_num
  have hp_even : ∀ j, p (-j) = p j := by
    intro j; dsimp [p]
    by_cases h0 : j = 0
    · subst h0; simp
    · simp [h0, Int.natAbs_neg]
  have hp_supp : ∀ j : ℤ, (M : ℤ) < |j| → p j = 0 := by
    intro j hj
    dsimp [p]
    split_ifs with h0 h0S hS
    · subst h0; simp at hj; omega
    · rfl
    · exfalso
      have hle : j.natAbs ≤ M := Finset.le_sup (f := id) hS
      have habs : |j| = (j.natAbs : ℤ) := (Int.natCast_natAbs j).symm
      omega
    · rfl
  have hp_eval : ∀ x : ℝ, ∑ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (p j : ℂ) * eChar j x =
      ((2 * g x : ℝ) : ℂ) := by
    intro x
    dsimp [g]
    have hsplit : Finset.Icc (-(M : ℤ)) (M : ℤ) =
        {0} ∪ ((Finset.Icc (1 : ℕ) M).image (fun k : ℕ => (k : ℤ)) ∪
               (Finset.Icc (1 : ℕ) M).image (fun k : ℕ => -(k : ℤ))) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
      constructor
      · intro ⟨hlo, hhi⟩
        rcases lt_trichotomy j 0 with hlt | rfl | hgt
        · right; right; exact ⟨j.natAbs, ⟨by omega, by omega⟩, by omega⟩
        · left; rfl
        · right; left; exact ⟨j.natAbs, ⟨by omega, by omega⟩, by omega⟩
      · rintro (rfl | ⟨k, ⟨h1, h2⟩, rfl⟩ | ⟨k, ⟨h1, h2⟩, rfl⟩) <;> omega
    have hd1 : Disjoint ({0} : Finset ℤ)
        ((Finset.Icc (1 : ℕ) M).image (fun k : ℕ => (k : ℤ)) ∪
         (Finset.Icc (1 : ℕ) M).image (fun k : ℕ => -(k : ℤ))) := by
      rw [Finset.disjoint_left]; intro j hj1 hj2
      simp only [Finset.mem_singleton, Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at hj1 hj2
      subst hj1; rcases hj2 with ⟨k, ⟨h1, _⟩, hk⟩ | ⟨k, ⟨h1, _⟩, hk⟩ <;> omega
    have hd2 : Disjoint ((Finset.Icc (1 : ℕ) M).image (fun k : ℕ => (k : ℤ)))
        ((Finset.Icc (1 : ℕ) M).image (fun k : ℕ => -(k : ℤ))) := by
      rw [Finset.disjoint_left]; intro j hj1 hj2
      simp only [Finset.mem_image, Finset.mem_Icc] at hj1 hj2
      obtain ⟨k1, ⟨h1, _⟩, rfl⟩ := hj1
      obtain ⟨k2, ⟨h2, _⟩, hk⟩ := hj2
      omega
    rw [hsplit, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton,
      Finset.sum_image (fun a _ b _ h => by omega),
      Finset.sum_image (fun a _ b _ h => by omega)]
    rw [← Finset.sum_add_distrib]
    have h0term : (p 0 : ℂ) * eChar 0 x =
        if 0 ∈ S then ((2 * ((b 0 : ℝ) * Real.cos ((0 : ℝ) * x)) : ℝ) : ℂ) else 0 := by
      dsimp [p]; rw [eChar_zero, mul_one]
      split_ifs <;> simp
    have hpos_term : ∀ k ∈ Finset.Icc (1 : ℕ) M,
        (p (k : ℤ) : ℂ) * eChar (k : ℤ) x + (p (-(k : ℤ)) : ℂ) * eChar (-(k : ℤ)) x =
        if k ∈ S then ((2 * ((b k : ℝ) * Real.cos ((k : ℝ) * x)) : ℝ) : ℂ) else 0 := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [hp_even, ← mul_add]
      have hcos : eChar (k : ℤ) x + eChar (-(k : ℤ)) x = ((2 * Real.cos ((k : ℝ) * x) : ℝ) : ℂ) := by
        unfold eChar; push_cast; rw [Complex.cos]
        have h1 : Complex.I * (k : ℂ) * (x : ℂ) = ((k : ℂ) * (x : ℂ)) * Complex.I := by ring
        have h2 : Complex.I * -(k : ℂ) * (x : ℂ) = -(((k : ℂ) * (x : ℂ)) * Complex.I) := by ring
        rw [h1, h2]; ring
      rw [hcos]
      have hpk : p (k : ℤ) = if k ∈ S then (b k : ℤ) else 0 := by
        dsimp [p]; rw [if_neg (by omega : (k : ℤ) ≠ 0)]
      rw [hpk]
      split_ifs
      · push_cast; ring
      · simp
    rw [h0term, Finset.sum_congr rfl hpos_term]
    have hSsub : S ⊆ insert 0 (Finset.Icc (1 : ℕ) M) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_Icc]
      by_cases hk0 : k = 0
      · exact Or.inl hk0
      · exact Or.inr ⟨by omega, Finset.le_sup (f := id) hk⟩
    have hnot0 : (0 : ℕ) ∉ Finset.Icc (1 : ℕ) M := by simp
    have hrhs : ((2 * ∑ k ∈ S, (b k : ℝ) * Real.cos ((k : ℝ) * x) : ℝ) : ℂ) =
        ∑ k ∈ insert 0 (Finset.Icc (1 : ℕ) M),
          if k ∈ S then ((2 * ((b k : ℝ) * Real.cos ((k : ℝ) * x)) : ℝ) : ℂ) else 0 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSsub]
      push_cast; rw [Finset.mul_sum]
    rw [hrhs, Finset.sum_insert hnot0]
    simp only [Nat.cast_zero]
  have hp_sum : (∑ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (p j : ℝ)) = 2 * (n : ℝ) := by
    have h0 := hp_eval 0
    simp only [eChar, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    have hg0 : g 0 = (n : ℝ) := by dsimp [g]; simp [← hsum]
    rw [hg0] at h0
    have hC : ((∑ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (p j : ℝ) : ℝ) : ℂ) = ((2 * (n : ℝ) : ℝ) : ℂ) := by
      push_cast; simpa using h0
    exact Complex.ofReal_injective hC
  -- Build sign-change TrigPoly T
  obtain ⟨T, hTev, hTsupp, hTtop, hTreal, hTl1⟩ := exists_sign_poly_tp (Finset.univ : Finset (Fin d)) t
  simp only [Finset.card_univ, Fintype.card_fin] at hTsupp hTtop hTl1
  let u : ℤ → ℝ := fun l => (T l).re
  have hu_supp : ∀ l : ℤ, ¬ (-(d : ℤ) ≤ l ∧ l ≤ (d : ℤ)) → u l = 0 := by
    intro l hl
    by_cases hmem : l ∈ T.support
    · exact absurd (hTsupp l hmem) hl
    · simp [u, Finsupp.notMem_support_iff.mp hmem]
  have hud : u (d : ℤ) = 1 := by simp [u, hTtop]
  have hu_l1 : ∑ l ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), |u l| ≤ (4 : ℝ) ^ d := by
    have hsub : T.support ⊆ Finset.Icc (-(d : ℤ)) (d : ℤ) := fun l hl => Finset.mem_Icc.mpr (hTsupp l hl)
    have heq : ∑ l ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), |u l| = T.sum fun _ c => ‖c‖ := by
      unfold Finsupp.sum
      symm
      refine Finset.sum_subset_zero_on_sdiff hsub (fun l hl => ?_) (fun l _ => ?_)
      · simp only [Finset.mem_sdiff, Finsupp.mem_support_iff, not_not] at hl
        simp [u, hl.2]
      · dsimp only
        have hEqC : T l = ((u l : ℝ) : ℂ) := Complex.ext rfl (by simp [hTreal l])
        conv_lhs => rw [hEqC]
        rw [Complex.norm_real, Real.norm_eq_abs]
    rw [heq]; exact hTl1
  -- Define β, v, δ, L, B₀, U
  let β : ℤ → ℤ := fun j => p (j - (P : ℤ)) - 2 * p j + p (j + (P : ℤ))
  let v : ℤ → ℝ := fun j => ∑ l ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), u l * (β (j - l) : ℝ)
  let δ : ℝ := (2 * (r.factorial : ℝ) * (8 : ℝ) ^ r)⁻¹
  let L : ℕ := 17 ^ r + 4 * r + 10 * P + 10
  let B₀ : ℕ := L + 1
  let U : ℝ := 8 * (4 : ℝ) ^ d
  let M' : ℕ := M + P + d
  have hβ_supp : ∀ j : ℤ, ((M + P : ℕ) : ℤ) < |j| → β j = 0 := by
    intro j hj
    have h1 : (M : ℤ) < |j - (P : ℤ)| := by
      rcases le_or_gt 0 j with h | h
      · rw [abs_of_nonneg h] at hj
        have hnn : 0 ≤ j - (P : ℤ) := by omega
        rw [abs_of_nonneg hnn]; omega
      · rw [abs_of_neg h] at hj
        have hnp : j - (P : ℤ) ≤ 0 := by omega
        rw [abs_of_nonpos hnp]; omega
    have h2 : (M : ℤ) < |j| := by omega
    have h3 : (M : ℤ) < |j + (P : ℤ)| := by
      rcases le_or_gt 0 j with h | h
      · rw [abs_of_nonneg h] at hj
        have hnn : 0 ≤ j + (P : ℤ) := by omega
        rw [abs_of_nonneg hnn]; omega
      · rw [abs_of_neg h] at hj
        have hnp : j + (P : ℤ) ≤ 0 := by omega
        rw [abs_of_nonpos hnp]; omega
    dsimp [β]; rw [hp_supp _ h1, hp_supp _ h2, hp_supp _ h3]; ring
  have hv_supp : ∀ j : ℤ, (M' : ℤ) < |j| → v j = 0 := by
    intro j hj
    dsimp [v]
    refine Finset.sum_eq_zero fun l hl => ?_
    simp only [Finset.mem_Icc] at hl
    have hjl : ((M + P : ℕ) : ℤ) < |j - l| := by
      rcases le_or_gt 0 j with h | h
      · rw [abs_of_nonneg h] at hj
        have : 0 ≤ j - l := by omega
        rw [abs_of_nonneg this]; omega
      · rw [abs_of_neg h] at hj
        have : j - l ≤ 0 := by omega
        rw [abs_of_nonpos this]; omega
    rw [hβ_supp _ hjl]; simp
  -- Evaluate F(x) = ∑_{j ∈ Icc (-M') M'} v j * eChar j x = 2g(x) * (2 cos(Px) - 2) * T(x)
  have hF_eval : ∀ x : ℝ, ∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x =
      ((2 * g x * (2 * Real.cos ((P : ℝ) * x) - 2) *
        ∏ i : Fin d, (2 * (Real.cos x - Real.cos (t i))) : ℝ) : ℂ) := by
    intro x
    have hcosP : ((2 * Real.cos ((P : ℝ) * x) - 2 : ℝ) : ℂ) =
        eChar (P : ℤ) x - 2 + eChar (-(P : ℤ)) x := by
      unfold eChar; push_cast; rw [Complex.cos]
      have h1 : Complex.I * (P : ℂ) * (x : ℂ) = ((P : ℂ) * (x : ℂ)) * Complex.I := by ring
      have h2 : Complex.I * -(P : ℂ) * (x : ℂ) = -(((P : ℂ) * (x : ℂ)) * Complex.I) := by ring
      rw [h1, h2]; ring
    have hβ_eval : ∑ j ∈ Finset.Icc (-((M + P : ℕ) : ℤ)) ((M + P : ℕ) : ℤ), (β j : ℂ) * eChar j x =
        ((2 * g x : ℝ) : ℂ) * ((2 * Real.cos ((P : ℝ) * x) - 2 : ℝ) : ℂ) := by
      rw [hcosP, ← hp_eval x]
      have hshift : ∀ (s : ℤ), |s| ≤ (P : ℤ) →
          ∑ j ∈ Finset.Icc (-((M + P : ℕ) : ℤ)) ((M + P : ℕ) : ℤ), (p (j + s) : ℂ) * eChar j x =
          (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (p k : ℂ) * eChar k x) * eChar (-s) x := by
        intro s hs
        rw [Finset.sum_mul]
        have hsub : Finset.Icc (-(M : ℤ)) (M : ℤ) ⊆
            (Finset.Icc (-((M + P : ℕ) : ℤ)) ((M + P : ℕ) : ℤ)).image (fun j => j + s) := by
          intro k hk
          simp only [Finset.mem_Icc, Finset.mem_image] at hk ⊢
          rw [abs_le] at hs
          exact ⟨k - s, ⟨by omega, by omega⟩, by omega⟩
        have h1 : ∑ j ∈ Finset.Icc (-((M + P : ℕ) : ℤ)) ((M + P : ℕ) : ℤ), (p (j + s) : ℂ) * eChar j x =
            ∑ k ∈ (Finset.Icc (-((M + P : ℕ) : ℤ)) ((M + P : ℕ) : ℤ)).image (fun j => j + s),
              (p k : ℂ) * (eChar k x * eChar (-s) x) := by
          rw [Finset.sum_image (fun a _ b _ h => by omega)]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← eChar_add]; congr 2; ring
        rw [h1]
        symm
        refine Finset.sum_subset_zero_on_sdiff hsub (fun k hk => ?_) (fun k _ => by ring)
        simp only [Finset.mem_sdiff, Finset.mem_Icc] at hk
        have hgt : (M : ℤ) < |k| := by
          rcases le_or_gt 0 k with h | h
          · rw [abs_of_nonneg h]; omega
          · rw [abs_of_neg h]; omega
        rw [hp_supp k hgt]; simp
      have hβ_split : ∑ j ∈ Finset.Icc (-((M + P : ℕ) : ℤ)) ((M + P : ℕ) : ℤ), (β j : ℂ) * eChar j x =
          (∑ j ∈ Finset.Icc (-((M + P : ℕ) : ℤ)) ((M + P : ℕ) : ℤ), (p (j - (P : ℤ)) : ℂ) * eChar j x) -
          2 * (∑ j ∈ Finset.Icc (-((M + P : ℕ) : ℤ)) ((M + P : ℕ) : ℤ), (p j : ℂ) * eChar j x) +
          (∑ j ∈ Finset.Icc (-((M + P : ℕ) : ℤ)) ((M + P : ℕ) : ℤ), (p (j + (P : ℤ)) : ℂ) * eChar j x) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by dsimp [β]; push_cast; ring
      rw [hβ_split]
      have hA := hshift (-(P : ℤ)) (by simp)
      have hB := hshift 0 (by simp)
      have hC := hshift (P : ℤ) (by simp)
      simp only [sub_eq_add_neg, neg_neg, add_zero, neg_zero, eChar_zero, mul_one] at hA hB hC ⊢
      rw [hA, hB, hC]; ring
    have hT_sum : ((∏ i : Fin d, (2 * (Real.cos x - Real.cos (t i))) : ℝ) : ℂ) =
        ∑ l ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), (u l : ℂ) * eChar l x := by
      rw [← hTev]
      unfold evalTP Finsupp.sum
      refine Finset.sum_subset_zero_on_sdiff (fun l hl => Finset.mem_Icc.mpr (hTsupp l hl))
        (fun l hl => ?_) (fun l _ => ?_)
      · simp only [Finset.mem_sdiff, Finsupp.mem_support_iff, not_not] at hl
        simp [u, hl.2]
      · have hEqC : T l = ((u l : ℝ) : ℂ) := Complex.ext rfl (by simp [hTreal l])
        rw [hEqC]
    rw [show ((2 * g x * (2 * Real.cos ((P : ℝ) * x) - 2) *
        ∏ i : Fin d, (2 * (Real.cos x - Real.cos (t i))) : ℝ) : ℂ) =
      (((2 * g x : ℝ) : ℂ) * ((2 * Real.cos ((P : ℝ) * x) - 2 : ℝ) : ℂ)) *
        ((∏ i : Fin d, (2 * (Real.cos x - Real.cos (t i))) : ℝ) : ℂ) by push_cast; ring]
    rw [← hβ_eval, hT_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    -- Reindex k + l = j
    have hv_expand : ∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x =
        ∑ l ∈ Finset.Icc (-(d : ℤ)) (d : ℤ),
          ∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (u l : ℂ) * (β (j - l) : ℂ) * eChar j x := by
      simp_rw [v, Complex.ofReal_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by push_cast; ring
    rw [hv_expand]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [Finset.mem_Icc] at hl
    have hsub : Finset.Icc (-((M + P : ℕ) : ℤ)) ((M + P : ℕ) : ℤ) ⊆
        (Finset.Icc (-(M' : ℤ)) (M' : ℤ)).image (fun j => j - l) := by
      intro k hk
      simp only [Finset.mem_Icc, Finset.mem_image] at hk ⊢
      exact ⟨k + l, ⟨by omega, by omega⟩, by omega⟩
    have h1 : ∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (u l : ℂ) * (β (j - l) : ℂ) * eChar j x =
        ∑ k ∈ (Finset.Icc (-(M' : ℤ)) (M' : ℤ)).image (fun j => j - l),
          (β k : ℂ) * eChar k x * ((u l : ℂ) * eChar l x) := by
      rw [Finset.sum_image (fun a _ b _ h => by omega)]
      refine Finset.sum_congr rfl fun j _ => ?_
      have he : eChar j x = eChar (j - l) x * eChar l x := by rw [← eChar_add]; congr 1; ring
      rw [he]; ring
    rw [h1]
    symm
    refine Finset.sum_subset_zero_on_sdiff hsub (fun k hk => ?_) (fun _ _ => rfl)
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hk
    have hgt : ((M + P : ℕ) : ℤ) < |k| := by
      rcases le_or_gt 0 k with h | h
      · rw [abs_of_nonneg h]; omega
      · rw [abs_of_neg h]; omega
    rw [hβ_supp k hgt]; simp
  -- Constant-sign L1 bound: ‖F‖_1 ≤ U = 8 * 4^d
  have hF_l1 : circleIntR (fun x => ‖∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x‖) ≤ U := by
    have hF_np : ∀ x : ℝ, (∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x) =
        ((2 * g x * (2 * Real.cos ((P : ℝ) * x) - 2) *
          ∏ i : Fin d, (2 * (Real.cos x - Real.cos (t i))) : ℝ) : ℂ) ∧
        2 * g x * (2 * Real.cos ((P : ℝ) * x) - 2) *
          ∏ i : Fin d, (2 * (Real.cos x - Real.cos (t i))) ≤ 0 := by
      intro x
      refine ⟨hF_eval x, ?_⟩
      have h1 := hprod_nonneg x
      have h2 : 2 * Real.cos ((P : ℝ) * x) - 2 ≤ 0 := by linarith [Real.cos_le_one ((P : ℝ) * x)]
      have hmul : 2 * g x * (2 * Real.cos ((P : ℝ) * x) - 2) *
          ∏ i : Fin d, (2 * (Real.cos x - Real.cos (t i))) =
          (2 * (2 * Real.cos ((P : ℝ) * x) - 2)) *
          (g x * ∏ i : Fin d, (2 * (Real.cos x - Real.cos (t i)))) := by ring
      rw [hmul]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) h1
    have hnorm_eq : (fun x => ‖∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x‖) =
        fun x => -(∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x).re := by
      ext x
      rw [(hF_np x).1, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs,
        abs_of_nonpos (hF_np x).2]
    rw [hnorm_eq]
    have hcontF : Continuous (fun x => ∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x) :=
      continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_eChar j)
    have hneg_int : circleIntR (fun x => -(∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x).re) =
        -(circleInt (fun x => ∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x)).re := by
      rw [circleInt_re _ hcontF]
      have h1 := circleIntR_const_mul (-1) (fun x => (∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x).re)
      simpa only [neg_one_mul] using h1
    rw [hneg_int]
    have hint0 : circleInt (fun x => ∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x) = (v 0 : ℂ) := by
      rw [circleInt_finset_sum (Finset.Icc (-(M' : ℤ)) (M' : ℤ)) (fun j x => (v j : ℂ) * eChar j x)
        (fun j _ => continuous_const.mul (continuous_eChar j))]
      simp_rw [circleInt_const_mul, circleInt_eChar, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j _ hj; simp [hj]
      · intro h; exfalso; apply h; simp only [Finset.mem_Icc]; omega
    rw [hint0, Complex.ofReal_re]
    have hv0_le : |v 0| ≤ U := by
      dsimp [v, U]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ l ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), |u l * (β (0 - l) : ℝ)| ≤ 8 * |u l| := by
        intro l _
        rw [abs_mul]
        have hβ8 : |(β (0 - l) : ℝ)| ≤ 8 := by
          have h1 := hp0 (0 - l - P); have h2 := hp4 (0 - l - P)
          have h3 := hp0 (0 - l); have h4 := hp4 (0 - l)
          have h5 := hp0 (0 - l + P); have h6 := hp4 (0 - l + P)
          have : |β (0 - l)| ≤ 8 := by dsimp [β]; rw [abs_le]; constructor <;> omega
          exact_mod_cast this
        nlinarith [abs_nonneg (u l)]
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum]
      linarith [hu_l1]
    linarith [neg_le_abs (v 0)]
  -- Step 3: Count q = #{j ∈ [-M', M'] | v j ≠ 0} and m = #{j ∈ [-M', M'] | β j ≠ 0}
  let Vsupp := (Finset.Icc (-(M' : ℤ)) (M' : ℤ)).filter (fun j => v j ≠ 0)
  let q : ℕ := Vsupp.card
  let s : ℕ := q / B₀
  have hlog_q : Real.log ((q : ℝ) + 1) ≤ Real.log (B₀ : ℝ) + 400 * U * (B₀ : ℝ) / δ := by
    have hsmall_v := small_interval_bound d p hp0 hp4 u hu_supp hud
    have hlog_s : Real.log ((s : ℝ) + 1) ≤ 400 * U * (B₀ : ℝ) / δ := by
      let emb : Fin q ↪o ℤ := Vsupp.orderEmbOfFin rfl
      have hF_emb : (fun x => ∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x) =
          fun x => ∑ i : Fin q, (v (emb i) : ℂ) * eChar (emb i) x := by
        ext x
        have h1 : ∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x =
            ∑ j ∈ Vsupp, (v j : ℂ) * eChar j x := by
          symm
          refine Finset.sum_subset (Finset.filter_subset _ _) fun j hj hnot => ?_
          simp only [Vsupp, Finset.mem_filter, not_and, not_not] at hnot
          rw [hnot hj]; simp
        rw [h1]
        symm
        refine Finset.sum_bij (fun (i : Fin q) _ => emb i) ?_ ?_ ?_ ?_
        · intro i _; exact Finset.orderEmbOfFin_mem Vsupp rfl i
        · intro a _ b _ h; exact emb.injective h
        · intro j hj
          have hrng := Finset.range_orderEmbOfFin Vsupp rfl
          have : j ∈ Set.range emb := by rw [hrng]; exact hj
          obtain ⟨i, rfl⟩ := this
          exact ⟨i, Finset.mem_univ _, rfl⟩
        · intro i _; rfl
      have hmps := mps_littlewood emb emb.strictMono (fun i => (v (emb i) : ℂ))
      have hnormF : (fun x => ‖∑ i : Fin q, (v (emb i) : ℂ) * eChar (emb i) x‖) =
          fun x => ‖∑ j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ), (v j : ℂ) * eChar j x‖ := by
        ext x; rw [← congrFun hF_emb x]
      rw [hnormF] at hmps
      have hmps_le : (1 / 400 : ℝ) * (∑ i : Fin q, |v (emb i)| / ((i.val : ℝ) + 1)) ≤ U := by
        have hnorm : ∀ i : Fin q, ‖(v (emb i) : ℂ)‖ = |v (emb i)| := fun i => by
          rw [Complex.norm_real, Real.norm_eq_abs]
        simp_rw [hnorm] at hmps
        exact hmps.trans hF_l1
      -- Each consecutive block of B₀ = L + 1 elements in emb contains an index with |v| ≥ δ
      have hblock_big : ∀ k : ℕ, k < s →
          ∃ i : Fin q, k * B₀ ≤ i.val ∧ i.val < (k + 1) * B₀ ∧ δ ≤ |v (emb i)| := by
        intro k hk
        have hhi : k * B₀ + L < q := by
          have h1 : (k + 1) * B₀ ≤ s * B₀ := Nat.mul_le_mul_right B₀ (by omega)
          have h2 : s * B₀ ≤ q := Nat.div_mul_le_self q B₀
          have h3 : (k + 1) * B₀ = k * B₀ + B₀ := by ring
          have h4 : B₀ = L + 1 := rfl
          omega
        have hB0_eq : B₀ = L + 1 := rfl
        have hkB0_lt : k * B₀ < q := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hhi
        let A0 : ℤ := emb ⟨k * B₀, hkB0_lt⟩
        let B1 : ℤ := emb ⟨k * B₀ + L, hhi⟩
        by_contra hall
        push Not at hall
        have hsmall_blk : ∀ j ∈ Finset.Icc A0 B1, |v j| < δ := by
          intro j hj
          by_cases hvj : v j = 0
          · rw [hvj, abs_zero]; dsimp [δ]; positivity
          · have hjIcc : j ∈ Finset.Icc (-(M' : ℤ)) (M' : ℤ) := by
              have h1 := (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem Vsupp rfl ⟨k * B₀, hkB0_lt⟩)).1
              have h2 := (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem Vsupp rfl ⟨k * B₀ + L, hhi⟩)).1
              simp only [Finset.mem_Icc] at h1 h2 hj ⊢
              dsimp only [A0, B1, emb] at hj
              omega
            have hjV : j ∈ Vsupp := Finset.mem_filter.mpr ⟨hjIcc, hvj⟩
            have hrng := Finset.range_orderEmbOfFin Vsupp rfl
            have : j ∈ Set.range emb := by rw [hrng]; exact hjV
            obtain ⟨i, rfl⟩ := this
            have hi1 : k * B₀ ≤ i.val := by
              have := emb.le_iff_le.mp (Finset.mem_Icc.mp hj).1
              exact Fin.le_def.mp this
            have hi2 : i.val ≤ k * B₀ + L := by
              have := emb.le_iff_le.mp (Finset.mem_Icc.mp hj).2
              exact Fin.le_def.mp this
            have hi3 : i.val < (k + 1) * B₀ := by
              have hmul : (k + 1) * B₀ = k * B₀ + B₀ := by ring
              omega
            exact hall i hi1 hi3
        have hcard_le := (hsmall_v A0 B1 hsmall_blk).2
        have hcard_ge : B₀ ≤ ((Finset.Icc A0 B1).filter (fun j => v j ≠ 0)).card := by
          have hinj : (Finset.range B₀).card ≤ ((Finset.Icc A0 B1).filter (fun j => v j ≠ 0)).card := by
            refine Finset.card_le_card_of_injOn (fun t => if ht : t < B₀ then emb ⟨k * B₀ + t, by omega⟩ else 0) ?_ ?_
            · intro t ht
              have htB : t < B₀ := Finset.mem_range.mp ht
              simp only [dif_pos htB]
              have hmem := Finset.orderEmbOfFin_mem Vsupp rfl ⟨k * B₀ + t, by omega⟩
              refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩,
                (Finset.mem_filter.mp hmem).2⟩)
              · exact emb.monotone (Fin.le_def.mpr (by dsimp only; omega))
              · exact emb.monotone (Fin.le_def.mpr (by dsimp only; omega))
            · intro t1 ht1 t2 ht2 h
              have ht1B : t1 < B₀ := Finset.mem_range.mp ht1
              have ht2B : t2 < B₀ := Finset.mem_range.mp ht2
              simp only [dif_pos ht1B, dif_pos ht2B] at h
              have := congrArg Fin.val (emb.injective h)
              dsimp only at this; omega
          simpa using hinj
        have hcard_le' : ((Finset.Icc A0 B1).filter (fun j => v j ≠ 0)).card ≤ L := hcard_le
        omega
      choose idx hidx_lo hidx_hi hidx_big using fun (k : Fin s) => hblock_big k.val k.isLt
      have hidx_inj : Function.Injective idx := by
        intro k1 k2 heq
        by_contra hne
        have h1lo := hidx_lo k1; have h1hi := hidx_hi k1
        have h2lo := hidx_lo k2; have h2hi := hidx_hi k2
        rw [heq] at h1lo h1hi
        rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
        · have : (k1.val + 1) * B₀ ≤ k2.val * B₀ := Nat.mul_le_mul_right B₀ (by omega)
          omega
        · have : (k2.val + 1) * B₀ ≤ k1.val * B₀ := Nat.mul_le_mul_right B₀ (by omega)
          omega
      have hsum_ge : (δ / (B₀ : ℝ)) * (∑ k ∈ Finset.range s, ((k : ℝ) + 1)⁻¹) ≤
          ∑ i : Fin q, |v (emb i)| / ((i.val : ℝ) + 1) := by
        have hsub : (Finset.univ : Finset (Fin s)).image idx ⊆ Finset.univ := Finset.subset_univ _
        refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
        rw [Finset.sum_image (fun a _ b _ h => hidx_inj h), Finset.mul_sum,
          ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_le_sum fun k _ => ?_
        have hden_le : ((idx k).val : ℝ) + 1 ≤ ((k.val : ℝ) + 1) * (B₀ : ℝ) := by
          have : (idx k).val + 1 ≤ (k.val + 1) * B₀ := by have := hidx_hi k; omega
          exact_mod_cast this
        have hden_pos : (0 : ℝ) < ((idx k).val : ℝ) + 1 := by positivity
        have hB0_pos : (0 : ℝ) < (B₀ : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos L)
        calc (δ / (B₀ : ℝ)) * ((k.val : ℝ) + 1)⁻¹
            = δ / (((k.val : ℝ) + 1) * (B₀ : ℝ)) := by rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring
          _ ≤ δ / (((idx k).val : ℝ) + 1) :=
              div_le_div_of_nonneg_left (by dsimp [δ]; positivity) hden_pos hden_le
          _ ≤ |v (emb (idx k))| / (((idx k).val : ℝ) + 1) :=
              div_le_div_of_nonneg_right (hidx_big k) hden_pos.le
      have hharm := log_add_one_le_harmonic s
      have hδ_pos : 0 < δ := by dsimp [δ]; positivity
      have hB0_pos : (0 : ℝ) < (B₀ : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos L)
      have h1 : (δ / (400 * (B₀ : ℝ))) * Real.log ((s : ℝ) + 1) ≤ U := by
        calc (δ / (400 * (B₀ : ℝ))) * Real.log ((s : ℝ) + 1)
            ≤ (δ / (400 * (B₀ : ℝ))) * ∑ k ∈ Finset.range s, ((k : ℝ) + 1)⁻¹ :=
              mul_le_mul_of_nonneg_left hharm (div_nonneg hδ_pos.le (by linarith))
          _ = (1 / 400 : ℝ) * ((δ / (B₀ : ℝ)) * ∑ k ∈ Finset.range s, ((k : ℝ) + 1)⁻¹) := by ring
          _ ≤ (1 / 400 : ℝ) * ∑ i : Fin q, |v (emb i)| / ((i.val : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left hsum_ge (by norm_num)
          _ ≤ U := hmps_le
      rw [le_div_iff₀ hδ_pos]
      have h2 := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ 400 * (B₀ : ℝ) by linarith)
      have hsimp : (δ / (400 * (B₀ : ℝ))) * Real.log ((s : ℝ) + 1) * (400 * (B₀ : ℝ)) =
          Real.log ((s : ℝ) + 1) * δ := by field_simp [hB0_pos.ne']
      linarith
    have hq_le : ((q : ℝ) + 1) ≤ (B₀ : ℝ) * ((s : ℝ) + 1) := by
      have h1 : q + 1 ≤ B₀ * (s + 1) := by
        have hB0_pos : 0 < B₀ := Nat.succ_pos L
        have hdiv := Nat.div_add_mod q B₀
        have hmod := Nat.mod_lt q hB0_pos
        dsimp only [s] at *
        nlinarith
      exact_mod_cast h1
    have hB0_posR : (0 : ℝ) < (B₀ : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos L)
    have hq1_pos : (0 : ℝ) < (q : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg q) zero_lt_one
    have hs1_pos : (0 : ℝ) < (s : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg s) zero_lt_one
    calc Real.log ((q : ℝ) + 1)
        ≤ Real.log ((B₀ : ℝ) * ((s : ℝ) + 1)) := Real.log_le_log hq1_pos hq_le
      _ = Real.log (B₀ : ℝ) + Real.log ((s : ℝ) + 1) := Real.log_mul hB0_posR.ne' hs1_pos.ne'
      _ ≤ Real.log (B₀ : ℝ) + 400 * U * (B₀ : ℝ) / δ := by linarith
  -- Count m = #{j ∈ [-M', M'] | β j ≠ 0} < (q + 1) * B₀
  let Bsupp := (Finset.Icc (-(M' : ℤ)) (M' : ℤ)).filter (fun j => β j ≠ 0)
  let m : ℕ := Bsupp.card
  have hm_le : m + 1 ≤ (q + 1) * B₀ := by
    have hbad_le : ((Finset.Icc (-(M' : ℤ)) (M' : ℤ)).filter (fun j => δ ≤ |v j|)).card ≤ q := by
      refine Finset.card_le_card fun j hj => ?_
      simp only [Vsupp, Finset.mem_filter] at hj ⊢
      refine ⟨hj.1, fun hv0 => ?_⟩
      rw [hv0, abs_zero] at hj
      have hδ_pos : 0 < δ := by dsimp [δ]; positivity
      linarith [hj.2]
    have hm_bound := card_filter_le_of_small_between L (fun j => δ ≤ |v j|) (fun j => β j ≠ 0)
      (fun A B hno => (small_interval_bound d p hp0 hp4 u hu_supp hud A B (fun j hj => by
        have := hno j hj; push Not at this; exact this)).1)
      q (-(M' : ℤ)) (M' : ℤ) hbad_le
    dsimp [m, Bsupp, B₀] at *; nlinarith
  -- Step 4: Fejer multiplier H(x) = 2g(x) * |(1/P) ∑_{s<P} e^{isx}|^2
  let τ : ℤ → ℝ := fun j => if |j| ≤ (P : ℤ) then ((P : ℝ) - ((|j| : ℤ) : ℝ)) / (P : ℝ) ^ 2 else 0
  let h : ℤ → ℝ := fun j => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (p k : ℝ) * τ (j - k)
  let N : ℕ := M + P
  have hτ_nn : ∀ j, 0 ≤ τ j := by
    intro j; dsimp [τ]; split_ifs with hle
    · have : ((|j| : ℤ) : ℝ) ≤ (P : ℝ) := by exact_mod_cast hle
      exact div_nonneg (by linarith) (sq_nonneg _)
    · exact le_rfl
  have hτ_sum : ∑ j ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), τ j = 1 := by
    have h0 := fejer_kernel_eval P hP1 0
    have hPc : (P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : P ≠ 0)
    simp only [eChar, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, inv_mul_cancel₀ hPc,
      norm_one, one_pow] at h0
    have hEq : ∑ j ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), (τ j : ℂ) = 1 := by
      have hcongr : ∑ j ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), (τ j : ℂ) =
          ∑ j ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), (((P : ℝ) - |(j : ℝ)|) / (P : ℝ) ^ 2 : ℂ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_Icc] at hj
        have hle : |j| ≤ (P : ℤ) := abs_le.mpr hj
        simp [τ, hle, Int.cast_abs]
      rw [hcongr]
      simpa using h0.symm
    have hEqR : ((∑ j ∈ Finset.Icc (-(P : ℤ)) (P : ℤ), τ j : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast; exact hEq
    exact Complex.ofReal_injective hEqR
  have hh0 : ∀ j, 0 ≤ h j := fun j => Finset.sum_nonneg fun k _ => mul_nonneg (by exact_mod_cast hp0 k) (hτ_nn _)
  have hh4 : ∀ j, h j ≤ 4 := by
    intro j
    dsimp [h]
    have hle1 : ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (p k : ℝ) * τ (j - k) ≤
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), 4 * τ (j - k) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hp4 k) (hτ_nn _)
    refine hle1.trans ?_
    rw [← Finset.mul_sum]
    have hsum_le1 : ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), τ (j - k) ≤ 1 := by
      rw [← hτ_sum]
      have hreidx : ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), τ (j - k) =
          ∑ r ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).image (fun k => j - k), τ r :=
        (Finset.sum_image (fun a _ b _ heq => by omega)).symm
      rw [hreidx]
      have hsub : ((Finset.Icc (-(M : ℤ)) (M : ℤ)).image (fun k => j - k)).filter (fun r => |r| ≤ (P : ℤ)) ⊆
          Finset.Icc (-(P : ℤ)) (P : ℤ) := fun r hr =>
        Finset.mem_Icc.mpr (abs_le.mp (Finset.mem_filter.mp hr).2)
      have hfilt : ∑ r ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).image (fun k => j - k), τ r =
          ∑ r ∈ ((Finset.Icc (-(M : ℤ)) (M : ℤ)).image (fun k => j - k)).filter (fun r => |r| ≤ (P : ℤ)), τ r := by
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun r hr hnot => ?_
        simp only [Finset.mem_filter] at hnot
        have : ¬ |r| ≤ (P : ℤ) := fun hle => hnot ⟨hr, hle⟩
        simp [τ, this]
      rw [hfilt]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hτ_nn _
    linarith
  have hh_int : ∀ j : ℤ, ∃ z : ℤ, h j = (z : ℝ) / (P : ℝ) ^ 2 := by
    intro j
    let z : ℤ := ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      p k * (if |j - k| ≤ (P : ℤ) then (P : ℤ) - |j - k| else 0)
    refine ⟨z, ?_⟩
    dsimp [h, τ, z]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> [push_cast; simp] <;> ring
  have hh_even : ∀ j : ℤ, h (-j) = h j := by
    intro j
    dsimp [h]
    refine Finset.sum_nbij (fun k => -k) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro a _ b _ heq; exact neg_injective heq
    · intro k hk; simp only [Finset.mem_coe, Finset.mem_Icc] at hk ⊢
      exact ⟨-k, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), by simp⟩
    · intro k _
      rw [hp_even]
      congr 1
      dsimp [τ]
      rw [show -j - k = -(j - -k) by ring, abs_neg]
  have hh_supp : ∀ j : ℤ, (N : ℤ) < |j| → h j = 0 := by
    intro j hj
    dsimp [h, τ]
    refine Finset.sum_eq_zero fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    have hgt : ¬ |j - k| ≤ (P : ℤ) := by
      rcases le_or_gt 0 j with h | h
      · rw [abs_of_nonneg h] at hj
        have : 0 ≤ j - k := by dsimp [N] at hj; omega
        rw [abs_of_nonneg this]; dsimp [N] at hj; omega
      · rw [abs_of_neg h] at hj
        have : j - k ≤ 0 := by dsimp [N] at hj; omega
        rw [abs_of_nonpos this]; dsimp [N] at hj; omega
    rw [if_neg hgt, mul_zero]
  have hh_diff2 : ∀ j : ℤ, h (j - 1) - 2 * h j + h (j + 1) = (β j : ℝ) / (P : ℝ) ^ 2 := by
    intro j
    dsimp [h]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    have hterm : ∀ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        (p k : ℝ) * τ (j - 1 - k) - 2 * ((p k : ℝ) * τ (j - k)) + (p k : ℝ) * τ (j + 1 - k) =
        (p k : ℝ) * (((if j - k = (P : ℤ) then (1 : ℝ) else 0) +
          (if j - k = -(P : ℤ) then (1 : ℝ) else 0) -
          (if j - k = 0 then (2 : ℝ) else 0)) / (P : ℝ) ^ 2) := by
      intro k _
      have h1 := fejer_second_diff P hP1 (j - k)
      have he1 : j - 1 - k = (j - k) - 1 := by ring
      have he2 : j + 1 - k = (j - k) + 1 := by ring
      rw [he1, he2]
      calc (p k : ℝ) * τ (j - k - 1) - 2 * ((p k : ℝ) * τ (j - k)) + (p k : ℝ) * τ (j - k + 1)
          = (p k : ℝ) * (τ (j - k - 1) - 2 * τ (j - k) + τ (j - k + 1)) := by ring
        _ = _ := by rw [h1]
    rw [Finset.sum_congr rfl hterm]
    have hsplit_sum : ∀ (c : ℤ),
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (p k : ℝ) * (if j - k = c then (1 : ℝ) else 0) =
        (p (j - c) : ℝ) := by
      intro c
      by_cases hmem : j - c ∈ Finset.Icc (-(M : ℤ)) (M : ℤ)
      · rw [Finset.sum_eq_single (j - c)]
        · simp
        · intro k _ hk; rw [if_neg (by omega), mul_zero]
        · intro h; exact absurd hmem h
      · rw [Finset.sum_eq_zero]
        · simp only [Finset.mem_Icc] at hmem
          have hgt : (M : ℤ) < |j - c| := by
            rcases le_or_gt 0 (j - c) with h | h
            · rw [abs_of_nonneg h]; omega
            · rw [abs_of_neg h]; omega
          rw [hp_supp _ hgt]; simp
        · intro k hk
          have hne : j - k ≠ c := fun h => hmem (by rw [show j - c = k by omega]; exact hk)
          rw [if_neg hne, mul_zero]
    have hrewrite : ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          (p k : ℝ) * (((if j - k = (P : ℤ) then (1 : ℝ) else 0) +
            (if j - k = -(P : ℤ) then (1 : ℝ) else 0) -
            (if j - k = 0 then (2 : ℝ) else 0)) / (P : ℝ) ^ 2) =
        ((∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (p k : ℝ) * (if j - k = (P : ℤ) then (1 : ℝ) else 0)) +
         (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (p k : ℝ) * (if j - k = -(P : ℤ) then (1 : ℝ) else 0)) -
         2 * (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (p k : ℝ) * (if j - k = 0 then (1 : ℝ) else 0))) /
          (P : ℝ) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => by split_ifs <;> ring
    rw [hrewrite, hsplit_sum (P : ℤ), hsplit_sum (-(P : ℤ)), hsplit_sum 0]
    simp only [sub_neg_eq_add, sub_zero]
    dsimp [β]; push_cast; ring
  -- Evaluate H(x) = ∑_{j ∈ [-N, N]} h j * eChar j x = 2 g(x) * |(1/P) ∑_{s<P} e^{isx}|^2
  let H : ℝ → ℝ := fun x =>
    2 * g x * (‖((P : ℂ)⁻¹ * ∑ s ∈ Finset.range P, eChar (s : ℤ) x)‖ ^ 2)
  have hH_eval : ∀ x : ℝ, ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (h j : ℂ) * eChar j x = (H x : ℂ) := by
    intro x
    dsimp [H]
    rw [Complex.ofReal_mul, ← hp_eval x, fejer_kernel_eval P hP1 x, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    have h1 : ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (h j : ℂ) * eChar j x =
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (p k : ℂ) * (τ (j - k) : ℂ) * eChar j x := by
      simp_rw [h, Complex.ofReal_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by push_cast; ring
    rw [h1]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    have hsub : Finset.Icc (-(P : ℤ)) (P : ℤ) ⊆
        (Finset.Icc (-(N : ℤ)) (N : ℤ)).image (fun j => j - k) := by
      intro r hr
      simp only [Finset.mem_Icc, Finset.mem_image] at hr ⊢
      exact ⟨r + k, ⟨by dsimp [N]; omega, by dsimp [N]; omega⟩, by omega⟩
    have h2 : ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (p k : ℂ) * (τ (j - k) : ℂ) * eChar j x =
        ∑ r ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).image (fun j => j - k),
          (p k : ℂ) * eChar k x * ((τ r : ℂ) * eChar r x) := by
      rw [Finset.sum_image (fun a _ b _ heq => by omega)]
      refine Finset.sum_congr rfl fun j _ => ?_
      have he : eChar j x = eChar k x * eChar (j - k) x := by rw [← eChar_add]; congr 1; ring
      rw [he]; ring
    rw [h2]
    symm
    refine Finset.sum_subset_zero_on_sdiff hsub (fun r hr => ?_) (fun r hr => ?_)
    · simp only [Finset.mem_sdiff, Finset.mem_Icc] at hr
      have hgt : ¬ |r| ≤ (P : ℤ) := by
        intro hle; rw [abs_le] at hle; exact hr.2 hle
      simp [τ, hgt]
    · simp only [Finset.mem_Icc] at hr
      have hle : |r| ≤ (P : ℤ) := abs_le.mpr hr
      simp [τ, hle]
  -- Lower bound on ‖H‖_1 via MPS
  have hH_lower : (1 / (400 * (P : ℝ) ^ 2)) * Real.log (1 + (n : ℝ) / 2) ≤
      circleIntR (fun x => |H x|) := by
    have hh_sum : ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), h j = 2 * (n : ℝ) := by
      have h0 := hH_eval 0
      have hPc : (P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : P ≠ 0)
      simp only [eChar, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, H,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        inv_mul_cancel₀ hPc, norm_one, one_pow] at h0
      have hg0 : g 0 = (n : ℝ) := by dsimp [g]; simp [← hsum]
      rw [hg0] at h0
      have hEq : ((∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), h j : ℝ) : ℂ) = ((2 * (n : ℝ) : ℝ) : ℂ) := by
        push_cast; simpa using h0
      exact Complex.ofReal_injective hEq
    let Hsupp := (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun j => h j ≠ 0)
    have hHcard : (n : ℝ) / 2 ≤ (Hsupp.card : ℝ) := by
      have h1 : 2 * (n : ℝ) = ∑ j ∈ Hsupp, h j := by
        rw [← hh_sum]
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun j hj hnot => ?_
        simp only [Hsupp, Finset.mem_filter, not_and, not_not] at hnot
        exact hnot hj
      have h2 : ∑ j ∈ Hsupp, h j ≤ 4 * (Hsupp.card : ℝ) := by
        refine (Finset.sum_le_sum fun j _ => hh4 j).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul]; ring_nf; rfl
      linarith
    let embH : Fin Hsupp.card ↪o ℤ := Hsupp.orderEmbOfFin rfl
    have hHeval_emb : ∀ x : ℝ, (H x : ℂ) = ∑ i : Fin Hsupp.card, (h (embH i) : ℂ) * eChar (embH i) x := by
      intro x
      rw [← hH_eval x]
      have h1 : ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (h j : ℂ) * eChar j x =
          ∑ j ∈ Hsupp, (h j : ℂ) * eChar j x := by
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun j hj hnot => ?_
        simp only [Hsupp, Finset.mem_filter, not_and, not_not] at hnot
        rw [hnot hj]; simp
      rw [h1]
      symm
      refine Finset.sum_bij (fun (i : Fin Hsupp.card) _ => embH i) ?_ ?_ ?_ ?_
      · intro i _; exact Finset.orderEmbOfFin_mem Hsupp rfl i
      · intro a _ b _ h; exact embH.injective h
      · intro j hj
        have hrng := Finset.range_orderEmbOfFin Hsupp rfl
        have : j ∈ Set.range embH := by rw [hrng]; exact hj
        obtain ⟨i, rfl⟩ := this
        exact ⟨i, Finset.mem_univ _, rfl⟩
      · intro i _; rfl
    have hmps := mps_littlewood embH embH.strictMono (fun i => (h (embH i) : ℂ))
    have hnorm_H : (fun x => ‖∑ i : Fin Hsupp.card, (h (embH i) : ℂ) * eChar (embH i) x‖) =
        fun x => |H x| := by
      ext x; rw [← hHeval_emb x, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm_H] at hmps
    have hcoeff_ge : ∀ i : Fin Hsupp.card, ((P : ℝ) ^ 2)⁻¹ ≤ ‖(h (embH i) : ℂ)‖ := by
      intro i
      have hne : h (embH i) ≠ 0 := (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem Hsupp rfl i)).2
      obtain ⟨z, hz⟩ := hh_int (embH i)
      have hz_ne : z ≠ 0 := fun h0 => hne (by rw [hz, h0, Int.cast_zero, zero_div])
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hh0 _), hz, inv_eq_one_div]
      refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
      have hz_pos : (0 : ℝ) < (z : ℝ) := by
        have hnn : 0 ≤ h (embH i) := hh0 _
        rw [hz] at hnn
        have hP2 : (0 : ℝ) < (P : ℝ) ^ 2 := by positivity
        have hznn : (0 : ℝ) ≤ (z : ℝ) := (div_nonneg_iff.mp hnn).resolve_right (fun h => by linarith [h.2]) |>.1
        exact lt_of_le_of_ne hznn (by exact_mod_cast hz_ne.symm)
      have : (1 : ℤ) ≤ z := by
        have : (0 : ℤ) < z := by exact_mod_cast hz_pos
        omega
      exact_mod_cast this
    have hsum_ge : ((P : ℝ) ^ 2)⁻¹ * Real.log (1 + (n : ℝ) / 2) ≤
        ∑ i : Fin Hsupp.card, ‖(h (embH i) : ℂ)‖ / ((i.val : ℝ) + 1) := by
      calc ((P : ℝ) ^ 2)⁻¹ * Real.log (1 + (n : ℝ) / 2)
          ≤ ((P : ℝ) ^ 2)⁻¹ * Real.log ((Hsupp.card : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) (by positivity)
        _ ≤ ((P : ℝ) ^ 2)⁻¹ * ∑ k ∈ Finset.range Hsupp.card, ((k : ℝ) + 1)⁻¹ :=
            mul_le_mul_of_nonneg_left (log_add_one_le_harmonic Hsupp.card) (by positivity)
        _ = ∑ i : Fin Hsupp.card, ((P : ℝ) ^ 2)⁻¹ / ((i.val : ℝ) + 1) := by
            rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
        _ ≤ ∑ i : Fin Hsupp.card, ‖(h (embH i) : ℂ)‖ / ((i.val : ℝ) + 1) :=
            Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right (hcoeff_ge i) (by positivity)
    calc (1 / (400 * (P : ℝ) ^ 2)) * Real.log (1 + (n : ℝ) / 2)
        = (1 / 400 : ℝ) * (((P : ℝ) ^ 2)⁻¹ * Real.log (1 + (n : ℝ) / 2)) := by ring
      _ ≤ (1 / 400 : ℝ) * ∑ i : Fin Hsupp.card, ‖(h (embH i) : ℂ)‖ / ((i.val : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hsum_ge (by norm_num)
      _ ≤ circleIntR (fun x => |H x|) := hmps
  -- Upper bound on ‖H‖_1 via primitive A(x) and piecewise-constant Abel summation
  let K : ℕ := 1 + 4 * P ^ 2 * (m + 1)
  have hK1 : 1 ≤ K := by omega
  have hH_cos : ∀ x : ℝ, H x = h 0 + 2 * ∑ j ∈ Finset.Icc (1 : ℕ) N, h (j : ℤ) * Real.cos ((j : ℝ) * x) := by
    intro x
    have hsplit : Finset.Icc (-(N : ℤ)) (N : ℤ) =
        {0} ∪ ((Finset.Icc (1 : ℕ) N).image (fun k : ℕ => (k : ℤ)) ∪
               (Finset.Icc (1 : ℕ) N).image (fun k : ℕ => -(k : ℤ))) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
      constructor
      · intro ⟨hlo, hhi⟩
        rcases lt_trichotomy j 0 with hlt | rfl | hgt
        · right; right; exact ⟨j.natAbs, ⟨by omega, by omega⟩, by omega⟩
        · left; rfl
        · right; left; exact ⟨j.natAbs, ⟨by omega, by omega⟩, by omega⟩
      · rintro (rfl | ⟨k, ⟨h1, h2⟩, rfl⟩ | ⟨k, ⟨h1, h2⟩, rfl⟩) <;> omega
    have hd1 : Disjoint ({0} : Finset ℤ)
        ((Finset.Icc (1 : ℕ) N).image (fun k : ℕ => (k : ℤ)) ∪
         (Finset.Icc (1 : ℕ) N).image (fun k : ℕ => -(k : ℤ))) := by
      rw [Finset.disjoint_left]; intro j hj1 hj2
      simp only [Finset.mem_singleton, Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at hj1 hj2
      subst hj1; rcases hj2 with ⟨k, ⟨h1, _⟩, hk⟩ | ⟨k, ⟨h1, _⟩, hk⟩ <;> omega
    have hd2 : Disjoint ((Finset.Icc (1 : ℕ) N).image (fun k : ℕ => (k : ℤ)))
        ((Finset.Icc (1 : ℕ) N).image (fun k : ℕ => -(k : ℤ))) := by
      rw [Finset.disjoint_left]; intro j hj1 hj2
      simp only [Finset.mem_image, Finset.mem_Icc] at hj1 hj2
      obtain ⟨k1, ⟨h1, _⟩, rfl⟩ := hj1
      obtain ⟨k2, ⟨h2, _⟩, hk⟩ := hj2
      omega
    have hC := hH_eval x
    rw [hsplit, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton, eChar_zero, mul_one,
      Finset.sum_image (fun a _ b _ h => by omega),
      Finset.sum_image (fun a _ b _ h => by omega),
      ← Finset.sum_add_distrib] at hC
    have hpair : ∀ k ∈ Finset.Icc (1 : ℕ) N,
        (h (k : ℤ) : ℂ) * eChar (k : ℤ) x + (h (-(k : ℤ)) : ℂ) * eChar (-(k : ℤ)) x =
        ((2 * (h (k : ℤ) * Real.cos ((k : ℝ) * x)) : ℝ) : ℂ) := by
      intro k _
      rw [hh_even, ← mul_add]
      have hcos : eChar (k : ℤ) x + eChar (-(k : ℤ)) x = ((2 * Real.cos ((k : ℝ) * x) : ℝ) : ℂ) := by
        unfold eChar; push_cast; rw [Complex.cos]
        have h1 : Complex.I * (k : ℂ) * (x : ℂ) = ((k : ℂ) * (x : ℂ)) * Complex.I := by ring
        have h2 : Complex.I * -(k : ℂ) * (x : ℂ) = -(((k : ℂ) * (x : ℂ)) * Complex.I) := by ring
        rw [h1, h2]; ring
      rw [hcos]; push_cast; ring
    rw [Finset.sum_congr rfl hpair] at hC
    have hEqR : ((h 0 + 2 * ∑ j ∈ Finset.Icc (1 : ℕ) N, h (j : ℤ) * Real.cos ((j : ℝ) * x) : ℝ) : ℂ) =
        (H x : ℂ) := by
      rw [← hC]; push_cast; rw [Finset.mul_sum]
    exact (Complex.ofReal_injective hEqR).symm
  have hH_cont : Continuous H := by
    have : H = fun x => h 0 + 2 * ∑ j ∈ Finset.Icc (1 : ℕ) N, h (j : ℤ) * Real.cos ((j : ℝ) * x) :=
      funext hH_cos
    rw [this]
    exact continuous_const.add (continuous_const.mul (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))))
  let A : ℝ → ℝ := fun x => h 0 * x + 2 * ∑ j ∈ Finset.Icc (1 : ℕ) N, h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ))
  have hA_deriv : ∀ x : ℝ, HasDerivAt A (H x) x := by
    intro x
    rw [hH_cos x]
    have h1 : HasDerivAt (fun y : ℝ => h 0 * y) (h 0) x := by
      simpa using (hasDerivAt_id x).const_mul (h 0)
    have h2 : HasDerivAt (fun y : ℝ => ∑ j ∈ Finset.Icc (1 : ℕ) N,
        h (j : ℤ) * (Real.sin ((j : ℝ) * y) / (j : ℝ)))
        (∑ j ∈ Finset.Icc (1 : ℕ) N, h (j : ℤ) * Real.cos ((j : ℝ) * x)) x := by
      refine HasDerivAt.fun_sum fun j hj => ?_
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjne : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
      have hd1 : HasDerivAt (fun y : ℝ => (j : ℝ) * y) (j : ℝ) x := by
        simpa using (hasDerivAt_id x).const_mul (j : ℝ)
      have hd2 := (Real.hasDerivAt_sin ((j : ℝ) * x)).comp x hd1
      have hd3 := (hd2.div_const (j : ℝ)).const_mul (h (j : ℤ))
      have hsimp : h (j : ℤ) * (Real.cos ((j : ℝ) * x) * (j : ℝ) / (j : ℝ)) =
          h (j : ℤ) * Real.cos ((j : ℝ) * x) := by
        rw [mul_div_cancel_right₀ _ hjne]
      rwa [hsimp] at hd3
    exact h1.add (h2.const_mul 2)
  have hA_bound : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, |A x| ≤ 60 * (1 + Real.log (K : ℝ)) := by
    intro x hx
    have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hK1R
    by_cases hx0 : x = 0
    · subst hx0; simp [A]; linarith
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      have hjumps : ((Finset.Icc (2 : ℕ) N).filter (fun j : ℕ => h (j : ℤ) ≠ h ((j - 1 : ℕ) : ℤ))).card + 1 ≤ K := by
        have hj1 := jumps_le_of_second_diff N P hP1 h β hh0 hh4 hh_diff2 hh_int
        have hm_sub : ((Finset.Icc (1 : ℕ) N).filter (fun j : ℕ => β (j : ℤ) ≠ 0)).card ≤ m := by
          have hinj : ((Finset.Icc (1 : ℕ) N).filter (fun j : ℕ => β (j : ℤ) ≠ 0)).card ≤ Bsupp.card := by
            refine Finset.card_le_card_of_injOn (fun j : ℕ => (j : ℤ)) ?_ ?_
            · intro j hj
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Bsupp] at hj ⊢
              exact ⟨⟨by dsimp [M', N] at *; omega, by dsimp [M', N] at *; omega⟩, hj.2⟩
            · intro a _ b _ heq; exact Nat.cast_injective heq
          exact hinj
        have hmul : 4 * P ^ 2 * (((Finset.Icc (1 : ℕ) N).filter (fun j : ℕ => β (j : ℤ) ≠ 0)).card + 1) ≤
            4 * P ^ 2 * (m + 1) := Nat.mul_le_mul_left _ (by omega)
        have hKeq : K = 1 + 4 * P ^ 2 * (m + 1) := rfl
        omega
      have hsine := piecewise_const_sine_sum_bound N K hK1 h hh0 hh4 hjumps x hxpos hx.2
      dsimp [A]
      have h1 : |h 0 * x| ≤ 4 * Real.pi := by
        rw [abs_mul, abs_of_nonneg (hh0 0), abs_of_pos hxpos]
        exact mul_le_mul (hh4 0) hx.2 hxpos.le (by norm_num)
      have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
      calc |h 0 * x + 2 * ∑ j ∈ Finset.Icc (1 : ℕ) N, h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ))|
          ≤ |h 0 * x| + |2 * ∑ j ∈ Finset.Icc (1 : ℕ) N, h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ))| :=
            abs_add_le _ _
        _ = |h 0 * x| + 2 * |∑ j ∈ Finset.Icc (1 : ℕ) N, h (j : ℤ) * (Real.sin ((j : ℝ) * x) / (j : ℝ))| := by
            congr 1; rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ 4 * Real.pi + 2 * (4 * (2 + Real.log (K : ℝ) + Real.pi)) := by linarith
        _ ≤ 60 * (1 + Real.log (K : ℝ)) := by linarith
  -- Integrate |H| over [0, pi] by splitting at the d sign changes t_0 < ... < t_{d-1}
  have hH_upper : circleIntR (fun x => |H x|) ≤ 60 * ((d : ℝ) + 1) * (1 + Real.log (K : ℝ)) := by
    let ep : Fin (d + 2) → ℝ := fun i =>
      if h0 : i.val = 0 then 0
      else if hd : i.val = d + 1 then Real.pi
      else t ⟨i.val - 1, by omega⟩
    have hep0 : ep ⟨0, by omega⟩ = 0 := by simp [ep]
    have hepd : ep ⟨d + 1, by omega⟩ = Real.pi := by simp [ep]
    have hpiece : ∀ i : Fin (d + 1),
        ∫ x in (ep ⟨i.val, by omega⟩)..(ep ⟨i.val + 1, by omega⟩), |H x| ≤
          120 * (1 + Real.log (K : ℝ)) := by
      intro i
      obtain ⟨hac, hsgn⟩ := hsign_Icc i
      have ha_eq : ep ⟨i.val, by omega⟩ = if h : i.val = 0 then 0 else t ⟨i.val - 1, by omega⟩ := by
        dsimp only [ep]
        by_cases h0 : i.val = 0
        · rw [dif_pos h0, dif_pos h0]
        · rw [dif_neg h0, dif_neg (by omega), dif_neg h0]
      have hc_eq : ep ⟨i.val + 1, by omega⟩ = if h : i.val = d then Real.pi else t ⟨i.val, by omega⟩ := by
        dsimp only [ep]
        rw [dif_neg (by omega)]
        by_cases hd : i.val = d
        · rw [dif_pos (by omega), dif_pos hd]
        · rw [dif_neg (by omega), dif_neg hd]; rfl
      have ha_mem : ep ⟨i.val, by omega⟩ ∈ Set.Icc (0 : ℝ) Real.pi := by
        rw [ha_eq]; split_ifs
        · exact ⟨le_rfl, Real.pi_pos.le⟩
        · exact ⟨(ht_mem _).1.le, (ht_mem _).2.le⟩
      have hc_mem : ep ⟨i.val + 1, by omega⟩ ∈ Set.Icc (0 : ℝ) Real.pi := by
        rw [hc_eq]; split_ifs
        · exact ⟨Real.pi_pos.le, le_rfl⟩
        · exact ⟨(ht_mem _).1.le, (ht_mem _).2.le⟩
      rw [← ha_eq, ← hc_eq] at hac hsgn
      have hftc : ∫ x in (ep ⟨i.val, by omega⟩)..(ep ⟨i.val + 1, by omega⟩), H x =
          A (ep ⟨i.val + 1, by omega⟩) - A (ep ⟨i.val, by omega⟩) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hA_deriv x)
          (hH_cont.intervalIntegrable _ _)
      have hEq_abs : ∫ x in (ep ⟨i.val, by omega⟩)..(ep ⟨i.val + 1, by omega⟩), |H x| =
          |∫ x in (ep ⟨i.val, by omega⟩)..(ep ⟨i.val + 1, by omega⟩), H x| := by
        rcases hsgn with hpos | hneg
        · have hHnn : ∀ x ∈ Set.uIcc (ep ⟨i.val, by omega⟩) (ep ⟨i.val + 1, by omega⟩), 0 ≤ H x := by
            intro x hx
            rw [Set.uIcc_of_le hac.le] at hx
            dsimp [H]
            exact mul_nonneg (mul_nonneg (by norm_num) (hpos x hx)) (sq_nonneg _)
          have heq : ∫ x in (ep ⟨i.val, by omega⟩)..(ep ⟨i.val + 1, by omega⟩), |H x| =
              ∫ x in (ep ⟨i.val, by omega⟩)..(ep ⟨i.val + 1, by omega⟩), H x :=
            intervalIntegral.integral_congr fun x hx => abs_of_nonneg (hHnn x hx)
          rw [heq, abs_of_nonneg (intervalIntegral.integral_nonneg hac.le fun x hx =>
            hHnn x (by rwa [Set.uIcc_of_le hac.le]))]
        · have hHnp : ∀ x ∈ Set.uIcc (ep ⟨i.val, by omega⟩) (ep ⟨i.val + 1, by omega⟩), H x ≤ 0 := by
            intro x hx
            rw [Set.uIcc_of_le hac.le] at hx
            dsimp [H]
            exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hneg x hx))
              (sq_nonneg _)
          have heq : ∫ x in (ep ⟨i.val, by omega⟩)..(ep ⟨i.val + 1, by omega⟩), |H x| =
              -(∫ x in (ep ⟨i.val, by omega⟩)..(ep ⟨i.val + 1, by omega⟩), H x) := by
            rw [← intervalIntegral.integral_neg]
            exact intervalIntegral.integral_congr fun x hx => abs_of_nonpos (hHnp x hx)
          have hneg_nn : 0 ≤ -(∫ x in (ep ⟨i.val, by omega⟩)..(ep ⟨i.val + 1, by omega⟩), H x) := by
            rw [← intervalIntegral.integral_neg]
            exact intervalIntegral.integral_nonneg hac.le fun x hx =>
              neg_nonneg.mpr (hHnp x (by rwa [Set.uIcc_of_le hac.le]))
          rw [heq, abs_of_nonpos (by linarith)]
      rw [hEq_abs, hftc]
      calc |A (ep ⟨i.val + 1, by omega⟩) - A (ep ⟨i.val, by omega⟩)|
          ≤ |A (ep ⟨i.val + 1, by omega⟩)| + |A (ep ⟨i.val, by omega⟩)| := abs_sub _ _
        _ ≤ 60 * (1 + Real.log (K : ℝ)) + 60 * (1 + Real.log (K : ℝ)) :=
            add_le_add (hA_bound _ hc_mem) (hA_bound _ ha_mem)
        _ = 120 * (1 + Real.log (K : ℝ)) := by ring
    have hsum_int : ∫ x in (0 : ℝ)..Real.pi, |H x| =
        ∑ i : Fin (d + 1), ∫ x in (ep ⟨i.val, by omega⟩)..(ep ⟨i.val + 1, by omega⟩), |H x| := by
      have htele : ∀ k : ℕ, (hk : k ≤ d + 1) →
          ∫ x in (ep ⟨0, by omega⟩)..(ep ⟨k, by omega⟩), |H x| =
          ∑ i : Fin k, ∫ x in (ep ⟨i.val, by omega⟩)..(ep ⟨i.val + 1, by omega⟩), |H x| := by
        intro k
        induction k with
        | zero => intro _; simp
        | succ k ih =>
          intro hk
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.val_castSucc, Fin.val_last]
          rw [← ih (by omega)]
          exact (intervalIntegral.integral_add_adjacent_intervals
            (hH_cont.abs.intervalIntegrable _ _) (hH_cont.abs.intervalIntegrable _ _)).symm
      have h1 := htele (d + 1) le_rfl
      rw [hep0, hepd] at h1
      exact h1
    have hint_pi_le : ∫ x in (0 : ℝ)..Real.pi, |H x| ≤ 120 * ((d : ℝ) + 1) * (1 + Real.log (K : ℝ)) := by
      rw [hsum_int]
      refine (Finset.sum_le_sum fun i _ => hpiece i).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring_nf; rfl
    -- By evenness and 2*pi periodicity, ∫_0^{2*pi} |H| = 2 * ∫_0^pi |H|
    have hH_sym : ∀ x : ℝ, H (2 * Real.pi - x) = H x := by
      intro x
      rw [hH_cos (2 * Real.pi - x), hH_cos x]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      have harg : (j : ℝ) * (2 * Real.pi - x) = -(j : ℝ) * x + (j : ℤ) * (2 * Real.pi) := by push_cast; ring
      rw [harg, Real.cos_add_int_mul_two_pi, neg_mul, Real.cos_neg]
    have h2pi_eq : ∫ x in (0 : ℝ)..(2 * Real.pi), |H x| = 2 * ∫ x in (0 : ℝ)..Real.pi, |H x| := by
      have hsplit : ∫ x in (0 : ℝ)..(2 * Real.pi), |H x| =
          (∫ x in (0 : ℝ)..Real.pi, |H x|) + (∫ x in Real.pi..(2 * Real.pi), |H x|) :=
        (intervalIntegral.integral_add_adjacent_intervals (b := Real.pi)
          (hH_cont.abs.intervalIntegrable 0 Real.pi) (hH_cont.abs.intervalIntegrable Real.pi (2 * Real.pi))).symm
      rw [hsplit]
      have hsecond : ∫ x in Real.pi..(2 * Real.pi), |H x| = ∫ x in (0 : ℝ)..Real.pi, |H x| := by
        have hcomp := intervalIntegral.integral_comp_sub_left (fun x => |H x|) (2 * Real.pi)
          (a := 0) (b := Real.pi)
        simp only [sub_zero, show 2 * Real.pi - Real.pi = Real.pi by ring] at hcomp
        have hcongr : ∫ x in (0 : ℝ)..Real.pi, |H (2 * Real.pi - x)| =
            ∫ x in (0 : ℝ)..Real.pi, |H x| :=
          intervalIntegral.integral_congr fun x _ => by rw [hH_sym x]
        linarith
      linarith
    unfold circleIntR
    rw [h2pi_eq]
    have hpi_gt2 : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
    have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    have hlogK_nn : 0 ≤ 1 + Real.log (K : ℝ) := by linarith [Real.log_nonneg hK1R]
    calc (2 * Real.pi)⁻¹ * (2 * ∫ x in (0 : ℝ)..Real.pi, |H x|)
        = Real.pi⁻¹ * ∫ x in (0 : ℝ)..Real.pi, |H x| := by field_simp [Real.pi_ne_zero]
      _ ≤ Real.pi⁻¹ * (120 * ((d : ℝ) + 1) * (1 + Real.log (K : ℝ))) :=
          mul_le_mul_of_nonneg_left hint_pi_le (by positivity)
      _ ≤ (1 / 2 : ℝ) * (120 * ((d : ℝ) + 1) * (1 + Real.log (K : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [inv_eq_one_div]
          exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi_gt2.le
      _ = 60 * ((d : ℝ) + 1) * (1 + Real.log (K : ℝ)) := by ring
  -- Step 5: Invert the estimates via standalone helper lemma
  have hd_lower := double_log_inversion n d q m hn_big hlog_q hm_le (hH_lower.trans hH_upper)
  exact (Nat.floor_le_of_le hd_lower).trans hd_le

end Green82Proof

theorem OMA.solution : OMA.R_Green82_green_82_lower_bound_R1.H2 := by
  refine ⟨(1 / 108 : ℝ), by norm_num, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨⌈Real.exp (Real.exp 3000)⌉₊, fun n hn => ?_⟩
  have hnR : Real.exp (Real.exp 3000) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  exact Green82Proof.green_82_H2_core n hnR

