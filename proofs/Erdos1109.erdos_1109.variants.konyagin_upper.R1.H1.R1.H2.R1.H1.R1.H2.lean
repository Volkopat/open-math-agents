import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1_H1_R1

/-!
# Large sieve with arbitrary circular spacing

We use Gallagher's local averaging proof on disjoint intervals inside one
period. Parseval bounds the squared norms of the trigonometric polynomial
and its derivative. Bounding the variation of its squared norm then gives
the separated sampling inequality.

Reference: P. X. Gallagher, *The large sieve*, Mathematika 14 (1967).
https://doi.org/10.1112/S0025579300007968
-/

namespace OMA.Gallagher1109

open MeasureTheory Finset
open scoped BigOperators ComplexConjugate

noncomputable def circleExp (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((x * n : ℝ) : ℂ))

private theorem circleExp_cross (n m : ℕ) (x : ℝ) :
    circleExp n x * conj (circleExp m x) =
      Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) - m) * x) := by
  unfold circleExp
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_mul,
    Complex.ofReal_natCast, map_natCast]
  ring

private theorem integral_circleExp_cross (n m : ℕ) (u : ℝ) :
    (∫ x in u..u+1, circleExp n x * conj (circleExp m x)) = if n = m then 1 else 0 := by
  simp_rw [circleExp_cross]
  by_cases h : n = m
  · subst m
    simp [intervalIntegral.integral_const]
  · let k : ℂ := 2 * Real.pi * Complex.I * ((n : ℂ) - m)
    have hk : k ≠ 0 := mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero) (sub_ne_zero.mpr (by exact_mod_cast h))
    have hkPeriod : Complex.exp k = 1 := by
      have hkCast : k = (((n : ℤ) - (m : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        unfold k
        push_cast
        ring
      rw [hkCast, Complex.exp_int_mul_two_pi_mul_I]
    have hStep : k * ((u+1 : ℝ) : ℂ) = k * u + k := by push_cast; ring
    change (∫ x in u..u+1, Complex.exp (k * x)) = _
    rw [if_neg h, integral_exp_mul_complex hk, hStep, Complex.exp_add, hkPeriod, mul_one,
      sub_self, zero_div]

/-- Orthogonality of distinct integer modes on an arbitrary interval of length one. -/
theorem integral_norm_sq_fourier_sum (A : Finset ℕ) (c : ℕ → ℂ) (u : ℝ) :
    (∫ x in u..u+1, ‖∑ n ∈ A, c n * circleExp n x‖^2) = ∑ n ∈ A, ‖c n‖^2 := by
  let g (n m : ℕ) (x : ℝ) := c n * conj (c m) * (circleExp n x * conj (circleExp m x))
  have hCont (n m : ℕ) : Continuous (g n m) := by
    unfold g circleExp
    fun_prop
  have hExpand (x : ℝ) : ((‖∑ n ∈ A, c n * circleExp n x‖^2 : ℝ) : ℂ) =
      ∑ n ∈ A, ∑ m ∈ A, g n m x := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul]
    apply sum_congr rfl
    intro n _
    rw [mul_sum]
    apply sum_congr rfl
    intro m _
    rw [map_mul]
    unfold g
    ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal, Complex.ofReal_sum]
  simp_rw [hExpand]
  rw [intervalIntegral.integral_finsetSum
    (fun n _ => (continuous_finsetSum A fun m _ => hCont n m).intervalIntegrable _ _)]
  apply sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_finsetSum (fun m _ => (hCont n m).intervalIntegrable _ _)]
  simp_rw [g, intervalIntegral.integral_const_mul, integral_circleExp_cross]
  rw [sum_eq_single n]
  · simp [Complex.mul_conj', Complex.ofReal_pow]
  · intro m _ hmn
    simp [Ne.symm hmn]
  · exact fun h => (h hn).elim

end OMA.Gallagher1109

namespace OMA.Gallagher1109

open scoped BigOperators RealInnerProductSpace

noncomputable def frequency (n : ℕ) : ℂ := 2 * Real.pi * Complex.I * n

noncomputable def fourierSum (A : Finset ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ A, circleExp n x

noncomputable def fourierDerivative (A : Finset ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ A, frequency n * circleExp n x

noncomputable def energyDerivative (A : Finset ℕ) (x : ℝ) : ℝ :=
  2 * ⟪fourierSum A x, fourierDerivative A x⟫

theorem continuous_circleExp (n : ℕ) : Continuous (circleExp n) := by
  unfold circleExp
  fun_prop

theorem hasDerivAt_circleExp (n : ℕ) (x : ℝ) :
    HasDerivAt (circleExp n) (frequency n * circleExp n x) x := by
  have hz : HasDerivAt (fun y : ℝ => ((y * n : ℝ) : ℂ)) (n : ℂ) x := by
    simpa using ((hasDerivAt_id x).mul_const (n : ℝ)).ofReal_comp
  have ht := (hz.const_mul (2 * Real.pi * Complex.I)).cexp
  change HasDerivAt (fun y : ℝ => Complex.exp (2 * Real.pi * Complex.I *
    ((y * n : ℝ) : ℂ))) ((2 * Real.pi * Complex.I * n) * Complex.exp
      (2 * Real.pi * Complex.I * ((x * n : ℝ) : ℂ))) x
  have he : frequency n * circleExp n x = circleExp n x * frequency n := mul_comm _ _
  rw [show ((2 * Real.pi * Complex.I * n) * Complex.exp
      (2 * Real.pi * Complex.I * ((x * n : ℝ) : ℂ))) =
      Complex.exp (2 * Real.pi * Complex.I * ((x * n : ℝ) : ℂ)) *
        (2 * Real.pi * Complex.I * n) from he]
  exact ht

theorem continuous_fourierSum (A : Finset ℕ) : Continuous (fourierSum A) :=
  continuous_finsetSum _ fun n _ => continuous_circleExp n

theorem continuous_fourierDerivative (A : Finset ℕ) : Continuous (fourierDerivative A) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_circleExp n)

theorem hasDerivAt_energy (A : Finset ℕ) (x : ℝ) :
    HasDerivAt (fun t => ‖fourierSum A t‖ ^ 2) (energyDerivative A x) x := by
  have hsum : HasDerivAt (fourierSum A) (fourierDerivative A x) x :=
    HasDerivAt.fun_sum fun n _ => hasDerivAt_circleExp n x
  exact hsum.norm_sq

theorem continuous_energyDerivative (A : Finset ℕ) : Continuous (energyDerivative A) := by
  unfold energyDerivative
  exact continuous_const.mul ((continuous_fourierSum A).inner (continuous_fourierDerivative A))

theorem abs_energyDerivative_le (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (x : ℝ) :
    |energyDerivative A x| ≤ L * ‖fourierSum A x‖^2 + ‖fourierDerivative A x‖^2 / L := by
  set u := ‖fourierSum A x‖
  set v := ‖fourierDerivative A x‖
  have hCS : |⟪fourierSum A x, fourierDerivative A x⟫| ≤ u*v := by
    rw [← Real.norm_eq_abs]
    exact norm_inner_le_norm _ _
  have hAM : 2 * (u*v) ≤ L*u^2 + v^2/L := by
    apply (mul_le_mul_iff_of_pos_left hL).mp
    have hmul : L * (L*u^2 + v^2/L) = L^2*u^2 + v^2 := by field_simp
    rw [hmul]
    nlinarith [sq_nonneg (L*u-v)]
  unfold energyDerivative
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact (mul_le_mul_of_nonneg_left hCS (by norm_num)).trans hAM

end OMA.Gallagher1109

namespace OMA.Gallagher1109

open MeasureTheory Set
open scoped BigOperators

theorem sample_interval {f g : ℝ → ℝ} (hderiv : ∀ x, HasDerivAt f (g x) x)
    (hg : Continuous g) {a b : ℝ} (hab : a ≤ b) :
    (b-a) * f a ≤ (∫ x in a..b, f x) + (b-a) * ∫ x in a..b, |g x| := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun x => (hderiv x).continuousAt
  have hga : Continuous fun x => |g x| := hg.abs
  let B := ∫ x in a..b, |g x|
  have hpt (y : ℝ) (hy : y ∈ Icc a b) : f a ≤ f y + B := by
    have hy₁ : a ≤ y := hy.1
    have hy₂ : y ≤ b := hy.2
    have hsub : (∫ x in a..y, g x) = f y - f a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
        (hg.intervalIntegrable _ _)
    have habs : |f y - f a| ≤ B := calc
      _ = |∫ x in a..y, g x| := congrArg abs hsub.symm
      _ ≤ ∫ x in a..y, |g x| := intervalIntegral.abs_integral_le_integral_abs hy₁
      _ ≤ B := intervalIntegral.integral_mono_interval le_rfl hy₁ hy₂
        (Filter.Eventually.of_forall fun x => abs_nonneg (g x)) (hga.intervalIntegrable _ _)
    linarith [neg_abs_le (f y - f a)]
  have hl : IntervalIntegrable (fun _ : ℝ => f a) volume a b :=
    continuous_const.intervalIntegrable _ _
  have hr : IntervalIntegrable (fun x : ℝ => f x + B) volume a b :=
    (hf.add continuous_const).intervalIntegrable _ _
  have hine := intervalIntegral.integral_mono_on hab hl hr hpt
  simpa only [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hf.intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b), smul_eq_mul, B] using hine

theorem interval_sum_le {ι : Type*} (J : Finset ι) (α : ι → ℝ)
    {f : ℝ → ℝ} (hf : Continuous f) (hn : ∀ x, 0 ≤ f x)
    {d a b : ℝ} (hd : 0 ≤ d) (hab : a ≤ b)
    (hbox : ∀ i ∈ J, a ≤ α i ∧ α i + d ≤ b)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → d ≤ |α i - α j|) :
    (∑ i ∈ J, ∫ x in α i..(α i+d), f x) ≤ ∫ x in a..b, f x := by
  let I (i : ι) := Ioc (α i) (α i+d)
  have hd' (i : ι) : α i ≤ α i+d := by linarith
  have hdis : Set.Pairwise (J : Set ι) (fun i j => Disjoint (I i) (I j)) := by
    intro i hi j hj hne
    rw [Set.disjoint_left]
    intro x hx hy
    have hs := hsep i hi j hj hne
    change α i < x ∧ x ≤ α i+d at hx
    change α j < x ∧ x ≤ α j+d at hy
    rcases le_total (α i) (α j) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hs
      linarith [hx.2, hy.1]
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hs
      linarith [hy.2, hx.1]
  have hI : ⋃ i ∈ J, I i ⊆ Ioc a b := by
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact Ioc_subset_Ioc (hbox i hi).1 (hbox i hi).2 hxi
  calc
    _ = ∑ i ∈ J, ∫ x in I i, f x := by
      apply Finset.sum_congr rfl
      intro i _
      exact intervalIntegral.integral_of_le (hd' i)
    _ = ∫ x in ⋃ i ∈ J, I i, f x :=
      (integral_biUnion_finset J (fun _ _ => measurableSet_Ioc) hdis
        (fun i _ => (hf.intervalIntegrable _ _).1)).symm
    _ ≤ ∫ x in Ioc a b, f x := setIntegral_mono_set (hf.intervalIntegrable _ _).1
      (Filter.Eventually.of_forall hn) hI.eventuallyLE
    _ = _ := (intervalIntegral.integral_of_le hab).symm

end OMA.Gallagher1109

namespace OMA.Gallagher1109

open MeasureTheory Finset
open scoped BigOperators

private theorem unit_interval_contains_samples {ι : Type*} (J : Finset ι) (α : ι → ℝ)
    (δ : ℝ) (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → δ ≤ 1 - |α i - α j|) :
    ∃ a : ℝ, ∀ i ∈ J, a ≤ α i ∧ α i + min δ 1 ≤ a + 1 := by
  classical
  by_cases hJ : J.Nonempty
  · obtain ⟨j, hj, hmin⟩ := J.exists_min_image α hJ
    refine ⟨α j, fun i hi => ⟨hmin i hi, ?_⟩⟩
    by_cases hij : i = j
    · rw [hij]
      linarith [min_le_right δ (1 : ℝ)]
    · have hwrap := hsep i hi j hj hij
      rw [abs_of_nonneg (sub_nonneg.mpr (hmin i hi))] at hwrap
      linarith [min_le_left δ (1 : ℝ)]
  · exact ⟨0, fun i hi => (hJ ⟨i, hi⟩).elim⟩

private theorem norm_frequency (n : ℕ) : ‖frequency n‖ = 2 * Real.pi * n := by
  simp [frequency, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem large_sieve_by_sampling {ι : Type*} (J : Finset ι) (N : ℕ) (A : Finset ℕ)
    (α : ι → ℝ) (δ : ℝ) (hN : 0 < N) (hA : A ⊆ Icc 1 N) (hδ : 0 < δ)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → δ ≤ |α i - α j| ∧ δ ≤ 1 - |α i - α j|) :
    (∑ j ∈ J, ‖fourierSum A (α j)‖^2) ≤ 16 * ((N : ℝ) + 1/δ) * A.card := by
  let d : ℝ := min δ 1
  have hd : 0 < d := lt_min hδ zero_lt_one
  obtain ⟨a, hbox⟩ := unit_interval_contains_samples J α δ
    (fun i hi j hj hne => (hsep i hi j hj hne).2)
  let f : ℝ → ℝ := fun x => ‖fourierSum A x‖^2
  let g : ℝ → ℝ := energyDerivative A
  let w : ℝ → ℝ := fun x => ‖fourierDerivative A x‖^2
  have hf : Continuous f := (continuous_fourierSum A).norm.pow 2
  have hg : Continuous g := continuous_energyDerivative A
  have hw : Continuous w := (continuous_fourierDerivative A).norm.pow 2
  have hsplit (v : ℝ → ℝ) (hv : Continuous v) (hv0 : ∀ x, 0 ≤ v x) :
      (∑ i ∈ J, ∫ x in α i..(α i+d), v x) ≤ ∫ x in a..(a+1), v x :=
    interval_sum_le J α hv hv0 hd.le (by linarith) hbox
      (fun i hi j hj hne => (min_le_left δ 1).trans (hsep i hi j hj hne).1)
  have hsamples : d * (∑ j ∈ J, f (α j)) ≤
      (∫ x in a..(a+1), f x) + d * ∫ x in a..(a+1), |g x| := by
    rw [mul_sum]
    calc
      _ ≤ ∑ j ∈ J, ((∫ x in α j..(α j+d), f x) + d * ∫ x in α j..(α j+d), |g x|) := by
        apply sum_le_sum
        intro j _
        simpa only [add_sub_cancel_left] using (sample_interval
          (fun x => hasDerivAt_energy A x) hg (a := α j) (b := α j+d) (by linarith))
      _ ≤ _ := by
        rw [sum_add_distrib, ← mul_sum]
        exact add_le_add (hsplit f hf (fun _ => sq_nonneg _))
          (mul_le_mul_of_nonneg_left (hsplit _ hg.abs (fun _ => abs_nonneg _)) hd.le)
  have hfInt : (∫ x in a..(a+1), f x) = A.card := by
    simpa [f, fourierSum] using integral_norm_sq_fourier_sum A (fun _ => (1 : ℂ)) a
  let L : ℝ := 2 * Real.pi * N
  have hL : 0 < L := by
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    dsimp [L]
    positivity
  have hwInt : (∫ x in a..(a+1), w x) ≤ L^2 * A.card := by
    change (∫ x in a..(a+1), ‖∑ n ∈ A, frequency n * circleExp n x‖^2) ≤ _
    rw [integral_norm_sq_fourier_sum]
    calc
      _ ≤ ∑ _n ∈ A, L^2 := by
        apply sum_le_sum
        intro n hn
        have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (mem_Icc.mp (hA hn)).2
        have hnL : ‖frequency n‖ ≤ L := by
          rw [norm_frequency]
          exact mul_le_mul_of_nonneg_left hnN (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) hnL _
      _ = _ := by simp [mul_comm]
  have hgBound : (∫ x in a..(a+1), |g x|) ≤ 2 * L * A.card := by
    have hgI := intervalIntegral.integral_mono_on (μ := volume) (a := a) (b := a+1) (by linarith)
      (hg.abs.intervalIntegrable _ _) (((continuous_const.mul hf).add (hw.div_const L)).intervalIntegrable _ _)
      (fun x _ => abs_energyDerivative_le A hL x)
    change (∫ x in a..(a+1), |g x|) ≤ ∫ x in a..(a+1), L * f x + w x / L at hgI
    have hleft : IntervalIntegrable (fun x : ℝ => L * f x) volume a (a+1) :=
      (continuous_const.mul hf).intervalIntegrable _ _
    have hright : IntervalIntegrable (fun x : ℝ => w x / L) volume a (a+1) :=
      (hw.div_const L).intervalIntegrable _ _
    have hsum : (∫ x in a..(a+1), L * f x + w x / L) =
        (∫ x in a..(a+1), L * f x) + ∫ x in a..(a+1), w x / L :=
      intervalIntegral.integral_add hleft hright
    rw [hsum, intervalIntegral.integral_const_mul, intervalIntegral.integral_div, hfInt] at hgI
    calc
      _ ≤ L * (A.card : ℝ) + (L^2 * (A.card : ℝ)) / L :=
        hgI.trans (add_le_add_right (div_le_div_of_nonneg_right hwInt hL.le) _)
      _ = _ := by
        field_simp
        ring
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcoeff : 1/d + 2*L ≤ 16 * ((N : ℝ) + 1/δ) := by
    have hdInv : 1/d ≤ 1 + 1/δ := by
      rcases le_total δ 1 with h | h
      · rw [show d = δ from min_eq_left h]
        linarith
      · rw [show d = 1 from min_eq_right h]
        have : 0 ≤ (1 : ℝ)/δ := by positivity
        linarith
    have hpi : Real.pi < 15/4 := Real.pi_lt_d2.trans (by norm_num)
    have hmul : (4 * Real.pi) * (N : ℝ) ≤ 15 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hδInv : 0 ≤ (1 : ℝ)/δ := by positivity
    dsimp [L]
    nlinarith
  have hres : (∑ j ∈ J, f (α j)) ≤ (1/d + 2*L) * A.card := by
    apply (mul_le_mul_iff_of_pos_left hd).mp
    calc
      _ ≤ (A.card : ℝ) + d * (2 * L * A.card) := by
        rw [hfInt] at hsamples
        exact hsamples.trans (add_le_add_right (mul_le_mul_of_nonneg_left hgBound hd.le) _)
      _ = _ := by field_simp
  exact hres.trans (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _))

end OMA.Gallagher1109

theorem OMA.solution :
    OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1_H2_R1_H1_R1.H2 := by
  intro ι _ J N A α δ hN hA hδ _ hsep
  exact OMA.Gallagher1109.large_sieve_by_sampling J N A α δ hN hA hδ hsep
