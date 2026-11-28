import OMAReductions.R_ERH_extended_riemann_hypothesis_R1

/-! # A squarefree-ideal criterion for the inverse Dedekind zeta germ

Expand the reciprocal Euler product over finite sets of distinct prime ideals.
H1 identifies the resulting Dirichlet series in the half-plane of absolute
convergence. H2 asks for cancellation in the partial sums of its signed integer
coefficients. Abel summation gives a Mellin transform holomorphic to the right
of one half. The class number formula forces this continuation to vanish at one.
Its divided difference there represents the regularized reciprocal.
-/

-- Credit: @deepqntm

namespace OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R1

open Complex Filter Set NumberField Asymptotics MeasureTheory
open scoped Topology NNReal ENNReal NumberField

/-- The signed prime-ideal sums are the coefficients of the reciprocal Euler product. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    let P := {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥}
    let N (S : Finset P) : ℕ := ∏ p ∈ S, Ideal.absNorm p.1
    let a (n : ℕ) : ℂ := ∑' S : N ⁻¹' {n}, (-1 : ℂ) ^ S.1.card
    ∀ s : ℂ, 1 < s.re → ∃ w : ℂ, HasSum (LSeries.term a s) w ∧ dedekindZeta K s * w = 1

/-- Square-root cancellation in the summatory function of the signed counts. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    let P := {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥}
    let N (S : Finset P) : ℕ := ∏ p ∈ S, Ideal.absNorm p.1
    let a (n : ℕ) : ℂ := ∑' S : N ⁻¹' {n}, (-1 : ℂ) ^ S.1.card
    ∀ r : ℝ, 1 / 2 < r →
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop] fun n => (n : ℝ) ^ r

theorem mellin_continuation (a : ℕ → ℂ)
    (hM : ∀ r : ℝ, 1 / 2 < r →
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop] fun n => (n : ℝ) ^ r) :
    ∃ F : ℂ → ℂ, (∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ F s) ∧
      ∀ s : ℂ, 1 < s.re → LSeriesSummable a s → F s = LSeries a s := by
  let A (x : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, a k
  let F (s : ℂ) : ℂ := s * mellin A (-s)
  have hsmall {x : ℝ} (hx : x < 1) : A x = 0 := by simp [A, Nat.floor_eq_zero.mpr hx]
  refine ⟨F, ?_, ?_⟩
  · intro s hs
    obtain ⟨r, hr, hrs⟩ := exists_between hs
    have hr0 : 0 ≤ r := by linarith
    have htop : A =O[atTop] fun x : ℝ => x ^ r :=
      ((hM r hr).comp_tendsto tendsto_nat_floor_atTop).trans
        (isEquivalent_nat_floor.isBigO.rpow hr0 (eventually_ge_atTop 0))
    have hloc : LocallyIntegrableOn A (Ioi 0) := by
      have h := locallyIntegrableOn_mul_sum_Icc a (m := 1) (a := (0 : ℝ)) le_rfl
        (locallyIntegrableOn_const (1 : ℂ))
      change LocallyIntegrableOn (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, a k) (Ioi 0)
      simpa only [one_mul] using h.mono_set (Ioi_subset_Ici_self)
    let b := -s.re - 1
    have hbot : A =O[𝓝[>] 0] fun x : ℝ => x ^ (-b) := by
      apply (isBigO_zero (fun x : ℝ => x ^ (-b)) _).congr' _ EventuallyEq.rfl
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
      exact (hsmall hx.2).symm
    have hm := mellin_differentiableAt_of_isBigO_rpow (a := -r) (b := b) (s := -s) hloc
      (by simpa using htop) (by simpa using hrs) hbot (by dsimp [b]; simp)
    exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)
  · intro s hs hsum
    have hM := hM 1 (by norm_num)
    change s * mellin A (-s) = LSeries a s
    rw [LSeries_eq_mul_integral a zero_le_one hs hsum hM]
    congr 1
    unfold mellin
    simp only [smul_eq_mul, mul_comm _ (A _), show -s - 1 = -(s + 1) by ring]
    rw [← integral_Ici_eq_integral_Ioi (f := fun x : ℝ => (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, a k) *
      (x : ℂ) ^ (-(s + 1))) (x := 1)]
    change (∫ t : ℝ in Ioi 0, A t * (t : ℂ) ^ (-(s + 1))) =
      ∫ t : ℝ in Ici 1, A t * (t : ℂ) ^ (-(s + 1))
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (show Ici (1 : ℝ) ⊆ Ioi 0 from fun _ hx => Set.mem_Ioi.mpr ((by norm_num : (0 : ℝ) < 1).trans_le (Set.mem_Ici.mp hx)))
    intro x hx
    have hx' : x < 1 := lt_of_not_ge hx.2
    change A x * _ = 0
    rw [hsmall hx', zero_mul]

theorem inverse_extension_zero (K : Type) [Field K] [NumberField K] {F : ℂ → ℂ}
    (hcont : ContinuousAt F 1) (hprod : ∀ s : ℂ, 1 < s.re → dedekindZeta K s * F s = 1) :
    F 1 = 0 := by
  have hembed : Tendsto ofReal (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using (continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 1))
  have hF : Tendsto (fun x : ℝ => F x) (𝓝[>] 1) (𝓝 (F 1)) :=
    hcont.tendsto.comp hembed
  have hres : Tendsto (fun x : ℝ => ((x : ℂ) - 1) * dedekindZeta K x)
      (𝓝[>] 1) (𝓝 ((dedekindZeta_residue K : ℝ) : ℂ)) := by
    simpa only [ofReal_sub, ofReal_one] using tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hx : Tendsto (fun x : ℝ => (x : ℂ) - 1) (𝓝[>] 1) (𝓝 (0 : ℂ)) := by
    simpa using hembed.sub (tendsto_const_nhds (x := (1 : ℂ)))
  have hz : Tendsto (fun x : ℝ => F x * (((x : ℂ) - 1) * dedekindZeta K x))
      (𝓝[>] 1) (𝓝 0) := by
    apply hx.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxr : 1 < (x : ℂ).re := hx
    calc (x : ℂ) - 1 = ((x : ℂ) - 1) * (dedekindZeta K x * F x) := by rw [hprod x hxr, mul_one]
         _ = _ := by ring
  have H := tendsto_nhds_unique (hF.mul hres) hz
  exact (mul_eq_zero.mp H).resolve_right (ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K))

theorem inverse_germ (K : Type) [Field K] [NumberField K] (F : ℂ → ℂ)
    (hd : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ F s)
    (hprod : ∀ s : ℂ, 1 < s.re → dedekindZeta K s * F s = 1) (t : ℝ) :
    let c : ℂ := ⟨2, t⟩
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3 / 2) ≤ p.radius ∧
      ∀ᶠ z in 𝓝 c, ((z - 1) * dedekindZeta K z) * p.sum (z - c) = 1 := by
  intro c
  let U := {s : ℂ | 1 / 2 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hG : DifferentiableOn ℂ (dslope F 1) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds (by norm_num [U]))).mpr
      (fun s hs => (hd s hs).differentiableWithinAt)
  have hF1 := inverse_extension_zero K (hd 1 (by norm_num)).continuousAt hprod
  obtain ⟨p, hp⟩ := hG.analyticAt (hU.mem_nhds (show c ∈ U by norm_num [c, U]))
  refine ⟨p, ?_, ?_⟩
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro r hr h3
    have hr' : (r : ℝ) < 3 / 2 := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).mp
      ((ENNReal.ofReal_coe_nnreal (p := r)).le.trans_lt h3)
    have hsub : Metric.closedBall (c) (r : ℝ) ⊆ U := by
      intro z hz
      have hdist : ‖c - z‖ ≤ (r : ℝ) := by
        simpa only [← dist_eq_norm, dist_comm] using (Metric.mem_closedBall.mp hz)
      have hre := Complex.re_le_norm (c - z)
      change 1 / 2 < z.re
      rw [sub_re] at hre
      change 2 - z.re ≤ _ at hre
      linarith
    have h := (hG.mono hsub).hasFPowerSeriesOnBall hr
    rw [hp.eq_formalMultilinearSeries h.hasFPowerSeriesAt]
    exact h.r_le
  · have hre : ∀ᶠ z in 𝓝 c, 1 < z.re :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num [c])
    filter_upwards [hp.eventually_hasSum_sub, hre] with z hz hzre
    have hz1 : z ≠ 1 := by rintro rfl; norm_num at hzre
    change ((z - 1) * dedekindZeta K z) * (∑' n, _) = 1
    rw [hz.tsum_eq, dslope_of_ne _ hz1, slope_def_module, hF1, sub_zero, smul_eq_mul,
      mul_mul_mul_comm, mul_inv_cancel₀ (sub_ne_zero.mpr hz1), one_mul, hprod z hzre]

theorem main : H1 → H2 → OMA.R_ERH_extended_riemann_hypothesis_R1.H2 := by
  intro heuler hcancel K _ _ t
  obtain ⟨F, hdiff, hagree⟩ := mellin_continuation _ (hcancel K)
  refine inverse_germ K F hdiff (fun s hs => ?_) t
  obtain ⟨w, hsum, hw⟩ := heuler K s hs
  rw [hagree s hs hsum.summable, show LSeries _ s = w from hsum.tsum_eq, hw]

end OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R1
