import FormalConjectures.Wikipedia.Bloch

/-!
# Rademacher's upper bound on the Landau constant

We prove `Bloch.landauConstant ≤ Real.Gamma (1 / 3) * Real.Gamma (5 / 6) / Real.Gamma (1 / 6)`
by constructing Rademacher's extremal covering map `𝔻 → ℂ \ L₀` via the primitive of `η(ψ(z))⁴ ψ'(z)`
composed with the Cayley transform `ψ : 𝔻 → ℍ`, identifying `℘[L₀] ∘ G = P ∘ ψ` via ODE uniqueness,
and computing the hexagonal lattice half-period `e₁` via the Beta integral and Legendre duplication.
-/

open Complex Real Metric Set Filter Topology Function
open UpperHalfPlane hiding I
open ModularForm ModularGroup MatrixGroups EisensteinSeries Derivative PeriodPair

namespace BlochLandauB

noncomputable section

/- ### Part 1: Hexagonal root `rhoC` and lattice `L0 = ℤ + rhoC ℤ` -/

private def rhoC : ℂ := ((-1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I

private lemma rhoC_re : rhoC.re = -1 / 2 := by
  simp [rhoC]

private lemma rhoC_im : rhoC.im = Real.sqrt 3 / 2 := by
  simp [rhoC]

private lemma rhoC_im_pos : 0 < rhoC.im := by
  rw [rhoC_im]
  positivity

private def rhoH : ℍ := ⟨rhoC, rhoC_im_pos⟩

private lemma rhoH_coe : (rhoH : ℂ) = rhoC := rfl

private lemma rhoC_sq_add_rhoC_add_one : rhoC ^ 2 + rhoC + 1 = 0 := by
  apply Complex.ext
  · simp [rhoC, sq]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · simp [rhoC, sq]
    ring

private lemma rhoC_cube : rhoC ^ 3 = 1 := by
  linear_combination (rhoC - 1) * rhoC_sq_add_rhoC_add_one

private lemma rhoC_ne_zero : rhoC ≠ 0 := by
  intro h
  have := rhoC_cube
  rw [h] at this
  norm_num at this

private lemma conj_rhoC : starRingEnd ℂ rhoC = -1 - rhoC := by
  simp only [rhoC, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  apply Complex.ext
  · simp; ring
  · simp

private lemma rhoC_sub_conj : rhoC - starRingEnd ℂ rhoC = I * (Real.sqrt 3 : ℝ) := by
  rw [conj_rhoC]
  apply Complex.ext
  · simp [rhoC]; ring
  · simp [rhoC]

private lemma rhoC_ne_one : rhoC ≠ 1 := by
  intro h
  have := congr_arg Complex.im h
  simp [rhoC_im] at this

private lemma rhoC_sq_ne_one : rhoC ^ 2 ≠ 1 := by
  intro h
  have h1 : rhoC + 2 = 0 := by linear_combination rhoC_sq_add_rhoC_add_one - h
  have := congr_arg Complex.im h1
  simp [rhoC_im] at this

private lemma linearIndependent_one_rhoC : LinearIndependent ℝ ![(1 : ℂ), rhoC] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by simpa [rhoC_im] using congr_arg Complex.im hst
  subst ht
  have hre := congr_arg Complex.re hst
  simp at hre
  exact ⟨hre, rfl⟩

private def L0 : PeriodPair := ⟨1, rhoC, linearIndependent_one_rhoC⟩

private lemma one_mem_L0 : (1 : ℂ) ∈ L0.lattice := L0.ω₁_mem_lattice

private lemma rhoC_mem_L0 : rhoC ∈ L0.lattice := L0.ω₂_mem_lattice

private lemma mem_L0_iff {z : ℂ} : z ∈ L0.lattice ↔ ∃ m n : ℤ, (m : ℂ) + n * rhoC = z := by
  simp [PeriodPair.mem_lattice, L0]

private lemma mul_rhoC_mem_L0 {l : ℂ} (hl : l ∈ L0.lattice) : rhoC * l ∈ L0.lattice := by
  obtain ⟨m, n, rfl⟩ := mem_L0_iff.mp hl
  rw [mem_L0_iff]
  refine ⟨-n, m - n, ?_⟩
  push_cast
  linear_combination -(n : ℂ) * rhoC_sq_add_rhoC_add_one

private lemma conj_mem_L0 {l : ℂ} (hl : l ∈ L0.lattice) : starRingEnd ℂ l ∈ L0.lattice := by
  obtain ⟨m, n, rfl⟩ := mem_L0_iff.mp hl
  rw [mem_L0_iff]
  refine ⟨m - n, -n, ?_⟩
  simp [conj_rhoC]
  ring

private def mulRhoEquiv : L0.lattice ≃ L0.lattice where
  toFun l := ⟨rhoC * l.1, mul_rhoC_mem_L0 l.2⟩
  invFun l := ⟨rhoC * (rhoC * l.1), mul_rhoC_mem_L0 (mul_rhoC_mem_L0 l.2)⟩
  left_inv l := by
    ext
    dsimp
    linear_combination l.1 * rhoC_cube
  right_inv l := by
    ext
    dsimp
    linear_combination l.1 * rhoC_cube

private def conjLatticeEquiv : L0.lattice ≃ L0.lattice where
  toFun l := ⟨starRingEnd ℂ l.1, conj_mem_L0 l.2⟩
  invFun l := ⟨starRingEnd ℂ l.1, conj_mem_L0 l.2⟩
  left_inv l := by ext; simp
  right_inv l := by ext; simp

private lemma L0_g2_eq_zero : L0.g₂ = 0 := by
  suffices h : L0.G 4 = 0 by simp [PeriodPair.g₂, h]
  have hG : L0.G 4 = (rhoC ^ 4)⁻¹ * L0.G 4 := by
    unfold PeriodPair.G
    conv_lhs => rw [← mulRhoEquiv.tsum_eq]
    rw [← tsum_mul_left]
    refine tsum_congr fun l => ?_
    simp [mulRhoEquiv, mul_pow, mul_comm]
  have hr4 : rhoC ^ 4 = rhoC := by linear_combination rhoC * rhoC_cube
  rw [hr4] at hG
  have hG' : (rhoC - 1) * L0.G 4 = 0 := by
    have := congr_arg (rhoC * ·) hG
    simp [← mul_assoc, mul_inv_cancel₀ rhoC_ne_zero] at this
    linear_combination this
  exact (mul_eq_zero.mp hG').resolve_left (sub_ne_zero.mpr rhoC_ne_one)

/- ### Part 2: Covering radius of `L0.lattice` is `1 / √3` -/

private lemma exists_dist_le_L0 (x : ℂ) : ∃ l ∈ L0.lattice, dist x l ≤ 1 / Real.sqrt 3 := by
  set v : ℂ := 1 + rhoC
  have hv_mem : v ∈ L0.lattice := add_mem one_mem_L0 rhoC_mem_L0
  have hv_re : v.re = 1 / 2 := by simp [v, rhoC_re]; ring
  have hv_im : v.im = Real.sqrt 3 / 2 := by simp [v, rhoC_im]
  have hsqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set y : ℝ := x.im / (Real.sqrt 3 / 2)
  set b : ℤ := ⌊y⌋
  set t : ℝ := Int.fract y
  have ht0 : 0 ≤ t := Int.fract_nonneg y
  have ht1 : t < 1 := Int.fract_lt_one y
  have ht_eq : (b : ℝ) + t = y := Int.floor_add_fract y
  set u : ℝ := x.re - (b : ℝ) * (1 / 2) - t * (1 / 2)
  set a : ℤ := ⌊u⌋
  set s : ℝ := Int.fract u
  have hs0 : 0 ≤ s := Int.fract_nonneg u
  have hs1 : s < 1 := Int.fract_lt_one u
  have hs_eq : (a : ℝ) + s = u := Int.floor_add_fract u
  set base : ℂ := (a : ℂ) * 1 + (b : ℂ) * v
  have hbase_mem : base ∈ L0.lattice :=
    add_mem (by simpa [zsmul_eq_mul] using Submodule.smul_mem L0.lattice a one_mem_L0)
      (by simpa [zsmul_eq_mul] using Submodule.smul_mem L0.lattice b hv_mem)
  have hx_eq : x - base = (s : ℂ) + (t : ℂ) * v := by
    apply Complex.ext
    · simp only [sub_re, add_re, mul_re, one_re, one_im, intCast_re, intCast_im,
        ofReal_re, ofReal_im, hv_re, hv_im, base]
      dsimp only [u] at hs_eq
      linarith
    · simp only [sub_im, add_im, mul_im, one_re, one_im, intCast_re, intCast_im,
        ofReal_re, ofReal_im, hv_re, hv_im, base]
      have hy : y * (Real.sqrt 3 / 2) = x.im := div_mul_cancel₀ x.im (by positivity)
      nlinarith [ht_eq, hy]
  have hnorm_sq : ∀ (p q : ℝ),
      ‖((p : ℂ) + (q : ℂ) * v)‖ ^ 2 = p ^ 2 + p * q + q ^ 2 := by
    intro p q
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, hv_re, hv_im]
    nlinarith [hsqrt3_sq]
  have htri : ∀ (p q : ℝ), 0 ≤ p → 0 ≤ q → p + q ≤ 1 →
      min (p ^ 2 + p * q + q ^ 2)
        (min ((p - 1) ^ 2 + (p - 1) * q + q ^ 2) (p ^ 2 + p * (q - 1) + (q - 1) ^ 2)) ≤ 1 / 3 := by
    intro p q hp hq hpq
    set α := 1 - p - q
    have hα : 0 ≤ α := by linarith
    have hcomb :
        α * (p ^ 2 + p * q + q ^ 2) +
        p * ((p - 1) ^ 2 + (p - 1) * q + q ^ 2) +
        q * (p ^ 2 + p * (q - 1) + (q - 1) ^ 2) =
        α * p + p * q + q * α := by
      dsimp [α]; ring
    have hbound : α * p + p * q + q * α ≤ 1 / 3 := by
      have : (α - p) ^ 2 + (p - q) ^ 2 + (q - α) ^ 2 ≥ 0 := by positivity
      have hsum : α + p + q = 1 := by dsimp [α]; ring
      nlinarith
    by_contra hlt
    push Not at hlt
    have h1 : 1 / 3 < p ^ 2 + p * q + q ^ 2 := lt_of_lt_of_le hlt (min_le_left _ _)
    have h2 : 1 / 3 < (p - 1) ^ 2 + (p - 1) * q + q ^ 2 :=
      lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _))
    have h3 : 1 / 3 < p ^ 2 + p * (q - 1) + (q - 1) ^ 2 :=
      lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_right _ _))
    have hsum : α + p + q = 1 := by dsimp [α]; ring
    nlinarith
  have hdist_of_sq : ∀ l : ℂ, l ∈ L0.lattice → ‖x - l‖ ^ 2 ≤ 1 / 3 →
      ∃ l' ∈ L0.lattice, dist x l' ≤ 1 / Real.sqrt 3 := by
    intro l hl hsq
    refine ⟨l, hl, ?_⟩
    rw [Complex.dist_eq]
    have h1 : ‖x - l‖ ≤ Real.sqrt (1 / 3) := Real.le_sqrt_of_sq_le hsq
    have h2 : Real.sqrt (1 / 3) = 1 / Real.sqrt 3 := by
      rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
    linarith
  by_cases hst : s + t ≤ 1
  · have hm := htri s t hs0 ht0 hst
    rcases le_or_gt (s ^ 2 + s * t + t ^ 2) (1 / 3) with h1 | h1
    · exact hdist_of_sq base hbase_mem (by rw [hx_eq, hnorm_sq]; exact h1)
    · rcases le_or_gt ((s - 1) ^ 2 + (s - 1) * t + t ^ 2) (1 / 3) with h2 | h2
      · refine hdist_of_sq (base + 1) (add_mem hbase_mem one_mem_L0) ?_
        have : x - (base + 1) = ((s - 1 : ℝ) : ℂ) + (t : ℂ) * v := by
          push_cast; linear_combination hx_eq
        rw [this, hnorm_sq]; exact h2
      · refine hdist_of_sq (base + v) (add_mem hbase_mem hv_mem) ?_
        have : x - (base + v) = (s : ℂ) + ((t - 1 : ℝ) : ℂ) * v := by
          push_cast; linear_combination hx_eq
        rw [this, hnorm_sq]
        by_contra h3
        push Not at h3
        have := lt_min h1 (lt_min h2 h3)
        linarith
  · push Not at hst
    set s' := 1 - s
    set t' := 1 - t
    have hs'0 : 0 ≤ s' := by linarith
    have ht'0 : 0 ≤ t' := by linarith
    have hst' : s' + t' ≤ 1 := by linarith
    have hm := htri s' t' hs'0 ht'0 hst'
    have hbase2 : base + 1 + v ∈ L0.lattice := add_mem (add_mem hbase_mem one_mem_L0) hv_mem
    have hx_eq' : (base + 1 + v) - x = (s' : ℂ) + (t' : ℂ) * v := by
      dsimp [s', t']; push_cast; linear_combination -hx_eq
    rcases le_or_gt (s' ^ 2 + s' * t' + t' ^ 2) (1 / 3) with h1 | h1
    · refine hdist_of_sq (base + 1 + v) hbase2 ?_
      rw [norm_sub_rev, hx_eq', hnorm_sq]; exact h1
    · rcases le_or_gt ((s' - 1) ^ 2 + (s' - 1) * t' + t' ^ 2) (1 / 3) with h2 | h2
      · refine hdist_of_sq (base + v) (add_mem hbase_mem hv_mem) ?_
        have : (base + v) - x = ((s' - 1 : ℝ) : ℂ) + (t' : ℂ) * v := by
          push_cast; linear_combination hx_eq'
        rw [norm_sub_rev, this, hnorm_sq]; exact h2
      · refine hdist_of_sq (base + 1) (add_mem hbase_mem one_mem_L0) ?_
        have : (base + 1) - x = (s' : ℂ) + ((t' - 1 : ℝ) : ℂ) * v := by
          push_cast; linear_combination hx_eq'
        rw [norm_sub_rev, this, hnorm_sq]
        by_contra h3
        push Not at h3
        have := lt_min h1 (lt_min h2 h3)
        linarith

/- ### Part 3: Modular forms — `E₄(ρ) = 0`, `L0.g₃`, and `serreDerivative 4 E₄ = -(1/3) E₆` -/

private lemma E4_rhoH : ModularForm.E₄ rhoH = 0 := by
  let γ : SL(2, ℤ) := ModularGroup.S * ModularGroup.T
  have hγ_mem : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hγ_act : γ • rhoH = rhoH := by
    rw [mul_smul, UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_S_smul]
    apply UpperHalfPlane.ext
    simp only [UpperHalfPlane.coe_vadd, rhoH_coe]
    change (-(1 + rhoC))⁻¹ = rhoC
    exact inv_eq_of_mul_eq_one_right (by linear_combination -rhoC_sq_add_rhoC_add_one)
  have h10 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by decide
  have h11 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by decide
  have hdenom : UpperHalfPlane.denom γ rhoH = rhoC + 1 := by
    rw [UpperHalfPlane.denom]
    simp [h10, h11, rhoH_coe]
  have hsl := congr_fun (SlashInvariantForm.slash_action_eqn ModularForm.E₄ _ hγ_mem) rhoH
  rw [show ((ModularForm.E₄ : ℍ → ℂ) ∣[(4 : ℤ)] (γ : GL (Fin 2) ℝ)) rhoH =
      ((ModularForm.E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ) rhoH from rfl,
    ModularForm.SL_slash_apply, hγ_act, hdenom] at hsl
  have hp4 : (rhoC + 1) ^ 4 = rhoC ^ 2 := by
    have h1 : rhoC + 1 = -rhoC ^ 2 := by linear_combination rhoC_sq_add_rhoC_add_one
    rw [h1]
    have : (-rhoC ^ 2) ^ 4 = rhoC ^ 8 := by ring
    rw [this]
    linear_combination (rhoC ^ 5 + rhoC ^ 2) * rhoC_cube
  have hne : rhoC + 1 ≠ 0 := by
    intro h; have := congr_arg Complex.im h; simp [rhoC_im] at this
  have hmul : ModularForm.E₄ rhoH * (rhoC ^ 2 - 1) = 0 := by
    have h2 : ModularForm.E₄ rhoH = ModularForm.E₄ rhoH * (rhoC + 1) ^ 4 := by
      have := congr_arg (· * (rhoC + 1) ^ 4) hsl
      rw [mul_assoc, ← zpow_natCast (rhoC + 1) 4, ← zpow_add₀ hne] at this
      simp at this
      exact this
    rw [hp4] at h2
    linear_combination -h2
  exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr rhoC_sq_ne_one)

private lemma E6_rhoH_sq : ModularForm.E₆ rhoH ^ 2 = -1728 * ModularForm.discriminant rhoH := by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq rhoH
  rw [E4_rhoH] at h
  linear_combination 1728 * h

private lemma E6_rhoH_ne_zero : ModularForm.E₆ rhoH ≠ 0 := by
  intro h
  have hsq := E6_rhoH_sq
  rw [h] at hsq
  have hne : (-1728 : ℂ) * ModularForm.discriminant rhoH ≠ 0 :=
    mul_ne_zero (by norm_num) (ModularForm.discriminant_ne_zero rhoH)
  exact hne (by simpa using hsq.symm)

private lemma riemannZeta_six : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  have hb : bernoulli 6 = 1 / 42 := by decide +kernel
  simp only [show (2 * 3 : ℕ) = 6 by norm_num, hb, Nat.factorial] at h
  norm_num at h
  rw [h]
  ring

private lemma L0_g3_eq : L0.g₃ = (8 * (Real.pi : ℂ) ^ 6 / 27) * ModularForm.E₆ rhoH := by
  have hG6 : L0.G 6 = ∑' v : Fin 2 → ℤ, EisensteinSeries.eisSummand 6 v rhoH := by
    unfold PeriodPair.G
    let e : (Fin 2 → ℤ) ≃ L0.lattice :=
      ((finTwoArrowEquiv ℤ).trans (Equiv.prodComm ℤ ℤ)).trans L0.latticeEquivProd.symm
    rw [← e.tsum_eq]
    refine tsum_congr fun v => ?_
    have hev : (e v : ℂ) = (v 0 : ℂ) * rhoC + (v 1 : ℂ) := by
      dsimp [e]
      rw [PeriodPair.latticeEquiv_symm_apply]
      simp [L0]
      ring
    simp [EisensteinSeries.eisSummand, hev, rhoH_coe, zpow_neg]
  have htsum := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 6) (by norm_num) rhoH
  norm_num at htsum
  have hE6 : ModularForm.E₆ rhoH = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 6 rhoH := rfl
  rw [PeriodPair.g₃, hG6, htsum, riemannZeta_six, hE6]
  ring

private lemma L0_g3_ne_zero : L0.g₃ ≠ 0 := by
  rw [L0_g3_eq]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 6 hpi)) (by norm_num))
    E6_rhoH_ne_zero

private lemma tendsto_atImInfty_E4 : Tendsto (ModularForm.E₄ : ℍ → ℂ) atImInfty (𝓝 1) := by
  have hana := ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ one_pos one_mem_strictPeriods_SL
  have hval : UpperHalfPlane.cuspFunction 1 ModularForm.E₄ 0 = 1 := by
    have h0 := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩
    simpa [UpperHalfPlane.qExpansion_coeff] using h0
  have heq : (UpperHalfPlane.cuspFunction 1 ModularForm.E₄ ∘ fun τ : ℍ => Periodic.qParam 1 τ) =
      ModularForm.E₄ := by
    funext τ
    exact SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ τ one_mem_strictPeriods_SL one_ne_zero
  simpa [heq, hval] using hana.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)

private lemma tendsto_atImInfty_E6 : Tendsto (ModularForm.E₆ : ℍ → ℂ) atImInfty (𝓝 1) := by
  have hana := ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₆ one_pos one_mem_strictPeriods_SL
  have hval : UpperHalfPlane.cuspFunction 1 ModularForm.E₆ 0 = 1 := by
    have h0 := EisensteinSeries.E_qExpansion_coeff_zero (k := 6) (by norm_num) ⟨3, rfl⟩
    simpa [UpperHalfPlane.qExpansion_coeff] using h0
  have heq : (UpperHalfPlane.cuspFunction 1 ModularForm.E₆ ∘ fun τ : ℍ => Periodic.qParam 1 τ) =
      ModularForm.E₆ := by
    funext τ
    exact SlashInvariantFormClass.eq_cuspFunction ModularForm.E₆ τ one_mem_strictPeriods_SL one_ne_zero
  simpa [heq, hval] using hana.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)

private lemma periodic_E2 : Function.Periodic (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw1,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    rw [EisensteinSeries.E2_eq_tsum_cexp, EisensteinSeries.E2_eq_tsum_cexp]
    congr 2
    refine tsum_congr fun n => ?_
    congr 2
    have : Complex.exp (2 * Real.pi * I * (w + 1)) = Complex.exp (2 * Real.pi * I * w) := by
      rw [mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    exact this
  · have hw1 : (w + 1).im ≤ 0 := by simpa using hw
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hw),
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hw1]

private lemma tendsto_atImInfty_E2 : Tendsto EisensteinSeries.E2 atImInfty (𝓝 1) := by
  have hana : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos periodic_E2
      E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  have hfps := UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction one_pos hana fun τ => by
    simpa only [Periodic.qParam, ofReal_one, div_one] using
      EisensteinSeries.hasSum_qExpansion_E2 (z := τ)
  have hval : UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2 0 = 1 := by
    have h0 := hfps.coeff_zero 1
    simpa using h0.symm
  have heq : (UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2 ∘ fun τ : ℍ => Periodic.qParam 1 τ) =
      EisensteinSeries.E2 := by
    funext τ
    exact UpperHalfPlane.eq_cuspFunction τ one_ne_zero periodic_E2
  simpa [heq, hval] using hana.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)

private lemma tendsto_atImInfty_D_E4 :
    Tendsto (Derivative.normalizedDerivOfComplex (ModularForm.E₄ : ℍ → ℂ)) atImInfty (𝓝 0) := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  have hdiff : DifferentiableOn ℂ (UpperHalfPlane.cuspFunction 1 ModularForm.E₄) (Metric.ball 0 1) :=
    UpperHalfPlane.differentiableOn_cuspFunction_ball one_pos hper ModularForm.E₄.holo'
      (ModularFormClass.bdd_at_infty ModularForm.E₄)
  have hderiv_cont : ContinuousAt (deriv (UpperHalfPlane.cuspFunction 1 ModularForm.E₄)) 0 :=
    ((hdiff.deriv Metric.isOpen_ball).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))).continuousAt
  have hDeq : ∀ τ : ℍ, Derivative.normalizedDerivOfComplex (ModularForm.E₄ : ℍ → ℂ) τ =
      Periodic.qParam 1 τ * deriv (UpperHalfPlane.cuspFunction 1 ModularForm.E₄) (Periodic.qParam 1 τ) := by
    intro τ
    have hq_mem : Periodic.qParam 1 τ ∈ Metric.ball (0 : ℂ) 1 := by
      simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
    have hcf : HasDerivAt (UpperHalfPlane.cuspFunction 1 ModularForm.E₄)
        (deriv (UpperHalfPlane.cuspFunction 1 ModularForm.E₄) (Periodic.qParam 1 τ))
        (Periodic.qParam 1 τ) :=
      (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hq_mem)).hasDerivAt
    have hqp : HasDerivAt (Periodic.qParam 1) (2 * Real.pi * I * Periodic.qParam 1 τ) (τ : ℂ) := by
      have h1 : Periodic.qParam 1 = fun w : ℂ => Complex.exp (2 * Real.pi * I * w) := by
        ext w; simp [Periodic.qParam]
      rw [h1]
      simpa [Periodic.qParam, mul_comm] using
        ((hasDerivAt_id (τ : ℂ)).const_mul (2 * Real.pi * I)).cexp
    have hcomp := hcf.comp (τ : ℂ) hqp
    have hev : (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (τ : ℂ)]
        (UpperHalfPlane.cuspFunction 1 ModularForm.E₄ ∘ Periodic.qParam 1) := by
      filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
      exact (SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ ⟨w, hw⟩
        one_mem_strictPeriods_SL one_ne_zero).symm
    rw [Derivative.normalizedDerivOfComplex, (hcomp.congr_of_eventuallyEq hev).deriv]
    have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    field_simp [h2pi]
  have ht : Tendsto
      (fun τ : ℍ => Periodic.qParam 1 τ *
        deriv (UpperHalfPlane.cuspFunction 1 ModularForm.E₄) (Periodic.qParam 1 τ))
      atImInfty (𝓝 0) := by
    simpa using (UpperHalfPlane.qParam_tendsto_atImInfty one_pos).mul
      (hderiv_cont.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos))
  exact ht.congr fun τ => (hDeq τ).symm

private lemma tendsto_atImInfty_serreE4 :
    Tendsto (Derivative.serreDerivative 4 (ModularForm.E₄ : ℍ → ℂ)) atImInfty (𝓝 (-1 / 3 : ℂ)) := by
  have h := tendsto_atImInfty_D_E4.sub
    ((tendsto_const_nhds (x := (4 * 12⁻¹ : ℂ)).mul tendsto_atImInfty_E2).mul tendsto_atImInfty_E4)
  have hval : (0 : ℂ) - 4 * 12⁻¹ * 1 * 1 = -1 / 3 := by norm_num
  rw [hval] at h
  exact h

private lemma serreE4_slash (γ : SL(2, ℤ)) :
    (Derivative.serreDerivative 4 (ModularForm.E₄ : ℍ → ℂ) ∣[(6 : ℤ)] γ) =
      Derivative.serreDerivative 4 (ModularForm.E₄ : ℍ → ℂ) := by
  have hinv : ((ModularForm.E₄ : ℍ → ℂ) ∣[(4 : ℤ)] γ) = ModularForm.E₄ :=
    ModularForm.E₄.slash_action_eq' (γ : GL (Fin 2) ℝ) ⟨γ, rfl⟩
  have h := Derivative.serreDerivative_slash_invariant (k := (4 : ℤ)) ModularForm.E₄.holo' hinv
  simpa [show (4 : ℤ) + 2 = 6 by norm_num] using h

private def serreE4MF : ModularForm 𝒮ℒ 6 where
  toFun := Derivative.serreDerivative 4 (ModularForm.E₄ : ℍ → ℂ)
  slash_action_eq' := fun _ ⟨γ, hγ⟩ => hγ ▸ serreE4_slash γ
  holo' := Derivative.serreDerivative_mdifferentiable 4 ModularForm.E₄.holo'
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [serreE4_slash γ]
    exact tendsto_atImInfty_serreE4.isBigO_one ℝ

private lemma serreDerivative_E4 :
    Derivative.serreDerivative 4 (ModularForm.E₄ : ℍ → ℂ) = (-1 / 3 : ℂ) • (ModularForm.E₆ : ℍ → ℂ) := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ModularForm.E₆ = serreE4MF :=
    (finrank_eq_one_iff_of_nonzero' ModularForm.E₆
      (EisensteinSeries.E_ne_zero (k := 6) (by norm_num) ⟨3, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_six_rank_one) serreE4MF
  have hfun : (fun z : ℍ => c * ModularForm.E₆ z) =
      Derivative.serreDerivative 4 (ModularForm.E₄ : ℍ → ℂ) := by
    funext z
    exact congr_fun (congr_arg DFunLike.coe hc) z
  have ht1 : Tendsto (fun z : ℍ => c * ModularForm.E₆ z) atImInfty (𝓝 (c * 1)) :=
    tendsto_const_nhds.mul tendsto_atImInfty_E6
  rw [hfun] at ht1
  have hc_eq : c = -1 / 3 := by
    have := tendsto_nhds_unique ht1 tendsto_atImInfty_serreE4
    simpa using this
  subst hc_eq
  ext z
  exact (congr_fun hfun z).symm

/- ### Part 4: Weierstrass `℘[L0]` symmetries, `e₁ > 0`, and the Beta integral -/

private lemma conj_weierstrassP (z : ℂ) :
    starRingEnd ℂ (℘[L0] z) = ℘[L0] (starRingEnd ℂ z) := by
  have h1 := (L0.hasSum_weierstrassP z).map (starRingEnd ℂ) Complex.continuous_conj
  have h2 := conjLatticeEquiv.hasSum_iff.mpr (L0.hasSum_weierstrassP (starRingEnd ℂ z))
  refine h1.unique ?_
  convert h2 using 1
  ext l
  simp [conjLatticeEquiv]

private lemma conj_derivWeierstrassP (z : ℂ) :
    starRingEnd ℂ (℘'[L0] z) = ℘'[L0] (starRingEnd ℂ z) := by
  have h1 := (L0.hasSum_derivWeierstrassP z).map (starRingEnd ℂ) Complex.continuous_conj
  have h2 := conjLatticeEquiv.hasSum_iff.mpr (L0.hasSum_derivWeierstrassP (starRingEnd ℂ z))
  refine h1.unique ?_
  convert h2 using 1
  ext l
  simp [conjLatticeEquiv, map_ofNat]

private lemma weierstrassP_mul_rhoC (z : ℂ) : ℘[L0] (rhoC * z) = rhoC * ℘[L0] z := by
  have h1 := (L0.hasSum_weierstrassP z).mul_left rhoC
  have h2 := mulRhoEquiv.hasSum_iff.mpr (L0.hasSum_weierstrassP (rhoC * z))
  have heq : ((fun l : L0.lattice => 1 / (rhoC * z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2) ∘ mulRhoEquiv) =
      fun l : L0.lattice => rhoC * (1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2) := by
    funext l
    have hinv : (rhoC ^ 2)⁻¹ = rhoC :=
      eq_inv_of_mul_eq_one_left (by linear_combination rhoC_cube) |>.symm
    change 1 / (rhoC * z - rhoC * l.1) ^ 2 - 1 / (rhoC * l.1) ^ 2 =
      rhoC * (1 / (z - l.1) ^ 2 - 1 / l.1 ^ 2)
    have hsub : rhoC * z - rhoC * l.1 = rhoC * (z - l.1) := by ring
    rw [hsub, mul_pow, mul_pow, one_div, one_div, one_div, one_div, mul_inv, mul_inv,
      ← mul_sub, hinv]
  rw [heq] at h2
  exact h2.unique h1

private def w1 : ℂ := I / (Real.sqrt 3 : ℝ)

private lemma w1_notMem_L0 : w1 ∉ L0.lattice := by
  intro hw
  obtain ⟨m, n, hmn⟩ := mem_L0_iff.mp hw
  have him := congr_arg Complex.im hmn
  simp [w1, rhoC_im] at him
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h3n : (n : ℝ) * 3 = 2 := by
    have := congr_arg (· * (2 * Real.sqrt 3)) him
    field_simp [hpos.ne'] at this
    nlinarith [hsq]
  have h3n_int : n * 3 = 2 := by exact_mod_cast h3n
  omega

private lemma rhoC_mul_w1_sub_w1_mem_L0 : rhoC * w1 - w1 ∈ L0.lattice := by
  have h : rhoC * w1 - w1 = -1 - rhoC := by
    have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    apply Complex.ext
    · simp [w1, rhoC]
      field_simp [hpos.ne']
      nlinarith [hsq]
    · simp [w1, rhoC]
      field_simp [hpos.ne']
      nlinarith [hsq]
  rw [h]
  exact sub_mem (neg_mem one_mem_L0) rhoC_mem_L0

private lemma weierstrassP_w1 : ℘[L0] w1 = 0 := by
  have h1 : ℘[L0] (rhoC * w1) = ℘[L0] w1 := by
    have heq : rhoC * w1 = w1 + (rhoC * w1 - w1) := by ring
    rw [heq]
    exact L0.weierstrassP_add_coe w1 ⟨rhoC * w1 - w1, rhoC_mul_w1_sub_w1_mem_L0⟩
  rw [weierstrassP_mul_rhoC] at h1
  have h2 : (rhoC - 1) * ℘[L0] w1 = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr rhoC_ne_one)

private lemma derivWeierstrassP_w1_sq : ℘'[L0] w1 ^ 2 = -L0.g₃ := by
  have h := L0.derivWeierstrassP_sq w1 w1_notMem_L0
  rw [weierstrassP_w1, L0_g2_eq_zero] at h
  simpa using h

private lemma derivWeierstrassP_w1_ne_zero : ℘'[L0] w1 ≠ 0 := by
  intro h
  have hsq := derivWeierstrassP_w1_sq
  rw [h] at hsq
  exact L0_g3_ne_zero (by linear_combination hsq)

private lemma deriv_derivWeierstrassP_eq (z : ℂ) (hz : z ∉ L0.lattice) :
    deriv ℘'[L0] z = 6 * ℘[L0] z ^ 2 := by
  let U : Set ℂ := (L0.lattice : Set ℂ)ᶜ
  have hU_open : IsOpen U := L0.isClosed_lattice.isOpen_compl
  have hU_conn : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L0.lattice))).isPreconnected
  have h_ana1 : AnalyticOnNhd ℂ (deriv ℘'[L0]) U := L0.analyticOnNhd_derivWeierstrassP.deriv
  have h_ana2 : AnalyticOnNhd ℂ (fun w => 6 * ℘[L0] w ^ 2) U := by
    intro w hw
    exact analyticAt_const.mul ((L0.analyticOnNhd_weierstrassP w hw).pow 2)
  have h_prod_zero : ∀ w ∈ U, 2 * ℘'[L0] w * (deriv ℘'[L0] w - 6 * ℘[L0] w ^ 2) = 0 := by
    intro w hw
    have hwp : HasDerivAt ℘[L0] (℘'[L0] w) w := by
      have hd := (L0.differentiableOn_weierstrassP.differentiableAt (hU_open.mem_nhds hw)).hasDerivAt
      rwa [L0.deriv_weierstrassP] at hd
    have hwp' : HasDerivAt ℘'[L0] (deriv ℘'[L0] w) w :=
      (L0.differentiableOn_derivWeierstrassP.differentiableAt (hU_open.mem_nhds hw)).hasDerivAt
    have hL : HasDerivAt (fun x => ℘'[L0] x ^ 2) (2 * ℘'[L0] w * deriv ℘'[L0] w) w := by
      refine (hwp'.fun_pow 2).congr_deriv ?_
      ring
    have hR : HasDerivAt (fun x => 4 * ℘[L0] x ^ 3 - L0.g₃) (12 * ℘[L0] w ^ 2 * ℘'[L0] w) w := by
      refine (((hwp.fun_pow 3).const_mul (4 : ℂ)).sub_const L0.g₃).congr_deriv ?_
      ring
    have hev : (fun x => ℘'[L0] x ^ 2) =ᶠ[𝓝 w] (fun x => 4 * ℘[L0] x ^ 3 - L0.g₃) := by
      filter_upwards [hU_open.mem_nhds hw] with x hx
      simpa [L0_g2_eq_zero] using L0.derivWeierstrassP_sq x hx
    have hder := (hL.congr_of_eventuallyEq hev.symm).unique hR
    linear_combination hder
  have hev_eq : deriv ℘'[L0] =ᶠ[𝓝 w1] fun w => 6 * ℘[L0] w ^ 2 := by
    have hcont : ContinuousAt ℘'[L0] w1 :=
      (L0.differentiableOn_derivWeierstrassP.differentiableAt (hU_open.mem_nhds w1_notMem_L0)).continuousAt
    have hne : ∀ᶠ w in 𝓝 w1, ℘'[L0] w ≠ 0 :=
      hcont.eventually_ne derivWeierstrassP_w1_ne_zero
    filter_upwards [hU_open.mem_nhds w1_notMem_L0, hne] with w hw hwn
    have hp := h_prod_zero w hw
    have h2n : 2 * ℘'[L0] w ≠ 0 := mul_ne_zero (by norm_num) hwn
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left h2n)
  exact h_ana1.eqOn_of_preconnected_of_eventuallyEq h_ana2 hU_conn w1_notMem_L0 hev_eq hz

private lemma half_notMem_L0 : (1 / 2 : ℂ) ∉ L0.lattice := L0.ω₁_div_two_notMem_lattice

private lemma derivWeierstrassP_half : ℘'[L0] (1 / 2 : ℂ) = 0 := by
  have h1 : ℘'[L0] (1 / 2 : ℂ) = ℘'[L0] (-(1 / 2 : ℂ)) := by
    have : (1 / 2 : ℂ) = -(1 / 2 : ℂ) + (1 : ℂ) := by ring
    conv_lhs => rw [this]
    exact L0.derivWeierstrassP_add_coe (-(1 / 2 : ℂ)) ⟨1, one_mem_L0⟩
  rw [L0.derivWeierstrassP_neg] at h1
  linear_combination h1 / 2

private lemma weierstrassP_ofReal_im (x : ℝ) : (℘[L0] (x : ℂ)).im = 0 := by
  rw [← Complex.conj_eq_iff_im, conj_weierstrassP, Complex.conj_ofReal]

private lemma derivWeierstrassP_ofReal_im (x : ℝ) : (℘'[L0] (x : ℂ)).im = 0 := by
  rw [← Complex.conj_eq_iff_im, conj_derivWeierstrassP, Complex.conj_ofReal]

private def e1 : ℝ := (℘[L0] (1 / 2 : ℂ)).re

private lemma weierstrassP_half_eq : ℘[L0] (1 / 2 : ℂ) = (e1 : ℂ) := by
  apply Complex.ext
  · simp [e1]
  · simpa using weierstrassP_ofReal_im (1 / 2 : ℝ)

private lemma L0_g3_eq_four_e1_cube : L0.g₃ = 4 * (e1 : ℂ) ^ 3 := by
  have h := L0.derivWeierstrassP_sq (1 / 2 : ℂ) half_notMem_L0
  rw [derivWeierstrassP_half, weierstrassP_half_eq, L0_g2_eq_zero] at h
  linear_combination h

private lemma e1_ne_zero : e1 ≠ 0 := by
  intro h
  have hg := L0_g3_eq_four_e1_cube
  rw [h] at hg
  exact L0_g3_ne_zero (by simpa using hg)

private lemma I_mul_notMem_L0 {y : ℝ} (hy0 : 0 < y) (hy1 : y < Real.sqrt 3) :
    I * (y : ℂ) ∉ L0.lattice := by
  intro hm
  obtain ⟨m, n, hmn⟩ := mem_L0_iff.mp hm
  have hre := congr_arg Complex.re hmn
  have him := congr_arg Complex.im hmn
  simp [rhoC_re, rhoC_im] at hre him
  have hn_eq : (n : ℝ) = 2 * (m : ℝ) := by linarith
  have hn_int : n = 2 * m := by exact_mod_cast hn_eq
  rw [hn_int] at him
  push_cast at him
  have hm_eq : (m : ℝ) * Real.sqrt 3 = y := by linarith
  have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hm0 : (0 : ℝ) < m := by nlinarith
  have hm1 : (m : ℝ) < 1 := by nlinarith
  have hm0' : (0 : ℤ) < m := by exact_mod_cast hm0
  have hm1' : m < (1 : ℤ) := by exact_mod_cast hm1
  omega

private lemma e1_pos : 0 < e1 := by
  have hpos3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  let h : ℝ → ℝ := fun y => (℘[L0] (I * (y : ℂ))).re
  let h' : ℝ → ℝ := fun y => (I * ℘'[L0] (I * (y : ℂ))).re
  have him_h : ∀ y : ℝ, (℘[L0] (I * (y : ℂ))).im = 0 := by
    intro y
    rw [← Complex.conj_eq_iff_im, conj_weierstrassP]
    simp [L0.weierstrassP_neg]
  have hh_deriv : ∀ y ∈ Ioo (0 : ℝ) (Real.sqrt 3), HasDerivAt h (h' y) y := by
    intro y hy
    have hnot : I * (y : ℂ) ∉ L0.lattice := I_mul_notMem_L0 hy.1 hy.2
    have hwp : HasDerivAt ℘[L0] (℘'[L0] (I * (y : ℂ))) (I * (y : ℂ)) := by
      have hd := (L0.differentiableOn_weierstrassP.differentiableAt
        (L0.isClosed_lattice.isOpen_compl.mem_nhds hnot)).hasDerivAt
      rwa [L0.deriv_weierstrassP] at hd
    have hlin : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I y := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul I
    have hcomp : HasDerivAt (fun t : ℝ => ℘[L0] (I * (t : ℂ))) (I * ℘'[L0] (I * (y : ℂ))) y := by
      refine (hwp.scomp y hlin).congr_deriv ?_
      simp [smul_eq_mul]
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hcomp
  have hh'_deriv : ∀ y ∈ Ioo (0 : ℝ) (Real.sqrt 3), HasDerivAt h' (-6 * h y ^ 2) y := by
    intro y hy
    have hnot : I * (y : ℂ) ∉ L0.lattice := I_mul_notMem_L0 hy.1 hy.2
    have hwp' : HasDerivAt ℘'[L0] (6 * ℘[L0] (I * (y : ℂ)) ^ 2) (I * (y : ℂ)) := by
      have hd := (L0.differentiableOn_derivWeierstrassP.differentiableAt
        (L0.isClosed_lattice.isOpen_compl.mem_nhds hnot)).hasDerivAt
      rwa [deriv_derivWeierstrassP_eq _ hnot] at hd
    have hlin : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I y := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul I
    have hcomp : HasDerivAt (fun t : ℝ => I * ℘'[L0] (I * (t : ℂ)))
        (-6 * ℘[L0] (I * (y : ℂ)) ^ 2) y := by
      refine ((hwp'.scomp y hlin).const_mul I).congr_deriv ?_
      simp only [smul_eq_mul]
      calc I * (I * (6 * ℘[L0] (I * ↑y) ^ 2))
          = (I * I) * (6 * ℘[L0] (I * ↑y) ^ 2) := by ring
        _ = -6 * ℘[L0] (I * ↑y) ^ 2 := by rw [Complex.I_mul_I]; ring
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hcomp
    refine hre.congr_deriv ?_
    have hreal : ℘[L0] (I * (y : ℂ)) = (h y : ℂ) := by
      apply Complex.ext <;> simp [h, him_h y]
    simp only [Complex.reCLM_apply, hreal]
    norm_cast
  have hh'_anti : AntitoneOn h' (Ioo 0 (Real.sqrt 3)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 (Real.sqrt 3)) ?_ ?_ ?_
    · exact fun y hy => (hh'_deriv y hy).continuousAt.continuousWithinAt
    · exact fun y hy => (hh'_deriv y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hh'_deriv y (interior_subset hy)).deriv]
      nlinarith [sq_nonneg (h y)]
  have hmid_mem : Real.sqrt 3 / 2 ∈ Ioo (0 : ℝ) (Real.sqrt 3) := ⟨by positivity, by linarith⟩
  have hmid_eq : I * ((Real.sqrt 3 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) + rhoC := by
    apply Complex.ext
    · simp [rhoC]; ring
    · simp [rhoC]
  have hh'_mid : h' (Real.sqrt 3 / 2) = 0 := by
    dsimp [h']
    rw [hmid_eq, L0.derivWeierstrassP_add_coe (1 / 2 : ℂ) ⟨rhoC, rhoC_mem_L0⟩,
      derivWeierstrassP_half, mul_zero, zero_re]
  have hh_mid : h (Real.sqrt 3 / 2) = e1 := by
    dsimp [h, e1]
    rw [hmid_eq, L0.weierstrassP_add_coe (1 / 2 : ℂ) ⟨rhoC, rhoC_mem_L0⟩]
  have hh_mono : MonotoneOn h (Ioc 0 (Real.sqrt 3 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 (Real.sqrt 3 / 2)) ?_ ?_ ?_
    · intro y hy
      exact (hh_deriv y ⟨hy.1, lt_of_le_of_lt hy.2 hmid_mem.2⟩).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioc] at hy
      exact (hh_deriv y ⟨hy.1, lt_trans hy.2 hmid_mem.2⟩).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ioc] at hy
      have hy_mem : y ∈ Ioo (0 : ℝ) (Real.sqrt 3) := ⟨hy.1, lt_trans hy.2 hmid_mem.2⟩
      rw [(hh_deriv y hy_mem).deriv, ← hh'_mid]
      exact hh'_anti hy_mem hmid_mem hy.2.le
  have h13_le : 1 / Real.sqrt 3 ≤ Real.sqrt 3 / 2 := by
    rw [div_le_div_iff₀ hpos3 (by norm_num)]
    nlinarith [hsq3]
  have h13_mem : 1 / Real.sqrt 3 ∈ Ioc (0 : ℝ) (Real.sqrt 3 / 2) := ⟨by positivity, h13_le⟩
  have hmid_mem' : Real.sqrt 3 / 2 ∈ Ioc (0 : ℝ) (Real.sqrt 3 / 2) := ⟨by positivity, le_rfl⟩
  have h13_zero : h (1 / Real.sqrt 3) = 0 := by
    dsimp [h]
    have : I * ((1 / Real.sqrt 3 : ℝ) : ℂ) = w1 := by
      simp [w1, div_eq_mul_inv]
    rw [this, weierstrassP_w1, zero_re]
  have hle : 0 ≤ e1 := by
    rw [← h13_zero, ← hh_mid]
    exact hh_mono h13_mem hmid_mem' h13_le
  exact lt_of_le_of_ne hle e1_ne_zero.symm

private lemma real_notMem_L0 {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : (x : ℂ) ∉ L0.lattice := by
  intro hm
  obtain ⟨m, n, hmn⟩ := mem_L0_iff.mp hm
  have hn : n = 0 := by simpa [rhoC_im] using congr_arg Complex.im hmn
  subst hn
  have hre := congr_arg Complex.re hmn
  simp at hre
  have hm0 : (0 : ℤ) < m := by exact_mod_cast (hre.symm ▸ hx0 : (0 : ℝ) < m)
  have hm1 : m < (1 : ℤ) := by exact_mod_cast (hre.symm ▸ hx1 : (m : ℝ) < 1)
  omega

private def wpR (x : ℝ) : ℝ := (℘[L0] (x : ℂ)).re
private def wpR' (x : ℝ) : ℝ := (℘'[L0] (x : ℂ)).re

private lemma wpR_coe (x : ℝ) : ℘[L0] (x : ℂ) = (wpR x : ℂ) := by
  apply Complex.ext <;> simp [wpR, weierstrassP_ofReal_im]

private lemma wpR'_coe (x : ℝ) : ℘'[L0] (x : ℂ) = (wpR' x : ℂ) := by
  apply Complex.ext <;> simp [wpR', derivWeierstrassP_ofReal_im]

private lemma hasDerivAt_wpR {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt wpR (wpR' x) x := by
  have hnot := real_notMem_L0 hx0 hx1
  have hwp : HasDerivAt ℘[L0] (℘'[L0] (x : ℂ)) (x : ℂ) := by
    have hd := (L0.differentiableOn_weierstrassP.differentiableAt
      (L0.isClosed_lattice.isOpen_compl.mem_nhds hnot)).hasDerivAt
    rwa [L0.deriv_weierstrassP] at hd
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hwp.comp_ofReal

private lemma hasDerivAt_wpR' {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt wpR' (6 * wpR x ^ 2) x := by
  have hnot := real_notMem_L0 hx0 hx1
  have hwp' : HasDerivAt ℘'[L0] (6 * ℘[L0] (x : ℂ) ^ 2) (x : ℂ) := by
    have hd := (L0.differentiableOn_derivWeierstrassP.differentiableAt
      (L0.isClosed_lattice.isOpen_compl.mem_nhds hnot)).hasDerivAt
    rwa [deriv_derivWeierstrassP_eq _ hnot] at hd
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hwp'.comp_ofReal
  refine hre.congr_deriv ?_
  simp only [Complex.reCLM_apply, wpR_coe]
  norm_cast

private lemma wpR'_sq {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    wpR' x ^ 2 = 4 * wpR x ^ 3 - 4 * e1 ^ 3 := by
  have h := L0.derivWeierstrassP_sq (x : ℂ) (real_notMem_L0 hx0 hx1)
  rw [wpR_coe, wpR'_coe, L0_g2_eq_zero, L0_g3_eq_four_e1_cube] at h
  norm_cast at h
  linarith

private lemma wpR_gt_e1_and_wpR'_neg {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    e1 < wpR x ∧ wpR' x < 0 := by
  have hmono' : MonotoneOn wpR' (Ioo 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 1) ?_ ?_ ?_
    · exact fun t ht => (hasDerivAt_wpR' ht.1 ht.2).continuousAt.continuousWithinAt
    · exact fun t ht => (hasDerivAt_wpR' (interior_subset ht).1 (interior_subset ht).2).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hasDerivAt_wpR' (interior_subset ht).1 (interior_subset ht).2).deriv]
      positivity
  have hhalf_zero : wpR' (1 / 2) = 0 := by
    dsimp [wpR']
    norm_num [derivWeierstrassP_half]
  have hanti : AntitoneOn wpR (Ioc 0 (1 / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 (1 / 2)) ?_ ?_ ?_
    · exact fun t ht => (hasDerivAt_wpR ht.1 (by linarith [ht.2])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      exact (hasDerivAt_wpR ht.1 (by linarith [ht.2])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      rw [(hasDerivAt_wpR ht.1 (by linarith [ht.2])).deriv, ← hhalf_zero]
      exact hmono' ⟨ht.1, by linarith [ht.2]⟩ ⟨by norm_num, by norm_num⟩ ht.2.le
  have hge_e1 : ∀ t ∈ Ioc (0 : ℝ) (1 / 2), e1 ≤ wpR t := by
    intro t ht
    have h12 : wpR (1 / 2) = e1 := by simp [wpR, e1]
    rw [← h12]
    exact hanti ht ⟨by norm_num, le_rfl⟩ ht.2
  have hstrict' : StrictMonoOn wpR' (Ioc 0 (1 / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioc 0 (1 / 2)) ?_ ?_
    · exact fun t ht => (hasDerivAt_wpR' ht.1 (by linarith [ht.2])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      rw [(hasDerivAt_wpR' ht.1 (by linarith [ht.2])).deriv]
      have := hge_e1 t ⟨ht.1, ht.2.le⟩
      nlinarith [e1_pos]
  have hwp'_neg : wpR' x < 0 := by
    rw [← hhalf_zero]
    exact hstrict' ⟨hx0, hx1.le⟩ ⟨by norm_num, le_rfl⟩ hx1
  have hstrict : StrictAntiOn wpR (Ioc 0 (1 / 2)) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioc 0 (1 / 2)) ?_ ?_
    · exact fun t ht => (hasDerivAt_wpR ht.1 (by linarith [ht.2])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioc] at ht
      rw [(hasDerivAt_wpR ht.1 (by linarith [ht.2])).deriv, ← hhalf_zero]
      exact hstrict' ⟨ht.1, ht.2.le⟩ ⟨by norm_num, le_rfl⟩ ht.2
  have hwp_gt : e1 < wpR x := by
    have h12 : wpR (1 / 2) = e1 := by simp [wpR, e1]
    rw [← h12]
    exact hstrict ⟨hx0, hx1.le⟩ ⟨by norm_num, le_rfl⟩ hx1
  exact ⟨hwp_gt, hwp'_neg⟩

private lemma wpR'_eq_neg_sqrt {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    wpR' x = -Real.sqrt (4 * wpR x ^ 3 - 4 * e1 ^ 3) := by
  have hsq := wpR'_sq hx0 (by linarith)
  have hneg := (wpR_gt_e1_and_wpR'_neg hx0 hx1).2
  have hnn : 0 ≤ 4 * wpR x ^ 3 - 4 * e1 ^ 3 := by nlinarith [sq_nonneg (wpR' x)]
  have h2 : (-wpR' x) ^ 2 = (Real.sqrt (4 * wpR x ^ 3 - 4 * e1 ^ 3)) ^ 2 := by
    rw [Real.sq_sqrt hnn]
    linarith
  have hpos1 : 0 ≤ -wpR' x := by linarith
  have hpos2 : 0 ≤ Real.sqrt (4 * wpR x ^ 3 - 4 * e1 ^ 3) := Real.sqrt_nonneg _
  have := (sq_eq_sq₀ hpos1 hpos2).mp h2
  linarith

private lemma three_mul_sqrt_e1_eq_gamma :
    3 * Real.sqrt e1 = Real.Gamma (1 / 6) * Real.sqrt Real.pi / Real.Gamma (2 / 3) := by
  have he1_pos : 0 < e1 := e1_pos
  let phi : ℝ → ℝ := fun x => if x = 0 then 0 else (e1 / wpR x) ^ 3
  let phi' : ℝ → ℝ := fun x =>
    6 * Real.sqrt e1 * phi x ^ (5 / 6 : ℝ) * (1 - phi x) ^ (1 / 2 : ℝ)
  let g : ℝ → ℝ := fun s => s ^ (-5 / 6 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ)
  have hphi0 : phi 0 = 0 := by simp [phi]
  have hphi_half : phi (1 / 2) = 1 := by
    have h12 : wpR (1 / 2) = e1 := by simp [wpR, e1]
    dsimp only [phi]
    rw [if_neg (by norm_num : (1 / 2 : ℝ) ≠ 0), h12, div_self e1_ne_zero, one_pow]
  have hphi_Ioo : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), 0 < phi x ∧ phi x < 1 := by
    intro x hx
    have hgt := (wpR_gt_e1_and_wpR'_neg hx.1 hx.2).1
    have hwp_pos : 0 < wpR x := lt_trans he1_pos hgt
    have hne : x ≠ 0 := hx.1.ne'
    simp only [phi, if_neg hne]
    refine ⟨by positivity, ?_⟩
    have hlt1 : e1 / wpR x < 1 := (div_lt_one hwp_pos).mpr hgt
    have hnn : 0 ≤ e1 / wpR x := by positivity
    nlinarith [sq_nonneg (e1 / wpR x)]
  have hphi_cont : ContinuousOn phi (uIcc 0 (1 / 2)) := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      let denomR : ℝ → ℝ := fun t => ((t : ℂ) ^ 2 * ℘[L0 - (0 : ℂ)] (t : ℂ) + 1).re
      have hdenom_cont : ContinuousAt denomR 0 := by
        have ha : ContinuousAt (fun z : ℂ => z ^ 2 * ℘[L0 - (0 : ℂ)] z + 1) 0 := by
          have h0 := (L0.analyticAt_weierstrassPExcept (0 : ℂ)).continuousAt
          exact ((continuous_pow 2).continuousAt.mul h0).add continuousAt_const
        have hcomp : ContinuousAt (fun t : ℝ => (t : ℂ) ^ 2 * ℘[L0 - (0 : ℂ)] (t : ℂ) + 1) 0 :=
          ContinuousAt.comp (g := fun z : ℂ => z ^ 2 * ℘[L0 - (0 : ℂ)] z + 1)
            ha Complex.continuous_ofReal.continuousAt
        exact Complex.continuous_re.continuousAt.comp hcomp
      have hdenom0 : denomR 0 = 1 := by simp [denomR]
      let aux : ℝ → ℝ := fun t => (e1 * t ^ 2 / denomR t) ^ 3
      have haux_cont : ContinuousAt aux 0 := by
        refine ((ContinuousAt.div ?_ hdenom_cont (by rw [hdenom0]; norm_num)).pow 3)
        fun_prop
      have heq_on : Set.EqOn phi aux (Icc 0 (1 / 2)) := by
        intro t ht
        by_cases ht0 : t = 0
        · simp [phi, aux, ht0]
        · have hadd := L0.weierstrassPExcept_add 0 (t : ℂ)
          have hmul : (t : ℂ) ^ 2 * ℘[L0] (t : ℂ) = (t : ℂ) ^ 2 * ℘[L0 - (0 : ℂ)] (t : ℂ) + 1 := by
            rw [← hadd]
            simp only [Submodule.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              zero_pow, div_zero, sub_zero]
            have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
            field_simp [htc]
          have hden_eq : denomR t = t ^ 2 * wpR t := by
            dsimp only [denomR, wpR]
            rw [← hmul, wpR_coe]
            norm_cast
          simp only [phi, aux, if_neg ht0, hden_eq]
          congr 1
          field_simp [ht0]
      exact (haux_cont.continuousWithinAt).congr heq_on (heq_on ⟨le_rfl, by norm_num⟩)
    · have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      have hwp_cont : ContinuousAt wpR x := (hasDerivAt_wpR hx_pos (by linarith [hx.2])).continuousAt
      have hwp_ne : wpR x ≠ 0 := by
        rcases eq_or_lt_of_le hx.2 with rfl | hlt
        · have : wpR (1 / 2) = e1 := by simp [wpR, e1]
          rw [this]; exact e1_ne_zero
        · exact (lt_trans he1_pos (wpR_gt_e1_and_wpR'_neg hx_pos hlt).1).ne'
      have hcont : ContinuousAt (fun t => (e1 / wpR t) ^ 3) x :=
        (continuousAt_const.div hwp_cont hwp_ne).pow 3
      have hev : phi =ᶠ[𝓝 x] fun t => (e1 / wpR t) ^ 3 := by
        filter_upwards [isOpen_ne.mem_nhds hx0] with t ht
        simp [phi, ht]
      exact (hcont.congr hev.symm).continuousWithinAt
  have hphi_deriv : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), HasDerivAt phi (phi' x) x := by
    intro x hx
    have hgt := (wpR_gt_e1_and_wpR'_neg hx.1 hx.2).1
    have hwp_pos : 0 < wpR x := lt_trans he1_pos hgt
    have hphi_val : phi x = (e1 / wpR x) ^ 3 := if_neg hx.1.ne'
    have h01 := hphi_Ioo x hx
    have hd1 : HasDerivAt (fun t => (e1 / wpR t) ^ 3)
        (-3 * e1 ^ 3 * wpR' x / wpR x ^ 4) x := by
      have hdiv : HasDerivAt (fun t => e1 / wpR t) (-(e1 * wpR' x) / wpR x ^ 2) x := by
        refine ((hasDerivAt_const x e1).fun_div (hasDerivAt_wpR hx.1 (by linarith [hx.2]))
          hwp_pos.ne').congr_deriv ?_
        ring
      refine (hdiv.fun_pow 3).congr_deriv ?_
      rw [div_pow]
      field_simp [hwp_pos.ne']
      ring
    have hev : phi =ᶠ[𝓝 x] fun t => (e1 / wpR t) ^ 3 := by
      filter_upwards [isOpen_ne.mem_nhds hx.1.ne'] with t ht
      simp [phi, ht]
    have hd2 : HasDerivAt phi (-3 * e1 ^ 3 * wpR' x / wpR x ^ 4) x :=
      hd1.congr_of_eventuallyEq hev
    refine hd2.congr_deriv ?_
    rw [wpR'_eq_neg_sqrt hx.1 hx.2]
    have hL_nn : 0 ≤ phi' x := by
      dsimp [phi']
      have h1 : 0 ≤ phi x ^ (5 / 6 : ℝ) := Real.rpow_nonneg h01.1.le _
      have h2 : 0 ≤ (1 - phi x) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (sub_nonneg.mpr h01.2.le) _
      positivity
    have hR_nn : 0 ≤ -3 * e1 ^ 3 * -Real.sqrt (4 * wpR x ^ 3 - 4 * e1 ^ 3) / wpR x ^ 4 := by
      have : -3 * e1 ^ 3 * -Real.sqrt (4 * wpR x ^ 3 - 4 * e1 ^ 3) =
          3 * e1 ^ 3 * Real.sqrt (4 * wpR x ^ 3 - 4 * e1 ^ 3) := by ring
      rw [this]
      positivity
    refine (pow_left_inj₀ hR_nn hL_nn (by norm_num : 6 ≠ 0)).mp ?_
    have hcube_le : e1 ^ 3 ≤ wpR x ^ 3 := pow_le_pow_left₀ he1_pos.le hgt.le 3
    have hp1 : (phi x ^ (5 / 6 : ℝ)) ^ 6 = phi x ^ 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h01.1.le]
      norm_num
    have hp2 : ((1 - phi x) ^ (1 / 2 : ℝ)) ^ 6 = (1 - phi x) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (sub_nonneg.mpr h01.2.le)]
      norm_num
    have hp3 : (Real.sqrt e1) ^ 6 = e1 ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt he1_pos.le]
    have hp4 : (Real.sqrt (4 * wpR x ^ 3 - 4 * e1 ^ 3)) ^ 6 = (4 * wpR x ^ 3 - 4 * e1 ^ 3) ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt (by linarith)]
    have hLHS6 : (-3 * e1 ^ 3 * -Real.sqrt (4 * wpR x ^ 3 - 4 * e1 ^ 3) / wpR x ^ 4) ^ 6 =
        (3 * e1 ^ 3) ^ 6 * (4 * wpR x ^ 3 - 4 * e1 ^ 3) ^ 3 / (wpR x ^ 4) ^ 6 := by
      rw [div_pow, show (-3 * e1 ^ 3 * -Real.sqrt (4 * wpR x ^ 3 - 4 * e1 ^ 3)) ^ 6 =
        (3 * e1 ^ 3) ^ 6 * (Real.sqrt (4 * wpR x ^ 3 - 4 * e1 ^ 3)) ^ 6 by ring, hp4]
    have hRHS6 : (phi' x) ^ 6 = 6 ^ 6 * e1 ^ 3 * (e1 ^ 3 / wpR x ^ 3) ^ 5 *
        (1 - e1 ^ 3 / wpR x ^ 3) ^ 3 := by
      dsimp [phi']
      rw [mul_pow, mul_pow, mul_pow, hp1, hp2, hp3, hphi_val, div_pow]
    rw [hLHS6, hRHS6]
    field_simp [hwp_pos.ne']
    ring
  have hphi'_nn : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), 0 ≤ phi' x := by
    intro x hx
    have h01 := hphi_Ioo x hx
    dsimp [phi']
    have h1 : 0 ≤ phi x ^ (5 / 6 : ℝ) := Real.rpow_nonneg h01.1.le _
    have h2 : 0 ≤ (1 - phi x) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (sub_nonneg.mpr h01.2.le) _
    positivity
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (g := g)
    hphi_cont (by simpa [min_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2),
      max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hphi_deriv)
    (by simpa [min_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2),
      max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hphi'_nn)
  rw [hphi0, hphi_half] at hsub
  have hconst_int : (∫ x in (0 : ℝ)..(1 / 2), (g ∘ phi) x * phi' x) = 3 * Real.sqrt e1 := by
    have hcongr : ∫ x in (0 : ℝ)..(1 / 2), (g ∘ phi) x * phi' x =
        ∫ x in (0 : ℝ)..(1 / 2), (6 * Real.sqrt e1) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hne_ae : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (1 / 2 : ℝ) := by
        rw [MeasureTheory.ae_iff]
        simp
      filter_upwards [hne_ae] with x hxne hx
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
      have hx_oo : x ∈ Ioo (0 : ℝ) (1 / 2) := ⟨hx.1, lt_of_le_of_ne hx.2 hxne⟩
      have h01 := hphi_Ioo x hx_oo
      simp only [Function.comp_apply, g, phi']
      have hp1 : phi x ^ (-5 / 6 : ℝ) * phi x ^ (5 / 6 : ℝ) = 1 := by
        rw [← Real.rpow_add h01.1]
        norm_num
      have hp2 : (1 - phi x) ^ (-1 / 2 : ℝ) * (1 - phi x) ^ (1 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add (sub_pos.mpr h01.2)]
        norm_num
      calc phi x ^ (-5 / 6 : ℝ) * (1 - phi x) ^ (-1 / 2 : ℝ) *
            (6 * Real.sqrt e1 * phi x ^ (5 / 6 : ℝ) * (1 - phi x) ^ (1 / 2 : ℝ))
          = 6 * Real.sqrt e1 * (phi x ^ (-5 / 6 : ℝ) * phi x ^ (5 / 6 : ℝ)) *
            ((1 - phi x) ^ (-1 / 2 : ℝ) * (1 - phi x) ^ (1 / 2 : ℝ)) := by ring
        _ = 6 * Real.sqrt e1 := by rw [hp1, hp2]; ring
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hreal_int : ∫ s in (0 : ℝ)..1, g s = 3 * Real.sqrt e1 := by
    rw [← hsub, hconst_int]
  have hbeta_eq : Complex.betaIntegral (1 / 6) (1 / 2) = ((3 * Real.sqrt e1 : ℝ) : ℂ) := by
    rw [← hreal_int, ← intervalIntegral.integral_ofReal, Complex.betaIntegral]
    refine intervalIntegral.integral_congr_ae ?_
    have hne_ae : ∀ᵐ s ∂MeasureTheory.volume, s ≠ (1 : ℝ) := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne_ae] with s hsne hs
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hs1 : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hsne)
    simp only [g, Complex.ofReal_mul]
    rw [show (1 / 6 : ℂ) - 1 = ((-5 / 6 : ℝ) : ℂ) by norm_num,
      show (1 / 2 : ℂ) - 1 = ((-1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hs.1.le,
      show (1 : ℂ) - (s : ℂ) = ((1 - s : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow hs1.le]
  have hbeta_gamma := Complex.betaIntegral_eq_Gamma_mul_div (1 / 6) (1 / 2)
    (by norm_num) (by norm_num)
  rw [hbeta_eq, show (1 / 6 : ℂ) + 1 / 2 = ((2 / 3 : ℝ) : ℂ) by norm_num,
    show (1 / 6 : ℂ) = ((1 / 6 : ℝ) : ℂ) by norm_num,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Real.Gamma_one_half_eq] at hbeta_gamma
  exact_mod_cast hbeta_gamma

/- ### Part 5: The extremal map `G : 𝔻 → ℂ \ L0.lattice` -/

private def A : ℝ := e1 / 12

private lemma A_pos : 0 < A := by dsimp [A]; linarith [e1_pos]

private def c0 : ℂ := -((Real.pi : ℂ) * I) / (3 * (Real.sqrt A : ℝ))

private def P (τ : ℍ) : ℂ := (A : ℂ) * (ModularForm.E₄ τ / ModularForm.eta τ ^ 8)

private def Q (τ : ℍ) : ℂ :=
  2 * ((Real.sqrt A ^ 3 : ℝ) : ℂ) * (ModularForm.E₆ τ / ModularForm.eta τ ^ 12)

private lemma Q_sq_eq (τ : ℍ) : Q τ ^ 2 = 4 * P τ ^ 3 - L0.g₃ := by
  have heta : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hdisc := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  change ModularForm.eta τ ^ 24 = (ModularForm.E₄ τ ^ 3 - ModularForm.E₆ τ ^ 2) / 1728 at hdisc
  have h1728 : ModularForm.E₄ τ ^ 3 - ModularForm.E₆ τ ^ 2 = 1728 * ModularForm.eta τ ^ 24 := by
    linear_combination -1728 * hdisc
  have hsqA : (Real.sqrt A : ℂ) ^ 2 = (A : ℂ) := by
    exact_mod_cast Real.sq_sqrt A_pos.le
  have hA3 : 4 * (A : ℂ) ^ 3 * 1728 = L0.g₃ := by
    rw [L0_g3_eq_four_e1_cube]
    dsimp [A]
    push_cast
    ring
  dsimp [P, Q]
  have hpow6 : ((Real.sqrt A ^ 3 : ℝ) : ℂ) ^ 2 = (A : ℂ) ^ 3 := by
    push_cast
    rw [show (Real.sqrt A : ℂ) ^ 3 = (Real.sqrt A : ℂ) ^ 2 * (Real.sqrt A : ℂ) by ring]
    linear_combination ((Real.sqrt A : ℂ) ^ 2 + (A : ℂ)) * (A : ℂ) * hsqA +
      (Real.sqrt A : ℂ) ^ 2 * (Real.sqrt A : ℂ) ^ 2 * hsqA
  rw [mul_pow, mul_pow, hpow6, div_pow]
  conv_rhs => rw [mul_pow, div_pow]
  field_simp [heta]
  linear_combination -4 * (A : ℂ) ^ 3 * h1728 - ModularForm.eta τ ^ 24 * hA3

private lemma hasDerivAt_P (τ : ℍ) :
    HasDerivAt (P ∘ UpperHalfPlane.ofComplex) (c0 * ModularForm.eta τ ^ 4 * Q τ) (τ : ℂ) := by
  have heta : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hd_eta : HasDerivAt ModularForm.eta (ModularForm.eta τ * (Real.pi * I / 12 * EisensteinSeries.E2 τ)) (τ : ℂ) := by
    have hlog := ModularForm.logDeriv_eta_eq_E2 τ
    rw [logDeriv_apply] at hlog
    have hd := (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet τ.2).hasDerivAt
    refine hd.congr_deriv ?_
    rw [div_eq_iff heta] at hlog
    linear_combination hlog
  have hd_eta8 : HasDerivAt (fun w => ModularForm.eta w ^ 8)
      (8 * ModularForm.eta τ ^ 8 * (Real.pi * I / 12 * EisensteinSeries.E2 τ)) (τ : ℂ) := by
    refine (hd_eta.fun_pow 8).congr_deriv ?_
    ring
  have hd_E4 : HasDerivAt (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex)
      (2 * Real.pi * I * Derivative.normalizedDerivOfComplex (ModularForm.E₄ : ℍ → ℂ) τ) (τ : ℂ) := by
    have hd := (UpperHalfPlane.mdifferentiableAt_iff.mp (ModularForm.E₄.holo' τ)).hasDerivAt
    refine hd.congr_deriv ?_
    rw [Derivative.normalizedDerivOfComplex]
    have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    field_simp [h2pi]
    rfl
  have hd_quot := (hd_E4.fun_div hd_eta8 (pow_ne_zero 8 heta)).const_mul (A : ℂ)
  have hev : (P ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      fun w => (A : ℂ) * ((ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) w / ModularForm.eta w ^ 8) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.2] with w hw
    simp [P, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  refine (hd_quot.congr_of_eventuallyEq hev).congr_deriv ?_
  have hserre := congr_fun serreDerivative_E4 τ
  simp only [Derivative.serreDerivative_apply, Pi.smul_apply, smul_eq_mul] at hserre
  have hsqA : (Real.sqrt A : ℂ) ^ 2 = (A : ℂ) := by exact_mod_cast Real.sq_sqrt A_pos.le
  have hrtA_ne : (Real.sqrt A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr A_pos).ne'
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply, c0, Q]
  push_cast
  field_simp [heta, hrtA_ne]
  have hD : Derivative.normalizedDerivOfComplex (ModularForm.E₄ : ℍ → ℂ) τ =
      4 * 12⁻¹ * EisensteinSeries.E2 τ * ModularForm.E₄ τ + (-1 / 3) * ModularForm.E₆ τ := by
    linear_combination hserre
  rw [hD]
  linear_combination 24 * ModularForm.E₆ τ * hsqA

private lemma hasDerivAt_Q (τ : ℍ) :
    HasDerivAt (Q ∘ UpperHalfPlane.ofComplex) (6 * (c0 * ModularForm.eta τ ^ 4) * P τ ^ 2) (τ : ℂ) := by
  have hdiffQ : DifferentiableOn ℂ (Q ∘ UpperHalfPlane.ofComplex) upperHalfPlaneSet := by
    intro w hw
    have hev : (Q ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 w]
        fun z => 2 * ((Real.sqrt A ^ 3 : ℝ) : ℂ) *
          ((ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) z / ModularForm.eta z ^ 12) := by
      filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw] with z hz
      simp [Q, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have hd : DifferentiableAt ℂ
        (fun z => 2 * ((Real.sqrt A ^ 3 : ℝ) : ℂ) *
          ((ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) z / ModularForm.eta z ^ 12)) w := by
      have h1 := UpperHalfPlane.mdifferentiableAt_iff.mp (ModularForm.E₆.holo' ⟨w, hw⟩)
      have h2 := (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hw).pow 12
      exact (h1.div h2 (pow_ne_zero 12 (ModularForm.eta_ne_zero hw))).const_mul _
    exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  have hdiffRHS : DifferentiableOn ℂ
      (fun z => 6 * (c0 * ModularForm.eta z ^ 4) * (P ∘ UpperHalfPlane.ofComplex) z ^ 2)
      upperHalfPlaneSet := by
    intro w hw
    have hP : DifferentiableAt ℂ (P ∘ UpperHalfPlane.ofComplex) w :=
      (hasDerivAt_P ⟨w, hw⟩).differentiableAt
    have he : DifferentiableAt ℂ ModularForm.eta w :=
      ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hw
    exact ((he.pow 4).const_mul c0 |>.const_mul 6 |>.mul (hP.pow 2)).differentiableWithinAt
  have hana1 : AnalyticOnNhd ℂ (deriv (Q ∘ UpperHalfPlane.ofComplex)) upperHalfPlaneSet :=
    (hdiffQ.deriv UpperHalfPlane.isOpen_upperHalfPlaneSet).analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hana2 : AnalyticOnNhd ℂ
      (fun z => 6 * (c0 * ModularForm.eta z ^ 4) * (P ∘ UpperHalfPlane.ofComplex) z ^ 2)
      upperHalfPlaneSet :=
    hdiffRHS.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hconn : IsPreconnected upperHalfPlaneSet :=
    (convex_halfSpace_im_gt 0).isPreconnected
  have hprod : ∀ z ∈ upperHalfPlaneSet,
      2 * (Q ∘ UpperHalfPlane.ofComplex) z *
        (deriv (Q ∘ UpperHalfPlane.ofComplex) z -
          6 * (c0 * ModularForm.eta z ^ 4) * (P ∘ UpperHalfPlane.ofComplex) z ^ 2) = 0 := by
    intro z hz
    let τz : ℍ := ⟨z, hz⟩
    have hdQ : HasDerivAt (Q ∘ UpperHalfPlane.ofComplex)
        (deriv (Q ∘ UpperHalfPlane.ofComplex) z) z :=
      (hdiffQ.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)).hasDerivAt
    have hdP : HasDerivAt (P ∘ UpperHalfPlane.ofComplex)
        (c0 * ModularForm.eta z ^ 4 * (Q ∘ UpperHalfPlane.ofComplex) z) z := by
      simpa [τz, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using hasDerivAt_P τz
    have hL : HasDerivAt (fun w => (Q ∘ UpperHalfPlane.ofComplex) w ^ 2)
        (2 * (Q ∘ UpperHalfPlane.ofComplex) z * deriv (Q ∘ UpperHalfPlane.ofComplex) z) z := by
      refine (hdQ.fun_pow 2).congr_deriv ?_
      ring
    have hR : HasDerivAt (fun w => 4 * (P ∘ UpperHalfPlane.ofComplex) w ^ 3 - L0.g₃)
        (12 * (P ∘ UpperHalfPlane.ofComplex) z ^ 2 *
          (c0 * ModularForm.eta z ^ 4 * (Q ∘ UpperHalfPlane.ofComplex) z)) z := by
      refine (((hdP.fun_pow 3).const_mul (4 : ℂ)).sub_const L0.g₃).congr_deriv ?_
      ring
    have hev : (fun w => (Q ∘ UpperHalfPlane.ofComplex) w ^ 2) =ᶠ[𝓝 z]
        fun w => 4 * (P ∘ UpperHalfPlane.ofComplex) w ^ 3 - L0.g₃ := by
      filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
      simpa [UpperHalfPlane.ofComplex_apply_of_im_pos hw] using Q_sq_eq ⟨w, hw⟩
    have hder := (hL.congr_of_eventuallyEq hev.symm).unique hR
    linear_combination hder
  have hQ_rho_ne : (Q ∘ UpperHalfPlane.ofComplex) rhoC ≠ 0 := by
    have hval : (Q ∘ UpperHalfPlane.ofComplex) rhoC = Q rhoH := by
      simp [UpperHalfPlane.ofComplex_apply_of_im_pos rhoC_im_pos, rhoH]
    rw [hval]
    intro h0
    have hsq := Q_sq_eq rhoH
    have hP0 : P rhoH = 0 := by simp [P, E4_rhoH]
    rw [h0, hP0] at hsq
    exact L0_g3_ne_zero (by linear_combination hsq)
  have hev_eq : deriv (Q ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 rhoC]
      fun z => 6 * (c0 * ModularForm.eta z ^ 4) * (P ∘ UpperHalfPlane.ofComplex) z ^ 2 := by
    have hcont : ContinuousAt (Q ∘ UpperHalfPlane.ofComplex) rhoC :=
      (hdiffQ.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds rhoC_im_pos)).continuousAt
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds rhoC_im_pos,
      hcont.eventually_ne hQ_rho_ne] with z hz hzne
    have hp := hprod z hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (mul_ne_zero (by norm_num) hzne))
  have hder_eq := hana1.eqOn_of_preconnected_of_eventuallyEq hana2 hconn rhoC_im_pos hev_eq τ.2
  have hd := (hdiffQ.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.2)).hasDerivAt
  rw [hder_eq] at hd
  simpa [UpperHalfPlane.ofComplex_apply_of_im_pos τ.2] using hd

private def psi (z : ℂ) : ℂ := (rhoC - starRingEnd ℂ rhoC * z) / (1 - z)

private lemma psi_zero : psi 0 = rhoC := by simp [psi]

private lemma one_sub_ne_zero_of_mem_ball {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) : 1 - z ≠ 0 := by
  intro h
  have hz1 : z = 1 := by linear_combination -h
  rw [Metric.mem_ball, dist_zero_right, hz1, norm_one] at hz
  exact lt_irrefl 1 hz

private lemma psi_im_pos {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) : 0 < (psi z).im := by
  have hne : 1 - z ≠ 0 := one_sub_ne_zero_of_mem_ball hz
  have hnz : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hne
  have hzn : Complex.normSq z < 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  dsimp [psi]
  rw [Complex.div_im, ← sub_div]
  have hnum : (rhoC - starRingEnd ℂ rhoC * z).im * (1 - z).re -
      (rhoC - starRingEnd ℂ rhoC * z).re * (1 - z).im =
      (Real.sqrt 3 / 2) * (1 - Complex.normSq z) := by
    simp [Complex.normSq_apply, rhoC_re, rhoC_im]
    ring
  rw [hnum]
  exact div_pos (mul_pos (by positivity) (sub_pos.mpr hzn)) hnz

private lemma hasDerivAt_psi {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    HasDerivAt psi (I * (Real.sqrt 3 : ℝ) / (1 - z) ^ 2) z := by
  have hne := one_sub_ne_zero_of_mem_ball hz
  have h1 : HasDerivAt (fun w => rhoC - starRingEnd ℂ rhoC * w) (-starRingEnd ℂ rhoC) z := by
    refine ((hasDerivAt_const z rhoC).fun_sub
      ((hasDerivAt_id z).const_mul (starRingEnd ℂ rhoC))).congr_deriv ?_
    ring
  have h2 : HasDerivAt (fun w => 1 - w) (-1) z := by
    refine ((hasDerivAt_const z (1 : ℂ)).fun_sub (hasDerivAt_id z)).congr_deriv ?_
    ring
  refine (h1.fun_div h2 hne).congr_deriv ?_
  have hsub := rhoC_sub_conj
  field_simp [hne]
  linear_combination hsub

private lemma exists_extremal_map :
    ∃ G : ℂ → ℂ,
      (∀ z ∈ Metric.ball (0 : ℂ) 1,
        HasDerivAt G (c0 * ModularForm.eta (psi z) ^ 4 * (I * (Real.sqrt 3 : ℝ) / (1 - z) ^ 2)) z) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, G z ∉ L0.lattice) := by
  have hQ_sq : Q rhoH ^ 2 = -L0.g₃ := by
    have h := Q_sq_eq rhoH
    have hP0 : P rhoH = 0 := by simp [P, E4_rhoH]
    rw [hP0] at h
    simpa using h
  have hw0_ex : ∃ w0 : ℂ, w0 ∉ L0.lattice ∧ ℘[L0] w0 = 0 ∧ ℘'[L0] w0 = Q rhoH := by
    have hsq : ℘'[L0] w1 ^ 2 = Q rhoH ^ 2 := by rw [derivWeierstrassP_w1_sq, hQ_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨w1, w1_notMem_L0, weierstrassP_w1, h⟩
    · refine ⟨-w1, fun hm => w1_notMem_L0 (by simpa using neg_mem hm), ?_, ?_⟩
      · rw [L0.weierstrassP_neg, weierstrassP_w1]
      · rw [L0.derivWeierstrassP_neg, h, neg_neg]
  obtain ⟨w0, hw0_not, hw0_P, hw0_Q⟩ := hw0_ex
  let g_int : ℂ → ℂ := fun z =>
    c0 * ModularForm.eta (psi z) ^ 4 * (I * (Real.sqrt 3 : ℝ) / (1 - z) ^ 2)
  have hg_diff : DifferentiableOn ℂ g_int (Metric.ball 0 1) := by
    intro z hz
    have hpsi : DifferentiableAt ℂ psi z := (hasDerivAt_psi hz).differentiableAt
    have heta : DifferentiableAt ℂ ModularForm.eta (psi z) :=
      ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (psi_im_pos hz)
    have hden : DifferentiableAt ℂ (fun w => I * (Real.sqrt 3 : ℝ) / (1 - w) ^ 2) z :=
      (differentiableAt_const _).div
        (((differentiableAt_const _).sub differentiableAt_id).pow 2)
        (pow_ne_zero 2 (one_sub_ne_zero_of_mem_ball hz))
    exact (((heta.comp z hpsi).pow 4).const_mul c0 |>.mul hden).differentiableWithinAt
  obtain ⟨G, hG0, hGderiv⟩ := hg_diff.isExactOn_ball.with_val_at 0 w0
  refine ⟨G, hGderiv, ?_⟩
  intro z₁ hz₁ hGz₁
  have hray_mem : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z₁ ∈ Metric.ball (0 : ℂ) 1 := by
    intro t ht
    rw [Metric.mem_ball, dist_zero_right] at hz₁ ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    calc t * ‖z₁‖ ≤ 1 * ‖z₁‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z₁)
      _ = ‖z₁‖ := one_mul _
      _ < 1 := hz₁
  have hG_ray_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => G ((s : ℂ) * z₁)) (z₁ * g_int ((t : ℂ) * z₁)) t := by
    intro t ht
    have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * z₁) z₁ t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z₁
    refine ((hGderiv _ (hray_mem t ht)).scomp t hlin).congr_deriv ?_
    simp [smul_eq_mul]
  have hG_ray_cont : ContinuousOn (fun s : ℝ => G ((s : ℂ) * z₁)) (Icc 0 1) :=
    fun t ht => (hG_ray_deriv t ht).continuousAt.continuousWithinAt
  let S : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | G ((t : ℂ) * z₁) ∈ L0.lattice}
  have hS_ne : S.Nonempty := ⟨1, ⟨by norm_num, le_rfl⟩, by simpa using hGz₁⟩
  have hS_bdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  have hS_closed : IsClosed S :=
    hG_ray_cont.preimage_isClosed_of_isClosed isClosed_Icc L0.isClosed_lattice
  let t₀ : ℝ := sInf S
  have ht₀_mem : t₀ ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
  have ht₀_pos : 0 < t₀ := by
    refine lt_of_le_of_ne ht₀_mem.1.1 ?_
    intro h0
    have h0' : (0 : ℝ) ∈ S := h0 ▸ ht₀_mem
    have : w0 ∈ L0.lattice := by simpa [S, hG0] using h0'.2
    exact hw0_not this
  have h_notMem_before : ∀ t ∈ Ico (0 : ℝ) t₀, G ((t : ℂ) * z₁) ∉ L0.lattice := by
    intro t ht hm
    have ht_S : t ∈ S := ⟨⟨ht.1, le_trans ht.2.le ht₀_mem.1.2⟩, hm⟩
    exact not_lt.mpr (csInf_le hS_bdd ht_S) ht.2
  have hofC_rho : UpperHalfPlane.ofComplex rhoC = rhoH := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos rhoC_im_pos]; rfl
  have hP_rho : P rhoH = 0 := by simp [P, E4_rhoH]
  have hP_eq_wp : ∀ t ∈ Ico (0 : ℝ) t₀,
      ℘[L0] (G ((t : ℂ) * z₁)) = P (UpperHalfPlane.ofComplex (psi ((t : ℂ) * z₁))) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst ht0
      simp only [Complex.ofReal_zero, zero_mul, hG0, hw0_P, psi_zero, hofC_rho, hP_rho]
    · let α : ℝ → ℂ × ℂ := fun u =>
        ((P ∘ UpperHalfPlane.ofComplex) (psi ((u : ℂ) * z₁)),
         (Q ∘ UpperHalfPlane.ofComplex) (psi ((u : ℂ) * z₁)))
      let β : ℝ → ℂ × ℂ := fun u =>
        (℘[L0] (G ((u : ℂ) * z₁)), ℘'[L0] (G ((u : ℂ) * z₁)))
      let m : ℝ → ℂ := fun u => z₁ * g_int ((u : ℂ) * z₁)
      let v : ℝ → ℂ × ℂ → ℂ × ℂ := fun u p => (m u * p.2, 6 * m u * p.1 ^ 2)
      have hα_deriv : ∀ u ∈ Icc (0 : ℝ) t, HasDerivAt α (v u (α u)) u := by
        intro u hu
        have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, le_trans hu.2 (le_trans ht.2.le ht₀_mem.1.2)⟩
        have hmem := hray_mem u hu1
        have him := psi_im_pos hmem
        let τu : ℍ := ⟨psi ((u : ℂ) * z₁), him⟩
        have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * z₁) z₁ u := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const z₁
        have hpsi_u : HasDerivAt (fun s : ℝ => psi ((s : ℂ) * z₁))
            (z₁ * (I * (Real.sqrt 3 : ℝ) / (1 - (u : ℂ) * z₁) ^ 2)) u := by
          refine ((hasDerivAt_psi hmem).scomp u hlin).congr_deriv ?_
          simp [smul_eq_mul]
        have hP_u : HasDerivAt (fun s : ℝ => (P ∘ UpperHalfPlane.ofComplex) (psi ((s : ℂ) * z₁)))
            (m u * (Q ∘ UpperHalfPlane.ofComplex) (psi ((u : ℂ) * z₁))) u := by
          refine ((hasDerivAt_P τu).scomp u hpsi_u).congr_deriv ?_
          simp only [smul_eq_mul, m, g_int, τu, Function.comp_apply,
            UpperHalfPlane.ofComplex_apply_of_im_pos him]
          ring
        have hQ_u : HasDerivAt (fun s : ℝ => (Q ∘ UpperHalfPlane.ofComplex) (psi ((s : ℂ) * z₁)))
            (6 * m u * (P ∘ UpperHalfPlane.ofComplex) (psi ((u : ℂ) * z₁)) ^ 2) u := by
          refine ((hasDerivAt_Q τu).scomp u hpsi_u).congr_deriv ?_
          simp only [smul_eq_mul, m, g_int, τu, Function.comp_apply,
            UpperHalfPlane.ofComplex_apply_of_im_pos him]
          ring
        exact hP_u.prodMk hQ_u
      have hβ_deriv : ∀ u ∈ Icc (0 : ℝ) t, HasDerivAt β (v u (β u)) u := by
        intro u hu
        have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, le_trans hu.2 (le_trans ht.2.le ht₀_mem.1.2)⟩
        have hnot : G ((u : ℂ) * z₁) ∉ L0.lattice :=
          h_notMem_before u ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩
        have hGu := hG_ray_deriv u hu1
        have hwp : HasDerivAt ℘[L0] (℘'[L0] (G ((u : ℂ) * z₁))) (G ((u : ℂ) * z₁)) := by
          have hd := (L0.differentiableOn_weierstrassP.differentiableAt
            (L0.isClosed_lattice.isOpen_compl.mem_nhds hnot)).hasDerivAt
          rwa [L0.deriv_weierstrassP] at hd
        have hwp' : HasDerivAt ℘'[L0] (6 * ℘[L0] (G ((u : ℂ) * z₁)) ^ 2) (G ((u : ℂ) * z₁)) := by
          have hd := (L0.differentiableOn_derivWeierstrassP.differentiableAt
            (L0.isClosed_lattice.isOpen_compl.mem_nhds hnot)).hasDerivAt
          rwa [deriv_derivWeierstrassP_eq _ hnot] at hd
        have h1 : HasDerivAt (fun s : ℝ => ℘[L0] (G ((s : ℂ) * z₁)))
            (m u * ℘'[L0] (G ((u : ℂ) * z₁))) u := by
          refine (hwp.scomp u hGu).congr_deriv ?_
          simp [m, smul_eq_mul]
        have h2 : HasDerivAt (fun s : ℝ => ℘'[L0] (G ((s : ℂ) * z₁)))
            (6 * m u * ℘[L0] (G ((u : ℂ) * z₁)) ^ 2) u := by
          refine (hwp'.scomp u hGu).congr_deriv ?_
          simp only [smul_eq_mul, m]
          ring
        exact h1.prodMk h2
      have hα_cont : ContinuousOn α (Icc 0 t) :=
        fun u hu => (hα_deriv u hu).continuousAt.continuousWithinAt
      have hβ_cont : ContinuousOn β (Icc 0 t) :=
        fun u hu => (hβ_deriv u hu).continuousAt.continuousWithinAt
      have hm_cont : ContinuousOn m (Icc 0 t) := by
        intro u hu
        have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, le_trans hu.2 (le_trans ht.2.le ht₀_mem.1.2)⟩
        have hlin : ContinuousAt (fun s : ℝ => (s : ℂ) * z₁) u :=
          Complex.continuous_ofReal.continuousAt.mul continuousAt_const
        have hgc : ContinuousAt g_int ((u : ℂ) * z₁) :=
          (hg_diff.differentiableAt (Metric.isOpen_ball.mem_nhds (hray_mem u hu1))).continuousAt
        have hcomp : ContinuousAt (fun s : ℝ => g_int ((s : ℂ) * z₁)) u :=
          ContinuousAt.comp (g := g_int) hgc hlin
        exact (continuousAt_const.mul hcomp).continuousWithinAt
      obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hm_cont.norm).bddAbove
      obtain ⟨R1, hR1⟩ := (isCompact_Icc.image_of_continuousOn hα_cont.norm).bddAbove
      obtain ⟨R2, hR2⟩ := (isCompact_Icc.image_of_continuousOn hβ_cont.norm).bddAbove
      let M' : ℝ := max M 0
      let R : ℝ := max (max R1 R2) 0
      have hM'_nn : 0 ≤ M' := le_max_right _ _
      have hR_nn : 0 ≤ R := le_max_right _ _
      let K : NNReal := ⟨M' * (1 + 12 * R), by positivity⟩
      have hlip : ∀ u ∈ Ico (0 : ℝ) t, LipschitzOnWith K (v u) (Metric.closedBall 0 R) := by
        intro u hu
        have hmu : ‖m u‖ ≤ M' :=
          le_trans (hM ⟨u, ⟨hu.1, hu.2.le⟩, rfl⟩) (le_max_left _ _)
        refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
        rw [Metric.mem_closedBall, dist_zero_right] at hp hq
        have hp1 : ‖p.1‖ ≤ R := le_trans (le_max_left _ _) hp
        have hq1 : ‖q.1‖ ≤ R := le_trans (le_max_left _ _) hq
        have hd1 : ‖p.1 - q.1‖ ≤ dist p q := by
          rw [Prod.dist_eq, Complex.dist_eq]; exact le_max_left _ _
        have hd2 : ‖p.2 - q.2‖ ≤ dist p q := by
          rw [Prod.dist_eq, Complex.dist_eq, Complex.dist_eq]; exact le_max_right _ _
        rw [Prod.dist_eq, Complex.dist_eq, Complex.dist_eq]
        refine max_le ?_ ?_
        · calc ‖m u * p.2 - m u * q.2‖
              = ‖m u‖ * ‖p.2 - q.2‖ := by rw [← mul_sub, norm_mul]
            _ ≤ M' * dist p q := mul_le_mul hmu hd2 (norm_nonneg _) hM'_nn
            _ ≤ (K : ℝ) * dist p q := by
                apply mul_le_mul_of_nonneg_right _ dist_nonneg
                change M' ≤ M' * (1 + 12 * R)
                nlinarith
        · calc ‖6 * m u * p.1 ^ 2 - 6 * m u * q.1 ^ 2‖
              = 6 * ‖m u‖ * ‖p.1 + q.1‖ * ‖p.1 - q.1‖ := by
                  rw [show 6 * m u * p.1 ^ 2 - 6 * m u * q.1 ^ 2 =
                    6 * m u * (p.1 + q.1) * (p.1 - q.1) by ring]
                  simp
            _ ≤ 6 * M' * (2 * R) * dist p q := by
                  have hsum : ‖p.1 + q.1‖ ≤ 2 * R := by
                    calc ‖p.1 + q.1‖ ≤ ‖p.1‖ + ‖q.1‖ := norm_add_le _ _
                      _ ≤ R + R := add_le_add hp1 hq1
                      _ = 2 * R := by ring
                  have h1 : 6 * ‖m u‖ ≤ 6 * M' := by linarith
                  have h2 : 6 * ‖m u‖ * ‖p.1 + q.1‖ ≤ 6 * M' * (2 * R) :=
                    mul_le_mul h1 hsum (norm_nonneg _) (by positivity)
                  exact mul_le_mul h2 hd1 (norm_nonneg _) (by positivity)
            _ ≤ (K : ℝ) * dist p q := by
                  apply mul_le_mul_of_nonneg_right _ dist_nonneg
                  change 6 * M' * (2 * R) ≤ M' * (1 + 12 * R)
                  nlinarith
      have h0_eq : α 0 = β 0 := by
        apply Prod.ext
        · simp only [α, β, Function.comp_apply, Complex.ofReal_zero, zero_mul, hG0, hw0_P,
            psi_zero, hofC_rho, hP_rho]
        · simp only [α, β, Function.comp_apply, Complex.ofReal_zero, zero_mul, hG0, hw0_Q,
            psi_zero, hofC_rho]
      have heq_on := ODE_solution_unique_of_mem_Icc_right (s := fun _ => Metric.closedBall 0 R)
        hlip hα_cont (fun u hu => (hα_deriv u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
        (fun u hu => by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact le_trans (hR1 ⟨u, ⟨hu.1, hu.2.le⟩, rfl⟩)
            (le_trans (le_max_left R1 R2) (le_max_left (max R1 R2) 0)))
        hβ_cont (fun u hu => (hβ_deriv u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
        (fun u hu => by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact le_trans (hR2 ⟨u, ⟨hu.1, hu.2.le⟩, rfl⟩)
            (le_trans (le_max_right R1 R2) (le_max_left (max R1 R2) 0)))
        h0_eq
      exact (congr_arg Prod.fst (heq_on ⟨ht.1, le_rfl⟩)).symm
  -- Pole contradiction at `t → t₀⁻`!
  let l₀ : ℂ := G ((t₀ : ℂ) * z₁)
  have hl₀ : l₀ ∈ L0.lattice := ht₀_mem.2
  have hG_tend : Tendsto (fun t : ℝ => G ((t : ℂ) * z₁)) (𝓝[<] t₀) (𝓝 l₀) :=
    ((hG_ray_deriv t₀ ht₀_mem.1).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hL_tend : Tendsto (fun t : ℝ => (G ((t : ℂ) * z₁) - l₀) ^ 2 * ℘[L0] (G ((t : ℂ) * z₁)))
      (𝓝[<] t₀) (𝓝 1) := by
    have hcont_ex : ContinuousAt (fun w => (w - l₀) ^ 2 * ℘[L0 - l₀] w + 1 - (w - l₀) ^ 2 / l₀ ^ 2) l₀ := by
      have h1 := (L0.analyticAt_weierstrassPExcept l₀).continuousAt
      have h2 : ContinuousAt (fun w : ℂ => (w - l₀) ^ 2) l₀ := by fun_prop
      have h3 : ContinuousAt (fun w : ℂ => (w - l₀) ^ 2 / l₀ ^ 2) l₀ := h2.div_const _
      exact ((h2.mul h1).add continuousAt_const).sub h3
    have hlim : Tendsto
        (fun t : ℝ => (G ((t : ℂ) * z₁) - l₀) ^ 2 * ℘[L0 - l₀] (G ((t : ℂ) * z₁)) + 1 -
          (G ((t : ℂ) * z₁) - l₀) ^ 2 / l₀ ^ 2) (𝓝[<] t₀) (𝓝 1) := by
      simpa [Function.comp_def] using hcont_ex.tendsto.comp hG_tend
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT ht₀_pos] with t ht
    have hne : G ((t : ℂ) * z₁) - l₀ ≠ 0 := by
      intro h0
      have heq : G ((t : ℂ) * z₁) = l₀ := sub_eq_zero.mp h0
      exact h_notMem_before t ⟨ht.1.le, ht.2⟩ (heq ▸ hl₀)
    have hadd := L0.weierstrassPExcept_add ⟨l₀, hl₀⟩ (G ((t : ℂ) * z₁))
    rw [← hadd]
    field_simp [hne]
    ring
  have hR_tend : Tendsto (fun t : ℝ => (G ((t : ℂ) * z₁) - l₀) ^ 2 * ℘[L0] (G ((t : ℂ) * z₁)))
      (𝓝[<] t₀) (𝓝 0) := by
    have hP_cont : ContinuousAt (fun t : ℝ => (P ∘ UpperHalfPlane.ofComplex) (psi ((t : ℂ) * z₁))) t₀ := by
      have hmem := hray_mem t₀ ht₀_mem.1
      have him := psi_im_pos hmem
      have hlin : ContinuousAt (fun s : ℝ => (s : ℂ) * z₁) t₀ :=
        Complex.continuous_ofReal.continuousAt.mul continuousAt_const
      have hpsi_c : ContinuousAt psi ((t₀ : ℂ) * z₁) := (hasDerivAt_psi hmem).continuousAt
      have hP_c : ContinuousAt (P ∘ UpperHalfPlane.ofComplex) (psi ((t₀ : ℂ) * z₁)) :=
        (hasDerivAt_P ⟨psi ((t₀ : ℂ) * z₁), him⟩).continuousAt
      have h1 : ContinuousAt (fun s : ℝ => psi ((s : ℂ) * z₁)) t₀ :=
        ContinuousAt.comp (g := psi) hpsi_c hlin
      exact ContinuousAt.comp (g := P ∘ UpperHalfPlane.ofComplex) hP_c h1
    have h0 : Tendsto (fun t : ℝ => (G ((t : ℂ) * z₁) - l₀) ^ 2 *
        (P ∘ UpperHalfPlane.ofComplex) (psi ((t : ℂ) * z₁))) (𝓝[<] t₀) (𝓝 0) := by
      have hsq : Tendsto (fun t : ℝ => (G ((t : ℂ) * z₁) - l₀) ^ 2) (𝓝[<] t₀) (𝓝 0) := by
        simpa using (hG_tend.sub (tendsto_const_nhds (x := l₀))).pow 2
      simpa using hsq.mul (hP_cont.tendsto.mono_left nhdsWithin_le_nhds)
    refine h0.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT ht₀_pos] with t ht
    rw [hP_eq_wp t ⟨ht.1.le, ht.2⟩]
    rfl
  exact one_ne_zero (tendsto_nhds_unique hL_tend hR_tend)

/- ### Part 6: Norm of `deriv G 0`, Gamma simplification, and `OMA.solution` -/

private lemma norm_deriv_G_zero_eq :
    ‖c0 * ModularForm.eta rhoC ^ 4 * (I * (Real.sqrt 3 : ℝ))‖ =
      Real.sqrt 3 * Real.sqrt e1 / ((2 : ℝ) ^ (1 / 3 : ℝ) * Real.pi) := by
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hrtA_pos : (0 : ℝ) < Real.sqrt A := Real.sqrt_pos.mpr A_pos
  have hrte1_pos : (0 : ℝ) < Real.sqrt e1 := Real.sqrt_pos.mpr e1_pos
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hL_nn : 0 ≤ ‖c0 * ModularForm.eta rhoC ^ 4 * (I * (Real.sqrt 3 : ℝ))‖ := norm_nonneg _
  have hR_nn : 0 ≤ Real.sqrt 3 * Real.sqrt e1 / ((2 : ℝ) ^ (1 / 3 : ℝ) * Real.pi) := by positivity
  refine (pow_left_inj₀ hL_nn hR_nn (by norm_num : 6 ≠ 0)).mp ?_
  have hnorm_c0 : ‖c0‖ = Real.pi / (3 * Real.sqrt A) := by
    dsimp [c0]
    rw [norm_div, norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Complex.norm_I, Complex.norm_ofNat, Real.norm_of_nonneg hpi_pos.le,
      Real.norm_of_nonneg hrtA_pos.le, mul_one]
  have hnorm_E6 : ‖ModularForm.E₆ rhoH‖ = 27 * e1 ^ 3 / (2 * Real.pi ^ 6) := by
    have h := L0_g3_eq
    rw [L0_g3_eq_four_e1_cube] at h
    have hn := congr_arg norm h
    simp only [norm_mul, norm_div, norm_pow, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg e1_pos.le, Real.norm_of_nonneg hpi_pos.le] at hn
    field_simp [hpi_pos.ne'] at hn ⊢
    linarith
  have hnorm_eta24 : ‖ModularForm.eta rhoC‖ ^ 24 = ‖ModularForm.E₆ rhoH‖ ^ 2 / 1728 := by
    have h := E6_rhoH_sq
    have hn := congr_arg norm h
    change ‖ModularForm.E₆ rhoH ^ 2‖ = ‖(-1728 : ℂ) * ModularForm.eta rhoC ^ 24‖ at hn
    simp only [norm_mul, norm_neg, norm_pow, Complex.norm_ofNat] at hn
    linarith
  have hL6 : ‖c0 * ModularForm.eta rhoC ^ 4 * (I * (Real.sqrt 3 : ℝ))‖ ^ 6 =
      (Real.pi / (3 * Real.sqrt A)) ^ 6 * ‖ModularForm.eta rhoC‖ ^ 24 * (Real.sqrt 3) ^ 6 := by
    simp only [norm_mul, norm_pow, hnorm_c0, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hrt3_pos.le]
    ring
  have hA_pow6 : (Real.sqrt A) ^ 6 = A ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt A_pos.le]
  have h3_pow6 : (Real.sqrt 3) ^ 6 = 27 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  have he1_pow6 : (Real.sqrt e1) ^ 6 = e1 ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt e1_pos.le]
  have h2_pow6 : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 6 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hL6, hnorm_eta24, hnorm_E6]
  conv_lhs => rw [div_pow, mul_pow, hA_pow6, h3_pow6]
  conv_rhs => rw [div_pow, mul_pow, mul_pow, h3_pow6, he1_pow6, h2_pow6]
  dsimp [A]
  field_simp [hpi_pos.ne', e1_pos.ne']
  ring

private lemma target_constant_eq :
    (1 / Real.sqrt 3) / (Real.sqrt 3 * Real.sqrt e1 / ((2 : ℝ) ^ (1 / 3 : ℝ) * Real.pi)) =
      Real.Gamma (1 / 3) * Real.Gamma (5 / 6) / Real.Gamma (1 / 6) := by
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hrtpi_pos : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi_pos
  have hrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hrte1_pos : (0 : ℝ) < Real.sqrt e1 := Real.sqrt_pos.mpr e1_pos
  have hG16_pos : 0 < Real.Gamma (1 / 6) := Real.Gamma_pos_of_pos (by norm_num)
  have hG23_pos : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hdup := Real.Gamma_mul_Gamma_add_half (1 / 3 : ℝ)
  norm_num at hdup
  have hbeta := three_mul_sqrt_e1_eq_gamma
  have hLHS :
      (1 / Real.sqrt 3) / (Real.sqrt 3 * Real.sqrt e1 / ((2 : ℝ) ^ (1 / 3 : ℝ) * Real.pi)) =
        (2 : ℝ) ^ (1 / 3 : ℝ) * Real.pi / (3 * Real.sqrt e1) := by
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    field_simp [hrt3_pos.ne', hrte1_pos.ne']
    nlinarith [hsq3]
  rw [hLHS, hbeta]
  have hsqpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi_pos.le
  field_simp [hG16_pos.ne', hG23_pos.ne', hrtpi_pos.ne']
  conv_rhs => rw [mul_assoc, hdup]
  conv_lhs => rw [← hsqpi]
  ring

end

end BlochLandauB

theorem OMA.solution : type_of% @Bloch.landauConstant_upper_bound := by
  unfold Bloch.landauConstant
  apply csSup_le
  · refine ⟨0, fun f _ _ => ⟨0, by simp⟩⟩
  · intro B hB
    obtain ⟨G, hGderiv, hGavoid⟩ := BlochLandauB.exists_extremal_map
    set d0 : ℂ := BlochLandauB.c0 * ModularForm.eta BlochLandauB.rhoC ^ 4 * (I * (Real.sqrt 3 : ℝ))
    have hdG0 : HasDerivAt G d0 0 := by
      simpa [BlochLandauB.psi_zero, d0] using hGderiv 0 (Metric.mem_ball_self one_pos)
    have hnorm_d0 : ‖d0‖ = Real.sqrt 3 * Real.sqrt BlochLandauB.e1 / ((2 : ℝ) ^ (1 / 3 : ℝ) * Real.pi) :=
      BlochLandauB.norm_deriv_G_zero_eq
    have hd0_pos : 0 < ‖d0‖ := by
      rw [hnorm_d0]
      have := BlochLandauB.e1_pos
      have := Real.pi_pos
      have : (0 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      positivity
    have hd0_ne : d0 ≠ 0 := norm_ne_zero_iff.mp hd0_pos.ne'
    let f : ℂ → ℂ := fun z => (G z - G 0) / d0
    have hf_diff : DifferentiableOn ℂ f (Metric.ball 0 1) :=
      fun z hz => (((hGderiv z hz).differentiableAt.sub_const _).div_const _).differentiableWithinAt
    have hf_deriv0 : deriv f 0 = 1 := by
      have hd : HasDerivAt f (d0 / d0) 0 := (hdG0.sub_const (G 0)).div_const d0
      rw [hd.deriv, div_self hd0_ne]
    obtain ⟨x, hx⟩ := hB f hf_diff hf_deriv0
    obtain ⟨l, hl_mem, hl_dist⟩ := BlochLandauB.exists_dist_le_L0 (x * d0 + G 0)
    let w : ℂ := (l - G 0) / d0
    have hw_not_mem : w ∉ f '' Metric.ball (0 : ℂ) 1 := by
      rintro ⟨z, hz, hfz⟩
      have hGz : G z = l := by
        dsimp [f, w] at hfz
        have := (div_left_inj' hd0_ne).mp hfz
        linear_combination this
      exact hGavoid z hz (hGz ▸ hl_mem)
    have hw_not_ball : w ∉ Metric.ball x B := fun hm => hw_not_mem (hx hm)
    rw [Metric.mem_ball, not_lt] at hw_not_ball
    have hdist_eq : dist w x = dist (x * d0 + G 0) l / ‖d0‖ := by
      rw [Complex.dist_eq, Complex.dist_eq, ← norm_div]
      have : w - x = -((x * d0 + G 0 - l) / d0) := by
        dsimp [w]
        field_simp [hd0_ne]
        ring
      rw [this, norm_neg]
    calc B ≤ dist w x := hw_not_ball
      _ = dist (x * d0 + G 0) l / ‖d0‖ := hdist_eq
      _ ≤ (1 / Real.sqrt 3) / ‖d0‖ := div_le_div_of_nonneg_right hl_dist hd0_pos.le
      _ = Real.Gamma (1 / 3) * Real.Gamma (5 / 6) / Real.Gamma (1 / 6) := by
        rw [hnorm_d0]
        exact BlochLandauB.target_constant_eq
