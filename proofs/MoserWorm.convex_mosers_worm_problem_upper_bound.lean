import FormalConjectures.Wikipedia.MoserWorm
import Mathlib

/-!
Proof of `MoserWorm.convex_mosers_worm_problem_upper_bound`:
There exists a convex measurable set `X ⊆ ℝ²` of Lebesgue area `0.270911861` that covers every
1-Lipschitz curve `f : [0, 1] → ℝ²` by a proper rigid motion (rotation + translation).

Following Panraksa and Wichiramala (2021), Wetzel's sector covers unit arcs
(Periodica Mathematica Hungarica 82, 2021, arXiv:1907.07351), a 30° circular sector of unit radius
(area π/12 ≈ 0.2618) already covers every unit arc. Scaling the 30° sector to radius
R = √(0.270911861 / (π/12)) ≈ 1.01725 gives exact area 0.270911861 and provides radius slack to
reduce arbitrary 1-Lipschitz curves directly to general-position simple polygonal arcs via finite
sampling, tiny perturbation, and 2-opt uncrossing.
-/

open EuclideanGeometry MeasureTheory Set Filter Finset Complex
open scoped Topology Pointwise ENNReal BigOperators Real

namespace MoserWormUpper

/- Section 1: Complex-plane equivalence, rotations, and the 30° circular sector -/

noncomputable def c2r : ℂ ≃ₗᵢ[ℝ] ℝ² where
  toFun z := WithLp.toLp 2 ![z.re, z.im]
  invFun p := ⟨p 0, p 1⟩
  left_inv z := by cases z; rfl
  right_inv p := by
    ext i
    fin_cases i <;> rfl
  map_add' z w := by
    ext i
    fin_cases i <;> simp
  map_smul' r z := by
    ext i
    fin_cases i <;> simp
  norm_map' z := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [Complex.norm_def, Complex.normSq_apply, sq]

lemma c2r_apply_zero (z : ℂ) : c2r z 0 = z.re := rfl
lemma c2r_apply_one (z : ℂ) : c2r z 1 = z.im := rfl

lemma c2r_measurePreserving : MeasurePreserving c2r volume volume :=
  c2r.measurePreserving

lemma c2r_symm_measurePreserving : MeasurePreserving c2r.symm volume volume :=
  c2r.symm.measurePreserving

noncomputable def rotC (θ : ℝ) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun z := Complex.exp (θ * I) * z
  invFun z := Complex.exp ((-θ) * I) * z
  left_inv z := by
    dsimp
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  right_inv z := by
    dsimp
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  map_add' z w := mul_add _ _ _
  map_smul' r z := by
    change Complex.exp (θ * I) * ((r : ℂ) * z) = (r : ℂ) * (Complex.exp (θ * I) * z)
    ring
  norm_map' z := by
    dsimp
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma rotC_apply (θ : ℝ) (z : ℂ) : rotC θ z = Complex.exp (θ * I) * z := rfl

lemma rotC_measurePreserving (θ : ℝ) : MeasurePreserving (rotC θ) volume volume :=
  (rotC θ).measurePreserving

noncomputable def rotR2 (θ : ℝ) : ℝ² ≃ₗᵢ[ℝ] ℝ² :=
  (c2r.symm.trans (rotC θ)).trans c2r

lemma rotR2_apply (θ : ℝ) (z : ℂ) : rotR2 θ (c2r z) = c2r (Complex.exp (θ * I) * z) := by
  simp [rotR2, rotC]

lemma rotR2_det (θ : ℝ) : (rotR2 θ).toLinearEquiv.det = 1 := by
  have hb0 : (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0 = c2r 1 := by
    ext i; fin_cases i <;> simp [EuclideanSpace.basisFun_apply, c2r]
  have hb1 : (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1 = c2r I := by
    ext i; fin_cases i <;> simp [EuclideanSpace.basisFun_apply, c2r]
  have he : Complex.exp (↑θ * I) = ⟨Real.cos θ, Real.sin θ⟩ := by
    apply Complex.ext
    · simp [Complex.exp_ofReal_mul_I_re]
    · simp [Complex.exp_ofReal_mul_I_im]
  have hmat : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (rotR2 θ).toLinearEquiv.toLinearMap =
      !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    fin_cases j
    · change ((rotR2 θ) ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 0)) i = _
      rw [hb0, rotR2_apply, mul_one, he]
      fin_cases i <;> simp [c2r]
    · change ((rotR2 θ) ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis 1)) i = _
      rw [hb1, rotR2_apply, he]
      fin_cases i <;> simp [c2r]
  have hdet : (rotR2 θ).toLinearEquiv.toLinearMap.det =
      (!![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]).det := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, hmat]
  have hval : (rotR2 θ).toLinearEquiv.toLinearMap.det = 1 := by
    rw [hdet, Matrix.det_fin_two_of]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  exact Units.ext (by simpa [LinearEquiv.coe_det] using hval)

noncomputable def targetArea : ℝ := 0.270911861

noncomputable def R0 : ℝ := Real.sqrt (targetArea / (Real.pi / 12))

lemma targetArea_pos : 0 < targetArea := by norm_num [targetArea]

lemma R0_sq : R0 ^ 2 = targetArea / (Real.pi / 12) := by
  apply Real.sq_sqrt
  have hpi : 0 < Real.pi := Real.pi_pos
  have ha : 0 < targetArea := targetArea_pos
  positivity

lemma R0_gt : (1.017 : ℝ) < R0 := by
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hsq : (1.017 : ℝ) ^ 2 < R0 ^ 2 := by
    rw [R0_sq]
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < Real.pi / 12)]
    unfold targetArea
    nlinarith
  have hR0 : 0 ≤ R0 := Real.sqrt_nonneg _
  nlinarith

lemma R0_nonneg : 0 ≤ R0 := Real.sqrt_nonneg _

noncomputable def tan15 : ℝ := 2 - Real.sqrt 3

lemma tan15_pos : 0 < tan15 := by
  unfold tan15
  have h : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

def sectorC (R : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ ≤ R ∧ |z.im| ≤ tan15 * z.re}

def sectorR2 (R : ℝ) : Set ℝ² := c2r '' sectorC R

lemma mem_sectorC_iff {R : ℝ} {z : ℂ} :
    z ∈ sectorC R ↔ ‖z‖ ≤ R ∧ |z.im| ≤ tan15 * z.re := Iff.rfl

lemma sectorC_re_nonneg {R : ℝ} {z : ℂ} (hz : z ∈ sectorC R) : 0 ≤ z.re := by
  have h1 : 0 ≤ tan15 * z.re := (abs_nonneg _).trans hz.2
  exact nonneg_of_mul_nonneg_right h1 tan15_pos

lemma sectorC_conj {R : ℝ} {z : ℂ} (hz : z ∈ sectorC R) : starRingEnd ℂ z ∈ sectorC R := by
  refine ⟨by simpa using hz.1, ?_⟩
  simpa using hz.2

lemma sectorC_convex (R : ℝ) : Convex ℝ (sectorC R) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by simp [Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * R + b * R := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
      _ = R := by rw [← add_mul, hab, one_mul]
  · simp only [add_im, smul_im, add_re, smul_re, smul_eq_mul]
    calc |a * x.im + b * y.im| ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
      _ = a * |x.im| + b * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (tan15 * x.re) + b * (tan15 * y.re) :=
          add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = tan15 * (a * x.re + b * y.re) := by ring

lemma sectorR2_convex (R : ℝ) : Convex ℝ (sectorR2 R) :=
  (sectorC_convex R).linear_image c2r.toLinearMap

lemma sectorC_isClosed (R : ℝ) : IsClosed (sectorC R) := by
  have h1 : IsClosed {z : ℂ | ‖z‖ ≤ R} := isClosed_le continuous_norm continuous_const
  have h2 : IsClosed {z : ℂ | |z.im| ≤ tan15 * z.re} :=
    isClosed_le (continuous_abs.comp Complex.continuous_im) (continuous_const.mul Complex.continuous_re)
  exact h1.inter h2

lemma sectorR2_measurable (R : ℝ) : MeasurableSet (sectorR2 R) := by
  have heq : sectorR2 R = c2r.symm ⁻¹' sectorC R := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hp
      exact ⟨c2r.symm p, hp, by simp⟩
  rw [heq]
  exact (sectorC_isClosed R).measurableSet.preimage c2r.symm.continuous.measurable

/- Exact volume of `sectorR2 R0` via 12 rotations tiling `closedBall 0 R0` -/

lemma tan_pi_div_twelve : Real.tan (Real.pi / 12) = tan15 := by
  have h1 : Real.tan (Real.pi / 6) = 1 / Real.sqrt 3 := by
    rw [Real.tan_pi_div_six]
  have h2 : Real.pi / 6 = 2 * (Real.pi / 12) := by ring
  have h3 := Real.tan_two_mul (x := Real.pi / 12)
  rw [← h2, h1] at h3
  set t := Real.tan (Real.pi / 12)
  have ht0 : 0 < t := Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by linarith [Real.pi_pos])
  have ht1 : t < 1 := by
    have : Real.tan (Real.pi / 12) < Real.tan (Real.pi / 4) :=
      Real.strictMonoOn_tan (by constructor <;> linarith [Real.pi_pos])
        (by constructor <;> linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    simpa [Real.tan_pi_div_four] using this
  have hden : 1 - t ^ 2 ≠ 0 := by nlinarith
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hmul : 1 - t ^ 2 = 2 * Real.sqrt 3 * t := by
    have h4 := h3
    field_simp at h4
    linarith
  have hquad : (t - (2 - Real.sqrt 3)) * (t + (2 + Real.sqrt 3)) = 0 := by
    nlinarith [hmul, hsq3]
  rcases mul_eq_zero.mp hquad with h | h
  · exact sub_eq_zero.mp h
  · exfalso; linarith

lemma tan_abs_eq {θ : ℝ} (hθ : |θ| < Real.pi / 2) : Real.tan |θ| = |Real.tan θ| := by
  rcases le_or_gt 0 θ with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (Real.tan_nonneg_of_nonneg_of_le_pi_div_two h (abs_lt.mp hθ).2.le)]
  · rw [abs_of_neg h, Real.tan_neg, abs_of_nonpos]
    have h1 : 0 ≤ Real.tan (-θ) :=
      Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith [(abs_lt.mp hθ).1])
    rw [Real.tan_neg] at h1
    linarith

lemma mem_sectorC_iff_arg {R : ℝ} {z : ℂ} (hz : z ≠ 0) :
    z ∈ sectorC R ↔ ‖z‖ ≤ R ∧ |Complex.arg z| ≤ Real.pi / 12 := by
  rw [mem_sectorC_iff]
  have hn_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn_ne : ‖z‖ ≠ 0 := hn_pos.ne'
  constructor
  · rintro ⟨hr, him⟩
    refine ⟨hr, ?_⟩
    have hre_nn : 0 ≤ z.re := sectorC_re_nonneg ⟨hr, him⟩
    have hre_pos : 0 < z.re := by
      by_contra h
      have hre0 : z.re = 0 := le_antisymm (not_lt.mp h) hre_nn
      have him0 : z.im = 0 := by
        rw [hre0, mul_zero] at him
        exact abs_nonpos_iff.mp him
      exact hz (Complex.ext hre0 him0)
    have harg_lt : |Complex.arg z| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_pos)
    have hcos_pos : 0 < Real.cos (Complex.arg z) :=
      Real.cos_pos_of_mem_Ioo (abs_lt.mp harg_lt)
    have htan_eq : |Real.tan (Complex.arg z)| = |z.im| / z.re := by
      rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hcos_pos,
        Complex.sin_arg, Complex.cos_arg hz, abs_div, abs_of_pos hn_pos,
        div_div_div_cancel_right₀ hn_ne]
    have htan_le : Real.tan |Complex.arg z| ≤ Real.tan (Real.pi / 12) := by
      rw [tan_pi_div_twelve, tan_abs_eq harg_lt, htan_eq, div_le_iff₀ hre_pos]
      exact him
    have hmem1 : |Complex.arg z| ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [abs_nonneg (Complex.arg z), Real.pi_pos], harg_lt⟩
    have hmem2 : Real.pi / 12 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact (Real.strictMonoOn_tan.le_iff_le hmem1 hmem2).mp htan_le
  · rintro ⟨hr, harg⟩
    refine ⟨hr, ?_⟩
    have harg_lt : |Complex.arg z| < Real.pi / 2 := lt_of_le_of_lt harg (by linarith [Real.pi_pos])
    have hcos_pos : 0 < Real.cos (Complex.arg z) := Real.cos_pos_of_mem_Ioo (abs_lt.mp harg_lt)
    have hre_pos : 0 < z.re := by
      have h := Complex.cos_arg hz
      have hre_eq : z.re = ‖z‖ * Real.cos (Complex.arg z) := by
        rw [h]; field_simp
      rw [hre_eq]; positivity
    have hmem1 : |Complex.arg z| ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [abs_nonneg (Complex.arg z), Real.pi_pos], harg_lt⟩
    have hmem2 : Real.pi / 12 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have htan_le : Real.tan |Complex.arg z| ≤ tan15 := by
      rw [← tan_pi_div_twelve]
      exact Real.strictMonoOn_tan.monotoneOn hmem1 hmem2 harg
    have htan_eq : Real.tan |Complex.arg z| = |z.im| / z.re := by
      rw [tan_abs_eq harg_lt, Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hcos_pos,
        Complex.sin_arg, Complex.cos_arg hz, abs_div, abs_of_pos hn_pos,
        div_div_div_cancel_right₀ hn_ne]
    rw [htan_eq, div_le_iff₀ hre_pos] at htan_le
    exact htan_le

lemma sectorC_arg_eq_pi_div_twelve_of_inter {i j : Fin 12} (hij : i ≠ j) {z : ℂ} (hz : z ≠ 0)
    (hi : z ∈ (rotC ((i : ℝ) * (Real.pi / 6))) '' sectorC R0)
    (hj : z ∈ (rotC ((j : ℝ) * (Real.pi / 6))) '' sectorC R0) :
    ∃ a ∈ ({1, -1} : Set ℝ),
      ((rotC (-((i : ℝ) * (Real.pi / 6))) z).im) = a * tan15 * (rotC (-((i : ℝ) * (Real.pi / 6))) z).re := by
  obtain ⟨wi, hwi, rfl⟩ := hi
  obtain ⟨wj, hwj, hzw⟩ := hj
  have hwi0 : wi ≠ 0 := by
    intro h; subst h; simp [rotC] at hz
  have hwj0 : wj ≠ 0 := by
    intro h; subst h
    have h0 : (rotC ((j : ℝ) * (Real.pi / 6))) 0 = 0 := map_zero _
    rw [h0] at hzw
    exact hz hzw.symm
  have hwi_arg : |Complex.arg wi| ≤ Real.pi / 12 := ((mem_sectorC_iff_arg hwi0).mp hwi).2
  have hwj_arg : |Complex.arg wj| ≤ Real.pi / 12 := ((mem_sectorC_iff_arg hwj0).mp hwj).2
  have hrot_back : rotC (-((i : ℝ) * (Real.pi / 6))) (rotC ((i : ℝ) * (Real.pi / 6)) wi) = wi := by
    simp [rotC, ← mul_assoc, ← Complex.exp_add]
  rw [hrot_back]
  -- Compare arguments using exp(I * (arg wi - arg wj + (i - j)*pi/6)) = 1
  have hnorm_eq : ‖wi‖ = ‖wj‖ := by
    have := congrArg norm hzw
    rw [(rotC _).norm_map, (rotC _).norm_map] at this
    exact this.symm
  have hexp_eq : Complex.exp (((Complex.arg wi - Complex.arg wj + ((i : ℝ) - j) * (Real.pi / 6)) : ℝ) * I) = 1 := by
    have h1 := Complex.norm_mul_exp_arg_mul_I wi
    have h2 := Complex.norm_mul_exp_arg_mul_I wj
    have h3 : (‖wi‖ : ℂ) * Complex.exp (((i : ℝ) * (Real.pi / 6) : ℝ) * I) * Complex.exp (Complex.arg wi * I) =
        (‖wi‖ : ℂ) * Complex.exp (((j : ℝ) * (Real.pi / 6) : ℝ) * I) * Complex.exp (Complex.arg wj * I) := by
      have h4 : rotC ((i : ℝ) * (Real.pi / 6)) wi = rotC ((j : ℝ) * (Real.pi / 6)) wj := hzw.symm
      simp only [rotC_apply] at h4
      calc (‖wi‖ : ℂ) * Complex.exp (((i : ℝ) * (Real.pi / 6) : ℝ) * I) * Complex.exp (Complex.arg wi * I)
          = Complex.exp (((i : ℝ) * (Real.pi / 6) : ℝ) * I) * ((‖wi‖ : ℂ) * Complex.exp (Complex.arg wi * I)) := by ring
        _ = Complex.exp (((i : ℝ) * (Real.pi / 6) : ℝ) * I) * wi := by rw [h1]
        _ = Complex.exp (((j : ℝ) * (Real.pi / 6) : ℝ) * I) * wj := h4
        _ = Complex.exp (((j : ℝ) * (Real.pi / 6) : ℝ) * I) * ((‖wj‖ : ℂ) * Complex.exp (Complex.arg wj * I)) := by rw [h2]
        _ = (‖wi‖ : ℂ) * Complex.exp (((j : ℝ) * (Real.pi / 6) : ℝ) * I) * Complex.exp (Complex.arg wj * I) := by
            rw [hnorm_eq]; ring
    have hn_c : (‖wi‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hwi0)
    have h5 : Complex.exp (((i : ℝ) * (Real.pi / 6) : ℝ) * I) * Complex.exp (Complex.arg wi * I) =
        Complex.exp (((j : ℝ) * (Real.pi / 6) : ℝ) * I) * Complex.exp (Complex.arg wj * I) := by
      apply mul_left_cancel₀ hn_c
      simpa [mul_assoc] using h3
    rw [← Complex.exp_add, ← Complex.exp_add] at h5
    have h6 := congrArg (· * Complex.exp (-(((j : ℝ) * (Real.pi / 6) : ℝ) * I + Complex.arg wj * I))) h5
    rw [← Complex.exp_add, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero] at h6
    convert h6 using 2
    push_cast; ring
  rw [Complex.exp_eq_one_iff] at hexp_eq
  obtain ⟨m, hm⟩ := hexp_eq
  have hreal : Complex.arg wi - Complex.arg wj + ((i : ℝ) - j) * (Real.pi / 6) = m * (2 * Real.pi) := by
    have := congrArg Complex.im hm
    simp at this
    linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have habs_diff : |Complex.arg wi - Complex.arg wj| ≤ Real.pi / 6 := by
    calc |Complex.arg wi - Complex.arg wj| ≤ |Complex.arg wi| + |Complex.arg wj| := abs_sub _ _
      _ ≤ Real.pi / 12 + Real.pi / 12 := add_le_add hwi_arg hwj_arg
      _ = Real.pi / 6 := by ring
  -- Since (i - j) - 12*m is a nonzero integer, |(i - j) - 12*m| >= 1, so |arg wi - arg wj| >= pi/6!
  have hint : ((i : ℤ) - (j : ℤ) - 12 * m) ≠ 0 := by
    intro h0
    have hdiv : (12 : ℤ) ∣ ((i : ℤ) - (j : ℤ)) := ⟨m, by linarith⟩
    have hi12 : (i : ℤ) < 12 := by exact_mod_cast i.isLt
    have hj12 : (j : ℤ) < 12 := by exact_mod_cast j.isLt
    have hi0 : (0 : ℤ) ≤ i := Int.natCast_nonneg _
    have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg _
    have hm0 : m = 0 := by omega
    have hij_eq : (i : ℤ) = j := by omega
    exact hij (Fin.ext (by omega))
  have habs_int : (1 : ℝ) ≤ |((i : ℝ) - j) - 12 * (m : ℝ)| := by
    have : (1 : ℤ) ≤ |(i : ℤ) - (j : ℤ) - 12 * m| := Int.one_le_abs hint
    have hcast : ((|(i : ℤ) - (j : ℤ) - 12 * m| : ℤ) : ℝ) = |((i : ℝ) - j) - 12 * (m : ℝ)| := by
      push_cast; rfl
    rw [← hcast]
    exact_mod_cast this
  have heq_diff : |Complex.arg wi - Complex.arg wj| = |((i : ℝ) - j) - 12 * (m : ℝ)| * (Real.pi / 6) := by
    have h1 : Complex.arg wi - Complex.arg wj = -((((i : ℝ) - j) - 12 * (m : ℝ)) * (Real.pi / 6)) := by
      linarith
    rw [h1, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 6)]
  have hdiff_ge : Real.pi / 6 ≤ |Complex.arg wi - Complex.arg wj| := by
    rw [heq_diff]
    nlinarith
  have hwi_eq : |Complex.arg wi| = Real.pi / 12 := by
    have htri : |Complex.arg wi - Complex.arg wj| ≤ |Complex.arg wi| + |Complex.arg wj| := abs_sub _ _
    linarith
  have harg_lt : |Complex.arg wi| < Real.pi / 2 := by rw [hwi_eq]; linarith
  have hre_pos : 0 < wi.re := by
    have hcos : 0 < Real.cos (Complex.arg wi) := Real.cos_pos_of_mem_Ioo (abs_lt.mp harg_lt)
    have hn : 0 < ‖wi‖ := norm_pos_iff.mpr hwi0
    have hre_eq : wi.re = ‖wi‖ * Real.cos (Complex.arg wi) := by
      rw [Complex.cos_arg hwi0]; field_simp
    rw [hre_eq]; positivity
  have hcos_pos : 0 < Real.cos (Complex.arg wi) := Real.cos_pos_of_mem_Ioo (abs_lt.mp harg_lt)
  have him_abs : |wi.im| = tan15 * wi.re := by
    have h1 : Real.tan |Complex.arg wi| = |wi.im| / wi.re := by
      rw [tan_abs_eq harg_lt, Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hcos_pos,
        Complex.sin_arg, Complex.cos_arg hwi0, abs_div, abs_of_pos (norm_pos_iff.mpr hwi0),
        div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr hwi0)]
    rw [hwi_eq, tan_pi_div_twelve] at h1
    rw [eq_div_iff hre_pos.ne'] at h1
    linarith
  rcases abs_cases wi.im with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact ⟨1, by simp, by linarith⟩
  · exact ⟨-1, by simp, by linarith⟩

lemma volume_line_zero (a : ℝ) :
    volume {z : ℂ | z.im = a * z.re} = 0 := by
  let S : Submodule ℝ ℂ :=
    { carrier := {z : ℂ | z.im = a * z.re}
      add_mem' := by
        intro x y hx hy
        change (x + y).im = a * (x + y).re
        simp only [add_im, add_re]; linarith [show x.im = a * x.re from hx, show y.im = a * y.re from hy]
      zero_mem' := by change (0 : ℂ).im = a * (0 : ℂ).re; simp
      smul_mem' := by
        intro r x hx
        change (r • x).im = a * (r • x).re
        simp only [smul_im, smul_re, smul_eq_mul]
        have hx' : x.im = a * x.re := hx
        rw [hx']; ring }
  have hne : S ≠ ⊤ := by
    intro htop
    have hI : I ∈ S := by rw [htop]; trivial
    have : (I : ℂ).im = a * (I : ℂ).re := hI
    simp at this
  exact Measure.addHaar_submodule volume S hne

lemma volume_sectorC_R0 : volume (sectorC R0) = ENNReal.ofReal targetArea := by
  let S (k : Fin 12) : Set ℂ := (rotC ((k : ℝ) * (Real.pi / 6))) '' sectorC R0
  have hmeas : ∀ k : Fin 12, MeasurableSet (S k) := fun k => by
    have heq : S k = (rotC (-((k : ℝ) * (Real.pi / 6)))) ⁻¹' sectorC R0 := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        change rotC (-((k : ℝ) * (Real.pi / 6))) (rotC ((k : ℝ) * (Real.pi / 6)) w) ∈ sectorC R0
        simpa [rotC, ← mul_assoc, ← Complex.exp_add] using hw
      · intro hz
        refine ⟨rotC (-((k : ℝ) * (Real.pi / 6))) z, hz, ?_⟩
        simp [rotC, ← mul_assoc, ← Complex.exp_add]
    rw [heq]
    exact (sectorC_isClosed R0).measurableSet.preimage (rotC _).continuous.measurable
  have hvol_eq : ∀ k : Fin 12, volume (S k) = volume (sectorC R0) := fun k => by
    have heq : S k = (rotC (-((k : ℝ) * (Real.pi / 6)))) ⁻¹' sectorC R0 := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa [rotC, ← mul_assoc, ← Complex.exp_add] using hw
      · intro hz
        refine ⟨rotC (-((k : ℝ) * (Real.pi / 6))) z, hz, ?_⟩
        simp [rotC, ← mul_assoc, ← Complex.exp_add]
    rw [heq]
    exact (rotC_measurePreserving _).measure_preimage (sectorC_isClosed R0).measurableSet.nullMeasurableSet
  have hunion : (⋃ k : Fin 12, S k) = Metric.closedBall (0 : ℂ) R0 := by
    ext z
    simp only [mem_iUnion, Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨k, w, hw, rfl⟩
      rw [(rotC _).norm_map]
      exact hw.1
    · intro hz
      by_cases hz0 : z = 0
      · subst hz0
        refine ⟨0, 0, ⟨by simpa using R0_nonneg, by simp⟩, by simp [rotC]⟩
      · set θ := Complex.arg z
        have hpi : 0 < Real.pi := Real.pi_pos
        set q : ℤ := ⌊(θ + Real.pi / 12) / (Real.pi / 6)⌋
        have hq_lo : (q : ℝ) ≤ (θ + Real.pi / 12) / (Real.pi / 6) := Int.floor_le _
        have hq_hi : (θ + Real.pi / 12) / (Real.pi / 6) < (q : ℝ) + 1 := Int.lt_floor_add_one _
        have hdiff_lo : -(Real.pi / 12) ≤ θ - (q : ℝ) * (Real.pi / 6) := by
          have := (le_div_iff₀ (by positivity : (0 : ℝ) < Real.pi / 6)).mp hq_lo
          linarith
        have hdiff_hi : θ - (q : ℝ) * (Real.pi / 6) ≤ Real.pi / 12 := by
          have := (div_lt_iff₀ (by positivity : (0 : ℝ) < Real.pi / 6)).mp hq_hi
          linarith
        have hmod_nn : 0 ≤ q % 12 := Int.emod_nonneg q (by norm_num)
        have hmod_lt : q % 12 < 12 := Int.emod_lt_of_pos q (by norm_num)
        let k : Fin 12 := ⟨(q % 12).toNat, by omega⟩
        let w := rotC (-((k : ℝ) * (Real.pi / 6))) z
        refine ⟨k, w, ?_, by simp [w, rotC, ← mul_assoc, ← Complex.exp_add]⟩
        have hw0 : w ≠ 0 := by
          intro h
          have := congrArg (rotC ((k : ℝ) * (Real.pi / 6))) h
          simp [w, rotC, ← mul_assoc, ← Complex.exp_add] at this
          exact hz0 this
        rw [mem_sectorC_iff_arg hw0]
        refine ⟨by dsimp [w]; rw [(rotC _).norm_map]; exact hz, ?_⟩
        -- Show Complex.arg w = θ - q * (pi/6)
        have hq_split : (q : ℝ) = (k : ℝ) + 12 * ((q / 12 : ℤ) : ℝ) := by
          have h1 : q = q % 12 + 12 * (q / 12) := by omega
          have hk : ((k : ℕ) : ℤ) = q % 12 := by
            change ((q % 12).toNat : ℤ) = q % 12
            exact Int.toNat_of_nonneg hmod_nn
          have h2 : (q : ℤ) = (k : ℕ) + 12 * (q / 12) := by omega
          exact_mod_cast h2
        have hw_polar : w = (‖z‖ : ℂ) * Complex.exp (((θ - (q : ℝ) * (Real.pi / 6)) : ℝ) * I) := by
          have hz_pol := (Complex.norm_mul_exp_arg_mul_I z).symm
          dsimp [w]
          rw [rotC_apply]
          conv_lhs => rw [hz_pol]
          have h1 : Complex.exp (((-((k : ℝ) * (Real.pi / 6))) : ℝ) * I) * ((‖z‖ : ℂ) * Complex.exp (θ * I)) =
              (‖z‖ : ℂ) * Complex.exp (((θ - (k : ℝ) * (Real.pi / 6)) : ℝ) * I) := by
            rw [mul_left_comm, ← Complex.exp_add]
            congr 2; push_cast; ring
          rw [h1]
          congr 1
          have hexp_per : Complex.exp ((((q / 12 : ℤ) : ℝ) * (2 * Real.pi) : ℝ) * I) = 1 := by
            rw [Complex.exp_eq_one_iff]
            exact ⟨q / 12, by push_cast; ring⟩
          calc Complex.exp (((θ - (k : ℝ) * (Real.pi / 6)) : ℝ) * I)
              = Complex.exp (((θ - (q : ℝ) * (Real.pi / 6)) : ℝ) * I) *
                  Complex.exp ((((q / 12 : ℤ) : ℝ) * (2 * Real.pi) : ℝ) * I) := by
                rw [← Complex.exp_add]
                congr 1
                rw [hq_split]
                push_cast; ring
            _ = Complex.exp (((θ - (q : ℝ) * (Real.pi / 6)) : ℝ) * I) := by rw [hexp_per, mul_one]
        have harg_w : Complex.arg w = θ - (q : ℝ) * (Real.pi / 6) := by
          rw [hw_polar, Complex.arg_real_mul _ (norm_pos_iff.mpr hz0),
            Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I ⟨by linarith, by linarith⟩]
        rw [harg_w, abs_le]
        exact ⟨hdiff_lo, hdiff_hi⟩
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume) S) := by
    intro i j hij
    change volume (S i ∩ S j) = 0
    have hsub : S i ∩ S j ⊆ (rotC (-((i : ℝ) * (Real.pi / 6)))) ⁻¹'
        ({z : ℂ | z.im = tan15 * z.re} ∪ {z : ℂ | z.im = (-tan15) * z.re}) := by
      intro z ⟨hi, hj⟩
      by_cases hz0 : z = 0
      · subst hz0
        left; simp [rotC]
      · obtain ⟨a, ha, heq⟩ := sectorC_arg_eq_pi_div_twelve_of_inter hij hz0 hi hj
        rcases ha with rfl | rfl
        · left; simpa using heq
        · right; simpa [neg_mul] using heq
    apply measure_mono_null hsub
    rw [(rotC_measurePreserving _).measure_preimage]
    · exact measure_union_null (volume_line_zero tan15) (volume_line_zero (-tan15))
    · exact ((isClosed_eq Complex.continuous_im (continuous_const.mul Complex.continuous_re)).measurableSet.union
        (isClosed_eq Complex.continuous_im (continuous_const.mul Complex.continuous_re)).measurableSet).nullMeasurableSet
  have hsum : volume (⋃ k : Fin 12, S k) = ∑ k : Fin 12, volume (S k) := by
    have hu : (⋃ k : Fin 12, S k) = ⋃ k ∈ (Finset.univ : Finset (Fin 12)), S k := by simp
    rw [hu]
    rw [measure_biUnion_finset₀ (fun i _ j _ hij => hdisj hij) (fun k _ => (hmeas k).nullMeasurableSet)]
  rw [hunion] at hsum
  simp only [hvol_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hball : volume (Metric.closedBall (0 : ℂ) R0) = ENNReal.ofReal (R0 ^ 2 * Real.pi) := by
    rw [Complex.volume_closedBall]
    rw [ENNReal.ofReal_mul (sq_nonneg R0), ENNReal.ofReal_pow R0_nonneg]
    congr 1
    rw [ENNReal.ofReal_eq_coe_nnreal Real.pi_pos.le]
    rfl
  rw [hball] at hsum
  have h12 : R0 ^ 2 * Real.pi = 12 * targetArea := by
    rw [R0_sq]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [h12, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12)] at hsum
  have h12_enn : ENNReal.ofReal 12 = (12 : ℝ≥0∞) := by norm_num
  rw [h12_enn] at hsum
  have hmul : ((12 : ℕ) : ℝ≥0∞) * ENNReal.ofReal targetArea = ((12 : ℕ) : ℝ≥0∞) * volume (sectorC R0) := by
    simpa using hsum
  exact ((ENNReal.mul_right_inj (by norm_num : ((12 : ℕ) : ℝ≥0∞) ≠ 0) (by norm_num)).mp hmul).symm

lemma volume_sectorR2_R0 : volume (sectorR2 R0) = 0.270911861 := by
  have heq : sectorR2 R0 = c2r.symm ⁻¹' sectorC R0 := by
    ext p
    exact ⟨fun ⟨x, hx, h⟩ => by simpa [← h] using hx, fun hp => ⟨c2r.symm p, hp, by simp⟩⟩
  rw [heq, c2r_symm_measurePreserving.measure_preimage (sectorC_isClosed R0).measurableSet.nullMeasurableSet,
    volume_sectorC_R0]
  unfold targetArea
  have h1 : (0.270911861 : ℝ) = ((0.270911861 : NNReal) : ℝ) := by norm_num
  rw [h1, ENNReal.ofReal_coe_nnreal]
  rfl

/- Section 2: Cross/dot products, general-position perturbation, and 2-opt simple polygonal reduction -/

def cross (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

def dotC (u v : ℂ) : ℝ := u.re * v.re + u.im * v.im

lemma cross_self (u : ℂ) : cross u u = 0 := by unfold cross; ring
lemma cross_antisymm (u v : ℂ) : cross u v = -cross v u := by unfold cross; ring
lemma cross_add_left (u v w : ℂ) : cross (u + v) w = cross u w + cross v w := by
  unfold cross; simp; ring
lemma cross_add_right (u v w : ℂ) : cross u (v + w) = cross u v + cross u w := by
  unfold cross; simp; ring
lemma cross_sub_left (u v w : ℂ) : cross (u - v) w = cross u w - cross v w := by
  unfold cross; simp; ring
lemma cross_sub_right (u v w : ℂ) : cross u (v - w) = cross u v - cross u w := by
  unfold cross; simp; ring
lemma cross_smul_left (r : ℝ) (u v : ℂ) : cross (r • u) v = r * cross u v := by
  unfold cross; simp; ring
lemma cross_smul_right (r : ℝ) (u v : ℂ) : cross u (r • v) = r * cross u v := by
  unfold cross; simp; ring
lemma cross_neg_left (u v : ℂ) : cross (-u) v = -cross u v := by unfold cross; simp; ring
lemma cross_neg_right (u v : ℂ) : cross u (-v) = -cross u v := by unfold cross; simp; ring
lemma cross_mul_unit (c u v : ℂ) : cross (c * u) (c * v) = Complex.normSq c * cross u v := by
  unfold cross; simp [Complex.normSq_apply]; ring
lemma cross_conj (u v : ℂ) : cross (starRingEnd ℂ u) (starRingEnd ℂ v) = -cross u v := by
  unfold cross; simp; ring

lemma dotC_add_left (u v w : ℂ) : dotC (u + v) w = dotC u w + dotC v w := by
  unfold dotC; simp; ring
lemma dotC_add_right (u v w : ℂ) : dotC u (v + w) = dotC u v + dotC u w := by
  unfold dotC; simp; ring
lemma dotC_sub_right (u v w : ℂ) : dotC u (v - w) = dotC u v - dotC u w := by
  unfold dotC; simp; ring
lemma dotC_comm (u v : ℂ) : dotC u v = dotC v u := by unfold dotC; ring
lemma dotC_self (u : ℂ) : dotC u u = ‖u‖ ^ 2 := by
  unfold dotC; rw [Complex.sq_norm, Complex.normSq_apply]
lemma dotC_sq_add_cross_sq (u v : ℂ) : dotC u v ^ 2 + cross u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  unfold dotC cross
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  ring

lemma norm_add_lt_of_cross_ne_zero {u v : ℂ} (h : cross u v ≠ 0) :
    ‖u + v‖ < ‖u‖ + ‖v‖ := by
  have hu : 0 ≤ ‖u‖ := norm_nonneg u
  have hv : 0 ≤ ‖v‖ := norm_nonneg v
  have hsq : ‖u + v‖ ^ 2 < (‖u‖ + ‖v‖) ^ 2 := by
    have h1 : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * dotC u v + ‖v‖ ^ 2 := by
      rw [← dotC_self, ← dotC_self, ← dotC_self, dotC_add_left, dotC_add_right, dotC_add_right,
        dotC_comm v u]
      ring
    have h2 : dotC u v < ‖u‖ * ‖v‖ := by
      have h3 : dotC u v ^ 2 < (‖u‖ * ‖v‖) ^ 2 := by
        have hc : 0 < cross u v ^ 2 := sq_pos_of_ne_zero h
        nlinarith [dotC_sq_add_cross_sq u v]
      nlinarith [mul_nonneg hu hv]
    linarith
  nlinarith [norm_nonneg (u + v)]

def GenPos {n : ℕ} (r : Fin n → ℂ) : Prop :=
  (∀ i j, i ≠ j → r i ≠ r j) ∧
  (∀ i j k, i ≠ j → j ≠ k → i ≠ k → cross (r j - r i) (r k - r i) ≠ 0)

lemma GenPos.comp_equiv {n : ℕ} {r : Fin n → ℂ} (hr : GenPos r) (σ : Equiv.Perm (Fin n)) :
    GenPos (r ∘ σ) :=
  ⟨fun i j hij => hr.1 _ _ (fun h => hij (σ.injective h)),
   fun i j k hij hjk hik => hr.2 _ _ _ (fun h => hij (σ.injective h))
     (fun h => hjk (σ.injective h)) (fun h => hik (σ.injective h))⟩

lemma GenPos.smul_pos {n : ℕ} {r : Fin n → ℂ} (hr : GenPos r) {c : ℝ} (hc : 0 < c) :
    GenPos (fun i => (c : ℂ) * r i) := by
  refine ⟨fun i j hij h => hr.1 i j hij (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne') h), ?_⟩
  intro i j k hij hjk hik
  have h1 : (c : ℂ) * r j - (c : ℂ) * r i = c • (r j - r i) := by simp [Complex.real_smul]; ring
  have h2 : (c : ℂ) * r k - (c : ℂ) * r i = c • (r k - r i) := by simp [Complex.real_smul]; ring
  rw [h1, h2, cross_smul_left, cross_smul_right]
  exact mul_ne_zero hc.ne' (mul_ne_zero hc.ne' (hr.2 i j k hij hjk hik))

lemma exists_genPos_approx {n : ℕ} (p : Fin n → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : Fin n → ℂ, GenPos q ∧ ∀ i, ‖q i - p i‖ < δ := by
  induction n with
  | zero => exact ⟨Fin.elim0, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, fun i => Fin.elim0 i⟩
  | succ m ih =>
    obtain ⟨q0, hq0, hdist0⟩ := ih (fun i : Fin m => p i.castSucc)
    let p_last := p (Fin.last m)
    let ε := min (δ / 4) (1 / 2)
    have hε : 0 < ε := lt_min (by linarith) (by norm_num)
    let γ (t : ℝ) : ℂ := p_last + (t : ℂ) + ((t ^ 2 : ℝ) : ℂ) * I
    have hγ_dist : ∀ t ∈ Ioo 0 ε, ‖γ t - p_last‖ < δ := by
      intro t ht
      have h1 : γ t - p_last = (t : ℂ) + ((t ^ 2 : ℝ) : ℂ) * I := by simp [γ]; ring
      rw [h1]
      have ht0 : 0 < t := ht.1
      have ht1 : t < δ / 4 := lt_of_lt_of_le ht.2 (min_le_left _ _)
      have ht2 : t < 1 / 2 := lt_of_lt_of_le ht.2 (min_le_right _ _)
      calc ‖(t : ℂ) + ((t ^ 2 : ℝ) : ℂ) * I‖ ≤ ‖(t : ℂ)‖ + ‖((t ^ 2 : ℝ) : ℂ) * I‖ := norm_add_le _ _
        _ = t + t ^ 2 := by
            rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
              Real.norm_of_nonneg ht0.le, Real.norm_of_nonneg (sq_nonneg t)]
        _ < δ := by nlinarith
    -- Finite set of bad t in R: either γ t = q0 i, or cross (q0 j - q0 i) (γ t - q0 i) = 0
    have hfin_pt : ∀ i : Fin m, ({t : ℝ | γ t = q0 i}).Finite := by
      intro i
      apply Set.Subsingleton.finite
      intro t1 ht1 t2 ht2
      have h1 := congrArg Complex.re ht1
      have h2 := congrArg Complex.re ht2
      simp only [γ, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, add_zero] at h1 h2
      linarith
    have hfin_line : ∀ i j : Fin m, i ≠ j → ({t : ℝ | cross (q0 j - q0 i) (γ t - q0 i) = 0}).Finite := by
      intro i j hij
      set a := q0 j - q0 i
      set b := p_last - q0 i
      have ha : a ≠ 0 := sub_ne_zero.mpr (hq0.1 j i hij.symm)
      have hcross_eq : ∀ t : ℝ, cross a (γ t - q0 i) =
          a.re * t ^ 2 - a.im * t + (a.re * b.im - a.im * b.re) := by
        intro t
        have hdiff : γ t - q0 i = b + (t : ℂ) + ((t ^ 2 : ℝ) : ℂ) * I := by simp [γ, b]; ring
        rw [hdiff]
        unfold cross
        simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
        ring
      let P : Polynomial ℝ :=
        Polynomial.C a.re * Polynomial.X ^ 2 - Polynomial.C a.im * Polynomial.X +
        Polynomial.C (a.re * b.im - a.im * b.re)
      have hP_eval : ∀ t : ℝ, P.eval t = cross a (γ t - q0 i) := by
        intro t
        rw [hcross_eq]
        simp [P]
      have hP_ne : P ≠ 0 := by
        intro h0
        have hc2 : P.coeff 2 = 0 := by rw [h0]; simp
        have hc1 : P.coeff 1 = 0 := by rw [h0]; simp
        simp only [P, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at hc2 hc1
        norm_num at hc2 hc1
        exact ha (Complex.ext hc2 hc1)
      have hsub : {t : ℝ | cross a (γ t - q0 i) = 0} ⊆ (P.roots.toFinset : Set ℝ) := by
        intro t ht
        simp only [Set.mem_ofPred_eq] at ht
        rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP_ne, Polynomial.IsRoot, hP_eval]
        exact ht
      exact (P.roots.toFinset.finite_toSet).subset hsub
    let badPts : Set ℝ := ⋃ i : Fin m, {t : ℝ | γ t = q0 i}
    let badLines : Set ℝ := ⋃ p : {x : Fin m × Fin m // x.1 ≠ x.2},
      {t : ℝ | cross (q0 p.1.2 - q0 p.1.1) (γ t - q0 p.1.1) = 0}
    have hbad_fin : (badPts ∪ badLines).Finite :=
      (Set.finite_iUnion hfin_pt).union (Set.finite_iUnion fun p => hfin_line p.1.1 p.1.2 p.2)
    have hinf : (Set.Ioo 0 ε).Infinite := Set.Ioo_infinite hε
    obtain ⟨t0, ht0_mem, ht0_good⟩ := (hinf.sdiff hbad_fin).nonempty
    let q : Fin (m + 1) → ℂ := Fin.snoc q0 (γ t0)
    have hnot_pt : ∀ i : Fin m, γ t0 ≠ q0 i := by
      intro i h
      exact ht0_good (Or.inl (Set.mem_iUnion.mpr ⟨i, h⟩))
    have hnot_line : ∀ i j : Fin m, i ≠ j → cross (q0 j - q0 i) (γ t0 - q0 i) ≠ 0 := by
      intro i j hij h
      exact ht0_good (Or.inr (Set.mem_iUnion.mpr ⟨⟨(i, j), hij⟩, h⟩))
    refine ⟨q, ⟨?_, ?_⟩, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;> intro hij
      · exact absurd rfl hij
      · simpa [q] using hnot_pt j'
      · simpa [q] using (hnot_pt i').symm
      · simpa [q] using hq0.1 i' j' (fun h => hij (congrArg Fin.castSucc h))
    · intro i j k
      refine Fin.lastCases ?_ (fun i' => ?_) i <;>
      refine Fin.lastCases ?_ (fun j' => ?_) j <;>
      refine Fin.lastCases ?_ (fun k' => ?_) k <;>
      intro hij hjk hik
      · exact absurd rfl hij
      · exact absurd rfl hij
      · exact absurd rfl hik
      · have hne : j' ≠ k' := fun h => hjk (congrArg Fin.castSucc h)
        simp only [q, Fin.snoc_last, Fin.snoc_castSucc]
        have hident : cross (q0 j' - γ t0) (q0 k' - γ t0) = cross (q0 k' - q0 j') (γ t0 - q0 j') := by
          unfold cross; simp; ring
        rw [hident]
        exact hnot_line j' k' hne
      · exact absurd rfl hjk
      · have hne : i' ≠ k' := fun h => hik (congrArg Fin.castSucc h)
        simp only [q, Fin.snoc_last, Fin.snoc_castSucc]
        have hident : cross (γ t0 - q0 i') (q0 k' - q0 i') = -cross (q0 k' - q0 i') (γ t0 - q0 i') :=
          cross_antisymm _ _
        rw [hident]
        exact neg_ne_zero.mpr (hnot_line i' k' hne)
      · have hne : i' ≠ j' := fun h => hij (congrArg Fin.castSucc h)
        simp only [q, Fin.snoc_last, Fin.snoc_castSucc]
        exact hnot_line i' j' hne
      · simp only [q, Fin.snoc_castSucc]
        exact hq0.2 i' j' k' (fun h => hij (congrArg Fin.castSucc h))
          (fun h => hjk (congrArg Fin.castSucc h)) (fun h => hik (congrArg Fin.castSucc h))
    · intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simpa [q, p_last] using hγ_dist t0 ht0_mem
      · simpa [q] using hdist0 i'

noncomputable def polyLen {N : ℕ} (r : Fin (N + 1) → ℂ) : ℝ :=
  ∑ k : Fin N, ‖r k.succ - r k.castSucc‖

def IsSimplePoly {N : ℕ} (r : Fin (N + 1) → ℂ) : Prop :=
  ∀ i j : Fin N, (i : ℕ) + 1 < (j : ℕ) →
    Disjoint (segment ℝ (r i.castSucc) (r i.succ)) (segment ℝ (r j.castSucc) (r j.succ))

lemma norm_add_eq_of_mem_segment {a b x : ℂ} (hx : x ∈ segment ℝ a b) :
    ‖x - a‖ + ‖b - x‖ = ‖b - a‖ := by
  rcases hx with ⟨s, t, hs, ht, hst, rfl⟩
  have h1 : s • a + t • b - a = t • (b - a) := by
    have hs' : s = 1 - t := by linarith
    rw [hs', sub_smul, one_smul, smul_sub]
    abel
  have h2 : b - (s • a + t • b) = s • (b - a) := by
    have ht' : t = 1 - s := by linarith
    rw [ht', sub_smul, one_smul, smul_sub]
    abel
  rw [h1, h2, norm_smul, norm_smul, Real.norm_of_nonneg ht, Real.norm_of_nonneg hs,
    ← add_mul, add_comm, hst, one_mul]

def revBlockFun (n a b : ℕ) (k : Fin n) : Fin n :=
  if h : a ≤ (k : ℕ) ∧ (k : ℕ) ≤ b ∧ b < n then
    ⟨a + b - (k : ℕ), by omega⟩
  else k

lemma revBlock_invol (n a b : ℕ) (k : Fin n) :
    revBlockFun n a b (revBlockFun n a b k) = k := by
  unfold revBlockFun
  by_cases h1 : a ≤ (k : ℕ) ∧ (k : ℕ) ≤ b ∧ b < n
  · rw [dif_pos h1]
    have h2 : a ≤ a + b - (k : ℕ) ∧ a + b - (k : ℕ) ≤ b ∧ b < n := by omega
    rw [dif_pos h2]
    ext; simp; omega
  · rw [dif_neg h1, dif_neg h1]

def revBlock (n a b : ℕ) : Equiv.Perm (Fin n) where
  toFun := revBlockFun n a b
  invFun := revBlockFun n a b
  left_inv := revBlock_invol n a b
  right_inv := revBlock_invol n a b

lemma two_opt_shortest {N : ℕ} (q : Fin (N + 1) → ℂ) (hq : GenPos q) :
    ∃ σ : Equiv.Perm (Fin (N + 1)),
      GenPos (q ∘ σ) ∧ polyLen (q ∘ σ) ≤ polyLen q ∧ IsSimplePoly (q ∘ σ) := by
  obtain ⟨σ, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun τ : Equiv.Perm (Fin (N + 1)) => polyLen (q ∘ τ))
    ⟨Equiv.refl _, Finset.mem_univ _⟩
  refine ⟨σ, hq.comp_equiv σ, hmin (Equiv.refl _) (Finset.mem_univ _), ?_⟩
  set r := q ∘ σ
  have hr : GenPos r := hq.comp_equiv σ
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  let a : ℕ := (i : ℕ) + 1
  let b : ℕ := (j : ℕ)
  have hab : a < b := hij
  have hb_lt : b < N + 1 := by omega
  let τ : Equiv.Perm (Fin (N + 1)) := (revBlock (N + 1) a b).trans σ
  have hle : polyLen r ≤ polyLen (q ∘ τ) := hmin τ (Finset.mem_univ τ)
  let perm := revBlock (N + 1) a b
  have hperm_apply : ∀ k : Fin (N + 1), (perm k : ℕ) = if a ≤ (k : ℕ) ∧ (k : ℕ) ≤ b then a + b - (k : ℕ) else (k : ℕ) := by
    intro k
    change (revBlockFun (N + 1) a b k : ℕ) = _
    unfold revBlockFun
    split_ifs <;> simp_all <;> omega
  let pairIdx (k : Fin N) : Fin N :=
    if h : a ≤ (k : ℕ) ∧ (k : ℕ) < b then ⟨a + b - 1 - (k : ℕ), by omega⟩ else k
  have hpair_invol : ∀ k : Fin N, pairIdx (pairIdx k) = k := by
    intro k
    dsimp only [pairIdx]
    by_cases h1 : a ≤ (k : ℕ) ∧ (k : ℕ) < b
    · rw [dif_pos h1]
      have h2 : a ≤ a + b - 1 - (k : ℕ) ∧ a + b - 1 - (k : ℕ) < b := by omega
      rw [dif_pos h2]
      ext; simp; omega
    · rw [dif_neg h1, dif_neg h1]
  let eN : Equiv.Perm (Fin N) := ⟨pairIdx, pairIdx, hpair_invol, hpair_invol⟩
  have hlen_other : ∀ k : Fin N, k ≠ i → k ≠ j →
      ‖r (perm (eN k).succ) - r (perm (eN k).castSucc)‖ = ‖r k.succ - r k.castSucc‖ := by
    intro k hki hkj
    have hki' : (k : ℕ) ≠ (i : ℕ) := fun h => hki (Fin.ext h)
    have hkj' : (k : ℕ) ≠ (j : ℕ) := fun h => hkj (Fin.ext h)
    by_cases hmid : a ≤ (k : ℕ) ∧ (k : ℕ) < b
    · have he : (eN k : ℕ) = a + b - 1 - (k : ℕ) := by simp [eN, pairIdx, hmid]
      have h1 : perm (eN k).succ = k.castSucc := by
        ext; rw [hperm_apply]; simp only [Fin.val_succ, Fin.val_castSucc, he]; split_ifs <;> omega
      have h2 : perm (eN k).castSucc = k.succ := by
        ext; rw [hperm_apply]; simp only [Fin.val_succ, Fin.val_castSucc, he]; split_ifs <;> omega
      rw [h1, h2, norm_sub_rev]
    · have he : eN k = k := by ext; simp [eN, pairIdx, hmid]
      rw [he]
      have h1 : perm k.succ = k.succ := by
        ext; rw [hperm_apply]; simp only [Fin.val_succ]; split_ifs <;> omega
      have h2 : perm k.castSucc = k.castSucc := by
        ext; rw [hperm_apply]; simp only [Fin.val_castSucc]; split_ifs <;> omega
      rw [h1, h2]
  have hperm_i_cast : perm i.castSucc = i.castSucc := by
    ext; rw [hperm_apply]; simp only [Fin.val_castSucc]; split_ifs <;> omega
  have hperm_i_succ : perm i.succ = j.castSucc := by
    ext; rw [hperm_apply]; simp only [Fin.val_succ, Fin.val_castSucc]; split_ifs <;> omega
  have hperm_j_cast : perm j.castSucc = i.succ := by
    ext; rw [hperm_apply]; simp only [Fin.val_succ, Fin.val_castSucc]; split_ifs <;> omega
  have hperm_j_succ : perm j.succ = j.succ := by
    ext; rw [hperm_apply]; simp only [Fin.val_succ]; split_ifs <;> omega
  have he_i : eN i = i := by ext; simp [eN, pairIdx]; split_ifs <;> omega
  have he_j : eN j = j := by ext; simp [eN, pairIdx]; split_ifs <;> omega
  have hlen_diff : polyLen (q ∘ τ) - polyLen r =
      (‖r j.castSucc - r i.castSucc‖ + ‖r j.succ - r i.succ‖) -
      (‖r i.succ - r i.castSucc‖ + ‖r j.succ - r j.castSucc‖) := by
    have hcomp : polyLen (q ∘ τ) = ∑ k : Fin N, ‖r (perm (eN k).succ) - r (perm (eN k).castSucc)‖ := by
      unfold polyLen
      rw [← Equiv.sum_comp eN]
      rfl
    rw [hcomp]
    unfold polyLen
    rw [← Finset.sum_sub_distrib]
    have hij_ne : i ≠ j := fun h => by rw [h] at hij; omega
    rw [Finset.sum_eq_add i j hij_ne]
    · rw [he_i, he_j, hperm_i_cast, hperm_i_succ, hperm_j_cast, hperm_j_succ]; ring
    · intro k _ hki
      rw [hlen_other k hki.1 hki.2, sub_self]
    · intro h; exact absurd (Finset.mem_univ i) h
    · intro h; exact absurd (Finset.mem_univ j) h
  -- Now prove strict inequality using x ∈ segment (r i) (r (i+1)) ∩ segment (r j) (r (j+1))
  have hseg1 := norm_add_eq_of_mem_segment hxi
  have hseg2 := norm_add_eq_of_mem_segment hxj
  have hne_cross : cross (x - r i.castSucc) (r j.castSucc - x) ≠ 0 := by
    rcases hxi with ⟨s1, t1, hs1, ht1, hst1, hx1⟩
    rcases hxj with ⟨s2, t2, hs2, ht2, hst2, hx2⟩
    have ht1_ne : t1 ≠ 0 := by
      intro ht0
      have hxi_eq : x = r i.castSucc := by
        rw [← hx1, ht0, show s1 = 1 by linarith]; simp
      have hc : cross (r j.succ - r j.castSucc) (r i.castSucc - r j.castSucc) = 0 := by
        rw [← hxi_eq, ← hx2]
        have hdiff : s2 • r j.castSucc + t2 • r j.succ - r j.castSucc = t2 • (r j.succ - r j.castSucc) := by
          rw [show s2 = 1 - t2 by linarith, sub_smul, one_smul, smul_sub]; abel
        rw [hdiff, cross_smul_right, cross_self, mul_zero]
      exact hr.2 j.castSucc j.succ i.castSucc (by intro h; simp [Fin.ext_iff] at h)
        (by intro h; simp [Fin.ext_iff] at h; omega) (by intro h; simp [Fin.ext_iff] at h; omega) hc
    have hdx1 : x - r i.castSucc = t1 • (r i.succ - r i.castSucc) := by
      rw [← hx1, show s1 = 1 - t1 by linarith, sub_smul, one_smul, smul_sub]; abel
    intro hzero
    rw [hdx1, cross_smul_left] at hzero
    have hzero1 : cross (r i.succ - r i.castSucc) (r j.castSucc - x) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left ht1_ne
    have hrewrite : r j.castSucc - x = (r j.castSucc - r i.castSucc) - (x - r i.castSucc) := by ring
    rw [hrewrite, cross_sub_right, hdx1, cross_smul_right, cross_self, mul_zero, sub_zero] at hzero1
    exact hr.2 i.castSucc i.succ j.castSucc (by intro h; simp [Fin.ext_iff] at h)
      (by intro h; simp [Fin.ext_iff] at h; omega) (by intro h; simp [Fin.ext_iff] at h; omega) hzero1
  have hlt1 : ‖r j.castSucc - r i.castSucc‖ < ‖x - r i.castSucc‖ + ‖r j.castSucc - x‖ := by
    have hsum : r j.castSucc - r i.castSucc = (x - r i.castSucc) + (r j.castSucc - x) := by ring
    rw [hsum]
    exact norm_add_lt_of_cross_ne_zero hne_cross
  have hle2 : ‖r j.succ - r i.succ‖ ≤ ‖r i.succ - x‖ + ‖r j.succ - x‖ := by
    have hsum : r j.succ - r i.succ = (x - r i.succ) + (r j.succ - x) := by ring
    rw [hsum]
    calc ‖(x - r i.succ) + (r j.succ - x)‖ ≤ ‖x - r i.succ‖ + ‖r j.succ - x‖ := norm_add_le _ _
      _ = ‖r i.succ - x‖ + ‖r j.succ - x‖ := by rw [norm_sub_rev]
  have hnorm_symm : ‖r j.castSucc - x‖ = ‖x - r j.castSucc‖ := norm_sub_rev _ _
  linarith

/- Shift and cover transfer from simple general-position unit-length polygons to arbitrary worms -/

lemma shift_ball_subset_sectorC_R0 {z w : ℂ} (hz : z ∈ sectorC 1.002) (hw : ‖w - z‖ ≤ 0.0011) :
    w + (0.006 : ℂ) ∈ sectorC R0 := by
  have hR0 : (1.017 : ℝ) < R0 := R0_gt
  have hsqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt3_lt : Real.sqrt 3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hsqrt3_gt : (1.732 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have htan15_gt : (0.2679 : ℝ) < tan15 := by unfold tan15; linarith
  have htan15_lt : tan15 < 0.268 := by unfold tan15; linarith
  have hre_diff : |w.re - z.re| ≤ 0.0011 := by
    calc |w.re - z.re| = |(w - z).re| := by simp
      _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
      _ ≤ 0.0011 := hw
  have him_diff : |w.im - z.im| ≤ 0.0011 := by
    calc |w.im - z.im| = |(w - z).im| := by simp
      _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      _ ≤ 0.0011 := hw
  rw [abs_le] at hre_diff him_diff
  refine ⟨?_, ?_⟩
  · calc ‖w + (0.006 : ℂ)‖ = ‖(w - z) + z + (0.006 : ℂ)‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z‖ + ‖(0.006 : ℂ)‖ := by
          calc ‖(w - z) + z + (0.006 : ℂ)‖ ≤ ‖(w - z) + z‖ + ‖(0.006 : ℂ)‖ := norm_add_le _ _
            _ ≤ ‖w - z‖ + ‖z‖ + ‖(0.006 : ℂ)‖ := by linarith [norm_add_le (w - z) z]
      _ ≤ 0.0011 + 1.002 + 0.006 := by
          have h006 : ‖(0.006 : ℂ)‖ = 0.006 := by
            rw [show (0.006 : ℂ) = ((0.006 : ℝ) : ℂ) by norm_num, Complex.norm_real]
            norm_num
          linarith [hz.1]
      _ ≤ R0 := by linarith
  · have hz_im := abs_le.mp hz.2
    simp only [add_im, add_re]
    have h006_re : ((0.006 : ℂ)).re = 0.006 := by norm_num
    have h006_im : ((0.006 : ℂ)).im = 0 := by norm_num
    rw [h006_re, h006_im, add_zero, abs_le]
    constructor <;> nlinarith

lemma worm_covered_of_simple_poly_cover
    (hpoly : ∀ (N : ℕ) (r : Fin (N + 1) → ℂ), 2 ≤ N → GenPos r → IsSimplePoly r → polyLen r ≤ 1 →
      ∃ (θ : ℝ) (v : ℂ) (refl : Bool), ∀ k,
        (if refl then starRingEnd ℂ (rotC θ (r k) + v) else rotC θ (r k) + v) ∈ sectorC 1) :
    sectorR2 R0 ∈ MoserWorm.WormCovers := by
  refine ⟨sectorR2_measurable R0, ?_⟩
  rintro w ⟨f, hf, rfl⟩
  let N : ℕ := 1000
  let tPt (k : Fin (N + 1)) : Set.Icc (0 : ℝ) 1 :=
    ⟨(k : ℝ) / (N : ℝ), div_nonneg (Nat.cast_nonneg _) (by positivity),
      div_le_one_of_le₀ (by exact_mod_cast Nat.le_of_lt_succ k.isLt) (by positivity)⟩
  let p (k : Fin (N + 1)) : ℂ := c2r.symm (f (tPt k))
  have hp_len : polyLen p ≤ 1 := by
    unfold polyLen
    have hterm : ∀ k : Fin N, ‖p k.succ - p k.castSucc‖ ≤ 1 / (N : ℝ) := by
      intro k
      have h1 : ‖p k.succ - p k.castSucc‖ = dist (f (tPt k.succ)) (f (tPt k.castSucc)) := by
        rw [← dist_eq_norm]
        exact c2r.symm.isometry.dist_eq _ _
      rw [h1]
      have h2 := hf.dist_le_mul (tPt k.succ) (tPt k.castSucc)
      simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq] at h2
      refine h2.trans ?_
      have hsub : ((k.succ : ℝ) / (N : ℝ)) - ((k.castSucc : ℝ) / (N : ℝ)) = 1 / (N : ℝ) := by
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
        ring
      rw [hsub, abs_of_pos (by positivity)]
    calc ∑ k : Fin N, ‖p k.succ - p k.castSucc‖ ≤ ∑ _k : Fin N, (1 / (N : ℝ)) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = 1 := by simp [N]
  obtain ⟨q, hq_gp, hq_dist⟩ := exists_genPos_approx p (δ := (1 : ℝ) / 10 ^ 6) (by norm_num)
  have hq_len : polyLen q ≤ 1.002 := by
    unfold polyLen
    have hterm : ∀ k : Fin N, ‖q k.succ - q k.castSucc‖ ≤ ‖p k.succ - p k.castSucc‖ + 2 / 10 ^ 6 := by
      intro k
      have hsplit : q k.succ - q k.castSucc =
          (q k.succ - p k.succ) + (p k.succ - p k.castSucc) + (p k.castSucc - q k.castSucc) := by ring
      rw [hsplit]
      have h1 := norm_add_le ((q k.succ - p k.succ) + (p k.succ - p k.castSucc)) (p k.castSucc - q k.castSucc)
      have h2 := norm_add_le (q k.succ - p k.succ) (p k.succ - p k.castSucc)
      have h3 := hq_dist k.succ
      have h4 := hq_dist k.castSucc
      rw [norm_sub_rev] at h1
      linarith
    calc ∑ k : Fin N, ‖q k.succ - q k.castSucc‖
        ≤ ∑ k : Fin N, (‖p k.succ - p k.castSucc‖ + 2 / 10 ^ 6) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = polyLen p + (N : ℝ) * (2 / 10 ^ 6) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; rfl
      _ ≤ 1 + 1000 * (2 / 10 ^ 6) := by norm_num [N]; linarith
      _ = 1.002 := by norm_num
  obtain ⟨σ, hσ_gp, hσ_len, hσ_simp⟩ := two_opt_shortest q hq_gp
  let c : ℝ := 1 / 1.002
  have hc_pos : 0 < c := by norm_num [c]
  let r (k : Fin (N + 1)) : ℂ := (c : ℂ) * (q (σ k))
  have hr_gp : GenPos r := hσ_gp.smul_pos hc_pos
  have hr_simp : IsSimplePoly r := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hmul_seg : ∀ (a b y : ℂ), y ∈ segment ℝ ((c : ℂ) * a) ((c : ℂ) * b) →
        ((c⁻¹ : ℝ) : ℂ) * y ∈ segment ℝ a b := by
      rintro a b y ⟨s, t, hs, ht, hst, rfl⟩
      refine ⟨s, t, hs, ht, hst, ?_⟩
      simp only [Complex.real_smul, mul_add]
      have hcc : ((c⁻¹ : ℝ) : ℂ) * (c : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ hc_pos.ne', Complex.ofReal_one]
      have h1 : ((c⁻¹ : ℝ) : ℂ) * ((s : ℂ) * ((c : ℂ) * a)) = (s : ℂ) * a := by
        calc _ = ((c⁻¹ : ℝ) : ℂ) * (c : ℂ) * ((s : ℂ) * a) := by ring
          _ = (s : ℂ) * a := by rw [hcc, one_mul]
      have h2 : ((c⁻¹ : ℝ) : ℂ) * ((t : ℂ) * ((c : ℂ) * b)) = (t : ℂ) * b := by
        calc _ = ((c⁻¹ : ℝ) : ℂ) * (c : ℂ) * ((t : ℂ) * b) := by ring
          _ = (t : ℂ) * b := by rw [hcc, one_mul]
      rw [h1, h2]
    exact Set.disjoint_left.mp (hσ_simp i j hij) (hmul_seg _ _ x hxi) (hmul_seg _ _ x hxj)
  have hr_len : polyLen r ≤ 1 := by
    unfold polyLen
    have h1 : ∀ k : Fin N, ‖r k.succ - r k.castSucc‖ = c * ‖q (σ k.succ) - q (σ k.castSucc)‖ := by
      intro k
      dsimp only [r]
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc_pos.le]
    simp_rw [h1, ← Finset.mul_sum]
    change c * polyLen (q ∘ σ) ≤ 1
    have hle : polyLen (q ∘ σ) ≤ 1.002 := hσ_len.trans hq_len
    dsimp [c]
    linarith
  obtain ⟨θ, v, refl, hcov⟩ := hpoly N r (by norm_num [N]) hr_gp hr_simp hr_len
  -- Since sectorC is conj-invariant, we can always remove `refl`!
  have hcov_rot : ∀ k : Fin (N + 1),
      rotC θ (q (σ k)) + (1.002 : ℂ) * v ∈ sectorC 1.002 := by
    intro k
    have hk := hcov k
    have hk' : rotC θ (r k) + v ∈ sectorC 1 := by
      cases refl
      · simpa using hk
      · simpa using sectorC_conj hk
    have hscale : rotC θ (q (σ k)) + (1.002 : ℂ) * v = (1.002 : ℝ) • (rotC θ (r k) + v) := by
      simp only [Complex.real_smul, rotC_apply, r, c]
      push_cast
      ring
    rw [hscale]
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      nlinarith [hk'.1]
    · simp only [Complex.real_smul, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, mul_re, sub_zero]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1.002)]
      nlinarith [hk'.2]
  -- Now cover the ENTIRE worm f([0, 1]) inside sectorC R0 via rotC θ and shift!
  let v_final : ℂ := (1.002 : ℂ) * v + (0.006 : ℂ)
  refine ⟨rotR2 (-θ), c2r (rotC (-θ) (-v_final)), rotR2_det (-θ), ?_⟩
  rintro _ ⟨t, rfl⟩
  have ht0 : 0 ≤ t.val := t.property.1
  have ht1 : t.val ≤ 1 := t.property.2
  have hNpos : (0 : ℝ) < (N : ℝ) := by norm_num [N]
  let kNat : ℕ := min N ⌊(N : ℝ) * t.val⌋₊
  have hk_lt : kNat < N + 1 := Nat.lt_succ_of_le (min_le_left _ _)
  let k : Fin (N + 1) := ⟨kNat, hk_lt⟩
  have ht_close : |t.val - (k : ℝ) / (N : ℝ)| ≤ 1 / (N : ℝ) := by
    by_cases htop : t.val = 1
    · have hkN : kNat = N := by
        dsimp [kNat]
        rw [htop, mul_one, Nat.floor_natCast, min_self]
      have hdiv : (k : ℝ) / (N : ℝ) = 1 := by
        change (kNat : ℝ) / (N : ℝ) = 1
        rw [hkN, div_self hNpos.ne']
      rw [htop, hdiv, sub_self, abs_zero]
      positivity
    · have ht_lt1 : t.val < 1 := lt_of_le_of_ne ht1 htop
      have hfl_lt : ⌊(N : ℝ) * t.val⌋₊ < N := by
        rw [Nat.floor_lt (mul_nonneg hNpos.le ht0)]
        nlinarith
      have hk_eq : kNat = ⌊(N : ℝ) * t.val⌋₊ := min_eq_right hfl_lt.le
      have hlo : (kNat : ℝ) ≤ t.val * (N : ℝ) := by
        rw [hk_eq, mul_comm]; exact Nat.floor_le (mul_nonneg ht0 hNpos.le)
      have hhi : t.val * (N : ℝ) < (kNat : ℝ) + 1 := by
        rw [hk_eq, mul_comm]; exact Nat.lt_floor_add_one _
      rw [abs_le]
      constructor
      · have : (k : ℝ) / (N : ℝ) ≤ t.val := (div_le_iff₀ hNpos).mpr (by simpa [k] using hlo)
        linarith [show (0 : ℝ) < 1 / (N : ℝ) by positivity]
      · have : t.val < ((k : ℝ) + 1) / (N : ℝ) := (lt_div_iff₀ hNpos).mpr (by simpa [k] using hhi)
        linarith [show ((k : ℝ) + 1) / (N : ℝ) = (k : ℝ) / (N : ℝ) + 1 / (N : ℝ) by ring]
  have hdist_fq : ‖c2r.symm (f t) - q k‖ ≤ 0.0011 := by
    have h1 : ‖c2r.symm (f t) - p k‖ ≤ 1 / (N : ℝ) := by
      have hd : ‖c2r.symm (f t) - p k‖ = dist (f t) (f (tPt k)) := by
        rw [← dist_eq_norm]; exact c2r.symm.isometry.dist_eq _ _
      rw [hd]
      have hlip := hf.dist_le_mul t (tPt k)
      simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq] at hlip
      exact hlip.trans ht_close
    have h2 : ‖p k - q k‖ < 1 / 10 ^ 6 := by rw [norm_sub_rev]; exact hq_dist k
    have hsplit : c2r.symm (f t) - q k = (c2r.symm (f t) - p k) + (p k - q k) := by ring
    rw [hsplit]
    have htri := norm_add_le (c2r.symm (f t) - p k) (p k - q k)
    norm_num [N] at h1
    linarith
  let z_w := rotC θ (c2r.symm (f t)) + v_final
  have hz_mem : z_w ∈ sectorC R0 := by
    let z_q := rotC θ (q k) + (1.002 : ℂ) * v
    have hzq : z_q ∈ sectorC 1.002 := by
      simpa [z_q] using hcov_rot (σ.symm k)
    have hdiff : ‖(rotC θ (c2r.symm (f t)) + (1.002 : ℂ) * v) - z_q‖ ≤ 0.0011 := by
      have heq : (rotC θ (c2r.symm (f t)) + (1.002 : ℂ) * v) - z_q =
          rotC θ (c2r.symm (f t) - q k) := by
        simp [z_q, map_sub]
      rw [heq, (rotC θ).norm_map]
      exact hdist_fq
    have hzw_eq : z_w = (rotC θ (c2r.symm (f t)) + (1.002 : ℂ) * v) + (0.006 : ℂ) := by
      simp [z_w, v_final]; ring
    rw [hzw_eq]
    exact shift_ball_subset_sectorC_R0 hzq hdiff
  refine ⟨c2r z_w, ⟨z_w, hz_mem, rfl⟩, ?_⟩
  dsimp only
  rw [rotR2_apply, ← map_add]
  have heq : Complex.exp ((-θ : ℝ) * I) * z_w + rotC (-θ) (-v_final) = c2r.symm (f t) := by
    simp [z_w, rotC, mul_add, ← mul_assoc, ← Complex.exp_add]
  rw [heq, LinearIsometryEquiv.apply_symm_apply]

/- Section 3: Complex winding number and the Alternating Boundary Chord Crossing Lemma -/

noncomputable def darg (z w : ℂ) : ℝ := Complex.arg (w / z)

lemma abs_arg_le_pi_div_two_of_re_nonneg {z : ℂ} (hz : z ≠ 0) (hre : 0 ≤ z.re) :
    |Complex.arg z| ≤ Real.pi / 2 := by
  have hcos : 0 ≤ Real.cos (Complex.arg z) := by
    rw [Complex.cos_arg hz]
    exact div_nonneg hre (norm_nonneg z)
  have hmem := Complex.arg_mem_Ioc z
  rw [abs_le]
  constructor
  · by_contra h
    push_neg at h
    have hneg : Real.cos (Complex.arg z) < 0 := by
      have h1 : Real.cos (-Complex.arg z) < 0 :=
        Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [hmem.1])
      rwa [Real.cos_neg] at h1
    linarith
  · by_contra h
    push_neg at h
    have hneg : Real.cos (Complex.arg z) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith [hmem.2, Real.pi_pos])
    linarith

lemma darg_eq_sub_arg {c z w : ℂ} (hc : c ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0)
    (hre1 : 0 ≤ (c * z).re) (hre2 : 0 ≤ (c * w).re) (hpos : 0 < (w / z).re) :
    darg z w = Complex.arg (c * w) - Complex.arg (c * z) := by
  have hcz : c * z ≠ 0 := mul_ne_zero hc hz
  have hcw : c * w ≠ 0 := mul_ne_zero hc hw
  have h1 : |Complex.arg (c * z)| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_of_re_nonneg hcz hre1
  have h2 : |Complex.arg (c * w)| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_of_re_nonneg hcw hre2
  have hdiff_le : |Complex.arg (c * w) - Complex.arg (c * z)| ≤ Real.pi := by
    calc |Complex.arg (c * w) - Complex.arg (c * z)|
        ≤ |Complex.arg (c * w)| + |Complex.arg (c * z)| := abs_sub _ _
      _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add h2 h1
      _ = Real.pi := by ring
  set θ := Complex.arg (c * w) - Complex.arg (c * z)
  have hratio : w / z = ((‖c * w‖ / ‖c * z‖ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I) := by
    have hp1 := (Complex.norm_mul_exp_arg_mul_I (c * z)).symm
    have hp2 := (Complex.norm_mul_exp_arg_mul_I (c * w)).symm
    have hcw_eq : w / z = (c * w) / (c * z) := by
      rw [mul_div_mul_left w z hc]
    rw [hcw_eq]
    conv_lhs => rw [hp2, hp1]
    have hne : (‖c * z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hcz)
    have hexp_ne : Complex.exp ((Complex.arg (c * z) : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
    rw [Complex.ofReal_div]
    have hsub : Complex.exp ((θ : ℂ) * I) =
        Complex.exp ((Complex.arg (c * w) : ℂ) * I) / Complex.exp ((Complex.arg (c * z) : ℂ) * I) := by
      rw [← Complex.exp_sub]
      congr 1; simp [θ]; ring
    rw [hsub]
    field_simp
  have hpos_r : 0 < ‖c * w‖ / ‖c * z‖ := div_pos (norm_pos_iff.mpr hcw) (norm_pos_iff.mpr hcz)
  have hcos_pos : 0 < Real.cos θ := by
    have hre : (w / z).re = (‖c * w‖ / ‖c * z‖) * Real.cos θ := by
      rw [hratio, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.exp_ofReal_mul_I_re]
    nlinarith
  have hθ_gt : -Real.pi < θ := by
    have hge : -Real.pi ≤ θ := (abs_le.mp hdiff_le).1
    rcases eq_or_lt_of_le hge with h | h
    · exfalso; rw [← h, Real.cos_neg, Real.cos_pi] at hcos_pos; linarith
    · exact h
  have hθ_le : θ ≤ Real.pi := (abs_le.mp hdiff_le).2
  unfold darg
  rw [hratio, Complex.arg_real_mul _ hpos_r, Complex.exp_mul_I,
    Complex.arg_cos_add_sin_mul_I ⟨hθ_gt, hθ_le⟩]

lemma re_div_pos_of_norm_sub_lt {z w : ℂ} (hz : z ≠ 0) (h : ‖w - z‖ < ‖z‖) :
    w ≠ 0 ∧ 0 < (w / z).re := by
  have hw : w ≠ 0 := by
    intro hw0; subst hw0; simp at h
  refine ⟨hw, ?_⟩
  have hsplit : w / z = 1 + (w - z) / z := by field_simp; ring
  rw [hsplit, add_re, one_re]
  have hbound : |((w - z) / z).re| ≤ ‖w - z‖ / ‖z‖ := by
    calc |((w - z) / z).re| ≤ ‖(w - z) / z‖ := Complex.abs_re_le_norm _
      _ = ‖w - z‖ / ‖z‖ := norm_div _ _
  have hlt1 : ‖w - z‖ / ‖z‖ < 1 := (div_lt_one (norm_pos_iff.mpr hz)).mpr h
  linarith [(abs_le.mp hbound).1]

lemma darg_antisymm {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) (hpos : 0 < (w / z).re) :
    darg z w + darg w z = 0 := by
  have hpos' : 0 < (z / w).re := by
    have hinv : z / w = (w / z)⁻¹ := by rw [inv_div]
    rw [hinv, Complex.inv_re]
    exact div_pos hpos (Complex.normSq_pos.mpr (div_ne_zero hw hz))
  have hc : z⁻¹ ≠ 0 := inv_ne_zero hz
  have h1 : (z⁻¹ * z).re = 1 := by rw [inv_mul_cancel₀ hz]; simp
  have h2 : (z⁻¹ * w).re = (w / z).re := by rw [div_eq_inv_mul]
  rw [darg_eq_sub_arg hc hz hw (by linarith) (by linarith) hpos,
      darg_eq_sub_arg hc hw hz (by linarith) (by linarith) hpos']
  ring

lemma darg_square_zero {z0 z1 z2 z3 : ℂ} {m : ℝ} (hm : 0 < m)
    (h0 : m ≤ ‖z0‖) (h1 : m ≤ ‖z1‖) (h2 : m ≤ ‖z2‖) (h3 : m ≤ ‖z3‖)
    (d01 : ‖z1 - z0‖ < m / 3) (d12 : ‖z2 - z1‖ < m / 3)
    (d23 : ‖z3 - z2‖ < m / 3) (d30 : ‖z0 - z3‖ < m / 3) :
    darg z0 z1 + darg z1 z2 + darg z2 z3 + darg z3 z0 = 0 := by
  have hz0 : z0 ≠ 0 := norm_pos_iff.mp (by linarith)
  have hz1 : z1 ≠ 0 := norm_pos_iff.mp (by linarith)
  have hz2 : z2 ≠ 0 := norm_pos_iff.mp (by linarith)
  have hz3 : z3 ≠ 0 := norm_pos_iff.mp (by linarith)
  have hc : z0⁻¹ ≠ 0 := inv_ne_zero hz0
  have hdist2 : ‖z2 - z0‖ < ‖z0‖ := by
    have : z2 - z0 = (z2 - z1) + (z1 - z0) := by ring
    rw [this]; linarith [norm_add_le (z2 - z1) (z1 - z0)]
  have hdist3 : ‖z3 - z0‖ < ‖z0‖ := by rw [norm_sub_rev]; linarith
  have hr0 : 0 ≤ (z0⁻¹ * z0).re := by rw [inv_mul_cancel₀ hz0]; simp
  have hr1 : 0 ≤ (z0⁻¹ * z1).re := by
    rw [← div_eq_inv_mul]; exact (re_div_pos_of_norm_sub_lt hz0 (by linarith)).2.le
  have hr2 : 0 ≤ (z0⁻¹ * z2).re := by
    rw [← div_eq_inv_mul]; exact (re_div_pos_of_norm_sub_lt hz0 hdist2).2.le
  have hr3 : 0 ≤ (z0⁻¹ * z3).re := by
    rw [← div_eq_inv_mul]; exact (re_div_pos_of_norm_sub_lt hz0 hdist3).2.le
  have hp01 : 0 < (z1 / z0).re := (re_div_pos_of_norm_sub_lt hz0 (by linarith : ‖z1 - z0‖ < ‖z0‖)).2
  have hp12 : 0 < (z2 / z1).re := (re_div_pos_of_norm_sub_lt hz1 (by linarith : ‖z2 - z1‖ < ‖z1‖)).2
  have hp23 : 0 < (z3 / z2).re := (re_div_pos_of_norm_sub_lt hz2 (by linarith : ‖z3 - z2‖ < ‖z2‖)).2
  have hp30 : 0 < (z0 / z3).re := (re_div_pos_of_norm_sub_lt hz3 (by linarith : ‖z0 - z3‖ < ‖z3‖)).2
  rw [darg_eq_sub_arg hc hz0 hz1 hr0 hr1 hp01,
      darg_eq_sub_arg hc hz1 hz2 hr1 hr2 hp12,
      darg_eq_sub_arg hc hz2 hz3 hr2 hr3 hp23,
      darg_eq_sub_arg hc hz3 hz0 hr3 hr0 hp30]
  ring

lemma grid_boundary_winding_zero (F : ℝ × ℝ → ℂ)
    (hcont : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hne : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, F p ≠ 0) :
    ∃ M : ℕ, 1 ≤ M ∧
      (∀ i j : ℕ, i < M → j ≤ M →
        0 < (F (((i + 1 : ℕ) : ℝ) / M, (j : ℝ) / M) / F ((i : ℝ) / M, (j : ℝ) / M)).re) ∧
      (∀ i j : ℕ, i ≤ M → j < M →
        0 < (F ((i : ℝ) / M, ((j + 1 : ℕ) : ℝ) / M) / F ((i : ℝ) / M, (j : ℝ) / M)).re) ∧
      (∑ i ∈ Finset.range M, darg (F ((i : ℝ) / M, 0)) (F (((i + 1 : ℕ) : ℝ) / M, 0))) +
      (∑ j ∈ Finset.range M, darg (F (1, (j : ℝ) / M)) (F (1, ((j + 1 : ℕ) : ℝ) / M))) +
      (∑ i ∈ Finset.range M, darg (F (((i + 1 : ℕ) : ℝ) / M, 1)) (F ((i : ℝ) / M, 1))) +
      (∑ j ∈ Finset.range M, darg (F (0, ((j + 1 : ℕ) : ℝ) / M)) (F (0, (j : ℝ) / M))) = 0 := by
  let Q : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hQ_comp : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hQ_ne : Q.Nonempty := ⟨(0, 0), ⟨left_mem_Icc.mpr zero_le_one, left_mem_Icc.mpr zero_le_one⟩⟩
  obtain ⟨pmin, hpmin_mem, hpmin⟩ := hQ_comp.exists_isMinOn hQ_ne hcont.norm
  set m := ‖F pmin‖
  have hm_pos : 0 < m := norm_pos_iff.mpr (hne pmin hpmin_mem)
  have hnorm_ge : ∀ p ∈ Q, m ≤ ‖F p‖ := fun p hp => hpmin hp
  have hunif : UniformContinuousOn F Q := hQ_comp.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨δ, hδ_pos, hδ⟩ := hunif (m / 3) (by positivity)
  obtain ⟨M0, hM0⟩ := exists_nat_gt (1 / δ)
  let M : ℕ := max 1 M0
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have hinv_lt : (1 : ℝ) / (M : ℝ) < δ := by
    have hlt : 1 / δ < (M : ℝ) := lt_of_lt_of_le hM0 (by exact_mod_cast le_max_right 1 M0)
    rw [div_lt_iff₀ hM_pos]
    have := (div_lt_iff₀ hδ_pos).mp hlt
    linarith
  let g (i j : ℕ) : ℂ := F ((i : ℝ) / (M : ℝ), (j : ℝ) / (M : ℝ))
  have hg_mem : ∀ i j : ℕ, i ≤ M → j ≤ M → ((i : ℝ) / M, (j : ℝ) / M) ∈ Q := by
    intro i j hi hj
    refine ⟨⟨div_nonneg (Nat.cast_nonneg _) hM_pos.le,
        div_le_one_of_le₀ (by exact_mod_cast hi) hM_pos.le⟩,
      ⟨div_nonneg (Nat.cast_nonneg _) hM_pos.le,
        div_le_one_of_le₀ (by exact_mod_cast hj) hM_pos.le⟩⟩
  have hstep_h : ∀ i j : ℕ, i < M → j ≤ M → ‖g (i + 1) j - g i j‖ < m / 3 := by
    intro i j hi hj
    rw [← dist_eq_norm]
    apply hδ _ (hg_mem (i + 1) j hi hj) _ (hg_mem i j hi.le hj)
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero]
    have hdiff : ((i + 1 : ℕ) : ℝ) / M - (i : ℝ) / M = 1 / M := by push_cast; ring
    rw [hdiff, abs_of_pos (by positivity), max_eq_left (by positivity)]
    exact hinv_lt
  have hstep_v : ∀ i j : ℕ, i ≤ M → j < M → ‖g i (j + 1) - g i j‖ < m / 3 := by
    intro i j hi hj
    rw [← dist_eq_norm]
    apply hδ _ (hg_mem i (j + 1) hi hj) _ (hg_mem i j hi hj.le)
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero]
    have hdiff : ((j + 1 : ℕ) : ℝ) / M - (j : ℝ) / M = 1 / M := by push_cast; ring
    rw [hdiff, abs_of_pos (by positivity), max_eq_right (by positivity)]
    exact hinv_lt
  have hre_h : ∀ i j : ℕ, i < M → j ≤ M → 0 < (g (i + 1) j / g i j).re := by
    intro i j hi hj
    have hnz : g i j ≠ 0 := hne _ (hg_mem i j hi.le hj)
    have hge : m ≤ ‖g i j‖ := hnorm_ge _ (hg_mem i j hi.le hj)
    exact (re_div_pos_of_norm_sub_lt hnz (by linarith [hstep_h i j hi hj])).2
  have hre_v : ∀ i j : ℕ, i ≤ M → j < M → 0 < (g i (j + 1) / g i j).re := by
    intro i j hi hj
    have hnz : g i j ≠ 0 := hne _ (hg_mem i j hi hj.le)
    have hge : m ≤ ‖g i j‖ := hnorm_ge _ (hg_mem i j hi hj.le)
    exact (re_div_pos_of_norm_sub_lt hnz (by linarith [hstep_v i j hi hj])).2
  -- Each cell sum is 0
  have hcell : ∀ i ∈ Finset.range M, ∀ j ∈ Finset.range M,
      (darg (g i j) (g (i + 1) j) + darg (g (i + 1) (j + 1)) (g i (j + 1))) +
      (darg (g (i + 1) j) (g (i + 1) (j + 1)) + darg (g i (j + 1)) (g i j)) = 0 := by
    intro i hi j hj
    rw [Finset.mem_range] at hi hj
    have hsq := darg_square_zero hm_pos
      (hnorm_ge _ (hg_mem i j hi.le hj.le))
      (hnorm_ge _ (hg_mem (i + 1) j hi hj.le))
      (hnorm_ge _ (hg_mem (i + 1) (j + 1) hi hj))
      (hnorm_ge _ (hg_mem i (j + 1) hi.le hj))
      (hstep_h i j hi hj.le)
      (hstep_v (i + 1) j hi hj)
      (by rw [norm_sub_rev]; exact hstep_h i (j + 1) hi hj)
      (by rw [norm_sub_rev]; exact hstep_v i j hi.le hj)
    linarith
  have htotal :
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        ((darg (g i j) (g (i + 1) j) + darg (g (i + 1) (j + 1)) (g i (j + 1))) +
         (darg (g (i + 1) j) (g (i + 1) (j + 1)) + darg (g i (j + 1)) (g i j))) = 0 := by
    exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => hcell i hi j hj
  -- Telescope horizontal and vertical sums!
  have hhor : ∀ i ∈ Finset.range M,
      ∑ j ∈ Finset.range M, (darg (g i j) (g (i + 1) j) + darg (g (i + 1) (j + 1)) (g i (j + 1))) =
      darg (g i 0) (g (i + 1) 0) + darg (g (i + 1) M) (g i M) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hneg : ∀ j ∈ Finset.range M,
        darg (g i j) (g (i + 1) j) + darg (g (i + 1) (j + 1)) (g i (j + 1)) =
        darg (g i j) (g (i + 1) j) - darg (g i (j + 1)) (g (i + 1) (j + 1)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have ha := darg_antisymm (hne _ (hg_mem i (j + 1) hi.le hj))
        (hne _ (hg_mem (i + 1) (j + 1) hi hj)) (hre_h i (j + 1) hi hj)
      linarith
    rw [Finset.sum_congr rfl hneg, Finset.sum_range_sub' (fun j => darg (g i j) (g (i + 1) j)) M]
    have haM := darg_antisymm (hne _ (hg_mem i M hi.le le_rfl))
      (hne _ (hg_mem (i + 1) M hi le_rfl)) (hre_h i M hi le_rfl)
    change darg (g i M) (g (i + 1) M) + darg (g (i + 1) M) (g i M) = 0 at haM
    linarith
  have hvert : ∀ j ∈ Finset.range M,
      ∑ i ∈ Finset.range M, (darg (g (i + 1) j) (g (i + 1) (j + 1)) + darg (g i (j + 1)) (g i j)) =
      darg (g M j) (g M (j + 1)) + darg (g 0 (j + 1)) (g 0 j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hneg : ∀ i ∈ Finset.range M,
        darg (g (i + 1) j) (g (i + 1) (j + 1)) + darg (g i (j + 1)) (g i j) =
        darg (g (i + 1) j) (g (i + 1) (j + 1)) - darg (g i j) (g i (j + 1)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have ha := darg_antisymm (hne _ (hg_mem i j hi.le hj.le))
        (hne _ (hg_mem i (j + 1) hi.le hj)) (hre_v i j hi.le hj)
      linarith
    rw [Finset.sum_congr rfl hneg, Finset.sum_range_sub (fun i => darg (g i j) (g i (j + 1))) M]
    have ha0 := darg_antisymm (hne _ (hg_mem 0 j (Nat.zero_le _) hj.le))
      (hne _ (hg_mem 0 (j + 1) (Nat.zero_le _) hj)) (hre_v 0 j (Nat.zero_le _) hj)
    change darg (g 0 j) (g 0 (j + 1)) + darg (g 0 (j + 1)) (g 0 j) = 0 at ha0
    linarith
  have hsplit :
      (∑ i ∈ Finset.range M, (darg (g i 0) (g (i + 1) 0) + darg (g (i + 1) M) (g i M))) +
      (∑ j ∈ Finset.range M, (darg (g M j) (g M (j + 1)) + darg (g 0 (j + 1)) (g 0 j))) = 0 := by
    have h1 : ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        ((darg (g i j) (g (i + 1) j) + darg (g (i + 1) (j + 1)) (g i (j + 1))) +
         (darg (g (i + 1) j) (g (i + 1) (j + 1)) + darg (g i (j + 1)) (g i j))) =
      (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        (darg (g i j) (g (i + 1) j) + darg (g (i + 1) (j + 1)) (g i (j + 1)))) +
      (∑ j ∈ Finset.range M, ∑ i ∈ Finset.range M,
        (darg (g (i + 1) j) (g (i + 1) (j + 1)) + darg (g i (j + 1)) (g i j))) := by
      have h2 : ∀ i, ∑ j ∈ Finset.range M,
          ((darg (g i j) (g (i + 1) j) + darg (g (i + 1) (j + 1)) (g i (j + 1))) +
           (darg (g (i + 1) j) (g (i + 1) (j + 1)) + darg (g i (j + 1)) (g i j))) =
        (∑ j ∈ Finset.range M, (darg (g i j) (g (i + 1) j) + darg (g (i + 1) (j + 1)) (g i (j + 1)))) +
        (∑ j ∈ Finset.range M, (darg (g (i + 1) j) (g (i + 1) (j + 1)) + darg (g i (j + 1)) (g i j))) :=
        fun i => Finset.sum_add_distrib
      simp_rw [h2]
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_comm
    rw [htotal] at h1
    rw [Finset.sum_congr rfl hhor, Finset.sum_congr rfl hvert] at h1
    exact h1.symm
  refine ⟨M, hM1, hre_h, hre_v, ?_⟩
  have hM_div : (M : ℝ) / (M : ℝ) = 1 := div_self hM_pos.ne'
  have h0_div : ((0 : ℕ) : ℝ) / (M : ℝ) = 0 := by simp
  simp only [Finset.sum_add_distrib] at hsplit
  have heq_b : ∀ i, g i 0 = F ((i : ℝ) / M, 0) := fun i => by simp [g]
  have heq_t : ∀ i, g i M = F ((i : ℝ) / M, 1) := fun i => by simp [g, hM_div]
  have heq_r : ∀ j, g M j = F (1, (j : ℝ) / M) := fun j => by simp [g, hM_div]
  have heq_l : ∀ j, g 0 j = F (0, (j : ℝ) / M) := fun j => by simp [g]
  simp only [heq_b, heq_t, heq_r, heq_l] at hsplit
  linarith

lemma cross_neg_imp_arg_lt {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hru : 0 ≤ u.re) (hrv : 0 ≤ v.re) (hc : cross u v < 0) :
    Complex.arg v < Complex.arg u := by
  have hau : |Complex.arg u| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_of_re_nonneg hu hru
  have hav : |Complex.arg v| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_of_re_nonneg hv hrv
  have hsin : Real.sin (Complex.arg v - Complex.arg u) = cross u v / (‖u‖ * ‖v‖) := by
    rw [Real.sin_sub, Complex.sin_arg, Complex.cos_arg hu, Complex.cos_arg hv, Complex.sin_arg]
    unfold cross
    have hu0 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    field_simp
  have hsin_neg : Real.sin (Complex.arg v - Complex.arg u) < 0 := by
    rw [hsin]
    exact div_neg_of_neg_of_pos hc (mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv))
  by_contra h
  push_neg at h
  have hle_pi : Complex.arg v - Complex.arg u ≤ Real.pi := by
    linarith [(abs_le.mp hau).1, (abs_le.mp hav).2]
  have hnn : 0 ≤ Real.sin (Complex.arg v - Complex.arg u) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hle_pi
  linarith

lemma halfplane_sum_darg_eq {c : ℂ} (hc : c ≠ 0) (g : ℕ → ℂ) (M : ℕ)
    (hne : ∀ i ≤ M, g i ≠ 0)
    (hre : ∀ i ≤ M, 0 ≤ (c * g i).re)
    (hpos : ∀ i < M, 0 < (g (i + 1) / g i).re) :
    ∑ i ∈ Finset.range M, darg (g i) (g (i + 1)) = Complex.arg (c * g M) - Complex.arg (c * g 0) := by
  have hterm : ∀ i ∈ Finset.range M,
      darg (g i) (g (i + 1)) = Complex.arg (c * g (i + 1)) - Complex.arg (c * g i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact darg_eq_sub_arg hc (hne i hi.le) (hne (i + 1) hi) (hre i hi.le) (hre (i + 1) hi) (hpos i hi)
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun i => Complex.arg (c * g i)) M]

lemma halfplane_sum_darg_rev_eq {c : ℂ} (hc : c ≠ 0) (g : ℕ → ℂ) (M : ℕ)
    (hne : ∀ i ≤ M, g i ≠ 0)
    (hre : ∀ i ≤ M, 0 ≤ (c * g i).re)
    (hpos : ∀ i < M, 0 < (g (i + 1) / g i).re) :
    ∑ i ∈ Finset.range M, darg (g (i + 1)) (g i) = Complex.arg (c * g 0) - Complex.arg (c * g M) := by
  have hterm : ∀ i ∈ Finset.range M,
      darg (g (i + 1)) (g i) = -(darg (g i) (g (i + 1))) := by
    intro i hi
    rw [Finset.mem_range] at hi
    linarith [darg_antisymm (hne i hi.le) (hne (i + 1) hi) (hpos i hi)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, halfplane_sum_darg_eq hc g M hne hre hpos]
  ring

theorem crossing_lemma {K : Set ℂ} {A B C D nA nB nC nD : ℂ}
    (hnA : nA ≠ 0) (hnB : nB ≠ 0) (hnC : nC ≠ 0) (hnD : nD ≠ 0)
    (hsupA : ∀ x ∈ K, dotC nA (x - A) ≤ 0)
    (hsupB : ∀ x ∈ K, dotC nB (x - B) ≤ 0)
    (hsupC : ∀ x ∈ K, dotC nC (x - C) ≤ 0)
    (hsupD : ∀ x ∈ K, dotC nD (x - D) ≤ 0)
    (hAB : cross (A - B) (C - B) < 0)
    (hBC : cross (C - B) (C - D) < 0)
    (hCD : cross (C - D) (A - D) < 0)
    (hDA : cross (A - D) (A - B) < 0)
    {α β : ℝ → ℂ}
    (hα_cont : ContinuousOn α (Icc 0 1)) (hβ_cont : ContinuousOn β (Icc 0 1))
    (hα_mem : ∀ s ∈ Icc (0 : ℝ) 1, α s ∈ K) (hβ_mem : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ K)
    (hα0 : α 0 = A) (hα1 : α 1 = C) (hβ0 : β 0 = B) (hβ1 : β 1 = D) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, α s = β t := by
  by_contra hdisj
  push_neg at hdisj
  let F : ℝ × ℝ → ℂ := fun p => α p.1 - β p.2
  have hF_cont : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    (hα_cont.comp continuousOn_fst (fun _ h => h.1)).sub
      (hβ_cont.comp continuousOn_snd (fun _ h => h.2))
  have hF_ne : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, F p ≠ 0 :=
    fun p hp => sub_ne_zero.mpr (hdisj p.1 hp.1 p.2 hp.2)
  obtain ⟨M, hM1, hre_h, hre_v, hsum0⟩ := grid_boundary_winding_zero F hF_cont hF_ne
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have hMdiv : (M : ℝ) / (M : ℝ) = 1 := div_self hMpos.ne'
  have hmemI : ∀ i ≤ M, (i : ℝ) / (M : ℝ) ∈ Icc (0 : ℝ) 1 := fun i hi =>
    ⟨div_nonneg (Nat.cast_nonneg _) hMpos.le, div_le_one_of_le₀ (by exact_mod_cast hi) hMpos.le⟩
  have hdot_re : ∀ n z : ℂ, (starRingEnd ℂ n * z).re = dotC n z := by
    intro n z; unfold dotC; simp
  -- Edge 1: F(i/M, 0) = α(i/M) - B, c1 = -(conj nB)
  let c1 : ℂ := -(starRingEnd ℂ nB)
  have hc1 : c1 ≠ 0 := neg_ne_zero.mpr (by simpa using hnB)
  have hE1 : ∑ i ∈ Finset.range M, darg (F ((i : ℝ) / M, 0)) (F (((i + 1 : ℕ) : ℝ) / M, 0)) =
      Complex.arg (c1 * (C - B)) - Complex.arg (c1 * (A - B)) := by
    have h := halfplane_sum_darg_eq hc1 (fun i => F ((i : ℝ) / M, 0)) M
      (fun i hi => hF_ne _ ⟨hmemI i hi, left_mem_Icc.mpr zero_le_one⟩)
      (fun i hi => by
        simp only [F, hβ0, c1, neg_mul, neg_re, hdot_re]
        linarith [hsupB _ (hα_mem _ (hmemI i hi))])
      (fun i hi => by simpa [show ((0 : ℕ) : ℝ) / M = 0 by simp] using hre_h i 0 hi (Nat.zero_le _))
    simpa [F, hα0, hα1, hβ0, hMdiv] using h
  -- Edge 2: F(1, j/M) = C - β(j/M), c2 = conj nC
  let c2 : ℂ := starRingEnd ℂ nC
  have hc2 : c2 ≠ 0 := by simpa [c2] using hnC
  have hE2 : ∑ j ∈ Finset.range M, darg (F (1, (j : ℝ) / M)) (F (1, ((j + 1 : ℕ) : ℝ) / M)) =
      Complex.arg (c2 * (C - D)) - Complex.arg (c2 * (C - B)) := by
    have h := halfplane_sum_darg_eq hc2 (fun j => F (1, (j : ℝ) / M)) M
      (fun j hj => hF_ne _ ⟨right_mem_Icc.mpr zero_le_one, hmemI j hj⟩)
      (fun j hj => by
        simp only [F, hα1, c2, hdot_re]
        have : dotC nC (C - β ((j : ℝ) / M)) = -dotC nC (β ((j : ℝ) / M) - C) := by unfold dotC; simp; ring
        linarith [hsupC _ (hβ_mem _ (hmemI j hj))])
      (fun j hj => by simpa [hMdiv] using hre_v M j le_rfl hj)
    simpa [F, hα1, hβ0, hβ1, hMdiv] using h
  -- Edge 3 (reversed): F((i+1)/M, 1) -> F(i/M, 1), c3 = -(conj nD)
  let c3 : ℂ := -(starRingEnd ℂ nD)
  have hc3 : c3 ≠ 0 := neg_ne_zero.mpr (by simpa using hnD)
  have hE3 : ∑ i ∈ Finset.range M, darg (F (((i + 1 : ℕ) : ℝ) / M, 1)) (F ((i : ℝ) / M, 1)) =
      Complex.arg (c3 * (A - D)) - Complex.arg (c3 * (C - D)) := by
    have h := halfplane_sum_darg_rev_eq hc3 (fun i => F ((i : ℝ) / M, 1)) M
      (fun i hi => hF_ne _ ⟨hmemI i hi, right_mem_Icc.mpr zero_le_one⟩)
      (fun i hi => by
        simp only [F, hβ1, c3, neg_mul, neg_re, hdot_re]
        linarith [hsupD _ (hα_mem _ (hmemI i hi))])
      (fun i hi => by simpa [hMdiv] using hre_h i M hi le_rfl)
    simpa [F, hα0, hα1, hβ1, hMdiv] using h
  -- Edge 4 (reversed): F(0, (j+1)/M) -> F(0, j/M), c4 = conj nA
  let c4 : ℂ := starRingEnd ℂ nA
  have hc4 : c4 ≠ 0 := by simpa [c4] using hnA
  have hE4 : ∑ j ∈ Finset.range M, darg (F (0, ((j + 1 : ℕ) : ℝ) / M)) (F (0, (j : ℝ) / M)) =
      Complex.arg (c4 * (A - B)) - Complex.arg (c4 * (A - D)) := by
    have h := halfplane_sum_darg_rev_eq hc4 (fun j => F (0, (j : ℝ) / M)) M
      (fun j hj => hF_ne _ ⟨left_mem_Icc.mpr zero_le_one, hmemI j hj⟩)
      (fun j hj => by
        simp only [F, hα0, c4, hdot_re]
        have : dotC nA (A - β ((j : ℝ) / M)) = -dotC nA (β ((j : ℝ) / M) - A) := by unfold dotC; simp; ring
        linarith [hsupA _ (hβ_mem _ (hmemI j hj))])
      (fun j hj => by simpa [show ((0 : ℕ) : ℝ) / M = 0 by simp] using hre_v 0 j (Nat.zero_le _) hj)
    simpa [F, hα0, hβ0, hβ1, hMdiv] using h
  -- Show each of the 4 terms is strictly negative!
  have hA_mem : A ∈ K := hα0 ▸ hα_mem 0 (left_mem_Icc.mpr zero_le_one)
  have hC_mem : C ∈ K := hα1 ▸ hα_mem 1 (right_mem_Icc.mpr zero_le_one)
  have hB_mem : B ∈ K := hβ0 ▸ hβ_mem 0 (left_mem_Icc.mpr zero_le_one)
  have hD_mem : D ∈ K := hβ1 ▸ hβ_mem 1 (right_mem_Icc.mpr zero_le_one)
  have hAB_ne : A - B ≠ 0 := by simpa [F, hα0, hβ0] using hF_ne (0, 0) ⟨left_mem_Icc.mpr zero_le_one, left_mem_Icc.mpr zero_le_one⟩
  have hCB_ne : C - B ≠ 0 := by simpa [F, hα1, hβ0] using hF_ne (1, 0) ⟨right_mem_Icc.mpr zero_le_one, left_mem_Icc.mpr zero_le_one⟩
  have hCD_ne : C - D ≠ 0 := by simpa [F, hα1, hβ1] using hF_ne (1, 1) ⟨right_mem_Icc.mpr zero_le_one, right_mem_Icc.mpr zero_le_one⟩
  have hAD_ne : A - D ≠ 0 := by simpa [F, hα0, hβ1] using hF_ne (0, 1) ⟨left_mem_Icc.mpr zero_le_one, right_mem_Icc.mpr zero_le_one⟩
  have hT1 : Complex.arg (c1 * (C - B)) < Complex.arg (c1 * (A - B)) := by
    apply cross_neg_imp_arg_lt (mul_ne_zero hc1 hAB_ne) (mul_ne_zero hc1 hCB_ne)
    · simp only [c1, neg_mul, neg_re, hdot_re]; linarith [hsupB A hA_mem]
    · simp only [c1, neg_mul, neg_re, hdot_re]; linarith [hsupB C hC_mem]
    · rw [cross_mul_unit]; exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hc1) hAB
  have hT2 : Complex.arg (c2 * (C - D)) < Complex.arg (c2 * (C - B)) := by
    apply cross_neg_imp_arg_lt (mul_ne_zero hc2 hCB_ne) (mul_ne_zero hc2 hCD_ne)
    · simp only [c2, hdot_re]
      have : dotC nC (C - B) = -dotC nC (B - C) := by unfold dotC; simp; ring
      linarith [hsupC B hB_mem]
    · simp only [c2, hdot_re]
      have : dotC nC (C - D) = -dotC nC (D - C) := by unfold dotC; simp; ring
      linarith [hsupC D hD_mem]
    · rw [cross_mul_unit]; exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hc2) hBC
  have hT3 : Complex.arg (c3 * (A - D)) < Complex.arg (c3 * (C - D)) := by
    apply cross_neg_imp_arg_lt (mul_ne_zero hc3 hCD_ne) (mul_ne_zero hc3 hAD_ne)
    · simp only [c3, neg_mul, neg_re, hdot_re]; linarith [hsupD C hC_mem]
    · simp only [c3, neg_mul, neg_re, hdot_re]; linarith [hsupD A hA_mem]
    · rw [cross_mul_unit]; exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hc3) hCD
  have hT4 : Complex.arg (c4 * (A - B)) < Complex.arg (c4 * (A - D)) := by
    apply cross_neg_imp_arg_lt (mul_ne_zero hc4 hAD_ne) (mul_ne_zero hc4 hAB_ne)
    · simp only [c4, hdot_re]
      have : dotC nA (A - D) = -dotC nA (D - A) := by unfold dotC; simp; ring
      linarith [hsupA D hD_mem]
    · simp only [c4, hdot_re]
      have : dotC nA (A - B) = -dotC nA (B - A) := by unfold dotC; simp; ring
      linarith [hsupA B hB_mem]
    · rw [cross_mul_unit]; exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hc4) hDA
  rw [hE1, hE2, hE3, hE4] at hsum0
  linarith

/- Section 4A: Polygonal curve parametrization and CCW convex hull polygon -/

noncomputable def polyAt {N : ℕ} (r : Fin (N + 1) → ℂ) (t : ℝ) : ℂ :=
  if hN : N = 0 then r ⟨0, by omega⟩
  else
    let k : ℕ := min (N - 1) ⌊t⌋₊
    let s : ℝ := t - (k : ℝ)
    (1 - s) • r ⟨k, by omega⟩ + s • r ⟨k + 1, by omega⟩

lemma polyAt_eq_on_edge {N : ℕ} (r : Fin (N + 1) → ℂ) (k : Fin N) {t : ℝ}
    (ht : t ∈ Icc (k : ℝ) ((k : ℝ) + 1)) :
    polyAt r t = (1 - (t - (k : ℝ))) • r k.castSucc + (t - (k : ℝ)) • r k.succ := by
  have hN : N ≠ 0 := by rintro rfl; exact k.elim0
  unfold polyAt
  rw [dif_neg hN]
  have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have ht_nn : 0 ≤ t := hk_nn.trans ht.1
  by_cases htop : t = (k : ℝ) + 1
  · subst htop
    have hfl : ⌊(k : ℝ) + 1⌋₊ = (k : ℕ) + 1 := by
      rw [show (k : ℝ) + 1 = (((k : ℕ) + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
    by_cases hlast : (k : ℕ) + 1 = N
    · have hmin : min (N - 1) ⌊(k : ℝ) + 1⌋₊ = (k : ℕ) := by rw [hfl]; omega
      simp only [hmin]
      have h1 : (⟨(k : ℕ), by omega⟩ : Fin (N + 1)) = k.castSucc := Fin.ext rfl
      have h2 : (⟨(k : ℕ) + 1, by omega⟩ : Fin (N + 1)) = k.succ := Fin.ext rfl
      rw [h1, h2]
    · have hmin : min (N - 1) ⌊(k : ℝ) + 1⌋₊ = (k : ℕ) + 1 := by rw [hfl]; omega
      simp only [hmin]
      have hdiff : ((k : ℝ) + 1) - (((k : ℕ) + 1 : ℕ) : ℝ) = 0 := by push_cast; ring
      rw [hdiff]
      have h1 : (⟨(k : ℕ) + 1, by omega⟩ : Fin (N + 1)) = k.succ := Fin.ext rfl
      rw [h1]
      simp
  · have ht_lt : t < (k : ℝ) + 1 := lt_of_le_of_ne ht.2 htop
    have hfl : ⌊t⌋₊ = (k : ℕ) := by
      rw [Nat.floor_eq_iff ht_nn]
      exact ⟨ht.1, ht_lt⟩
    have hmin : min (N - 1) ⌊t⌋₊ = (k : ℕ) := by rw [hfl]; omega
    simp only [hmin]
    have h1 : (⟨(k : ℕ), by omega⟩ : Fin (N + 1)) = k.castSucc := Fin.ext rfl
    have h2 : (⟨(k : ℕ) + 1, by omega⟩ : Fin (N + 1)) = k.succ := Fin.ext rfl
    rw [h1, h2]

lemma polyAt_nat {N : ℕ} (r : Fin (N + 1) → ℂ) (k : Fin (N + 1)) :
    polyAt r (k : ℝ) = r k := by
  by_cases hN : N = 0
  · subst hN
    have hk0 : k = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst hk0; simp [polyAt]
  · by_cases hlast : (k : ℕ) = N
    · let k' : Fin N := ⟨N - 1, by omega⟩
      have hk'_eq : (k' : ℝ) + 1 = (k : ℝ) := by
        dsimp [k']; rw [hlast, Nat.cast_sub (by omega : 1 ≤ N)]; simp
      have ht : (k : ℝ) ∈ Icc (k' : ℝ) ((k' : ℝ) + 1) := ⟨by linarith, by linarith⟩
      rw [polyAt_eq_on_edge r k' ht]
      have hsub : (k : ℝ) - (k' : ℝ) = 1 := by linarith
      rw [hsub, sub_self, zero_smul, zero_add, one_smul]
      congr 1; ext; simp [k']; omega
    · let k' : Fin N := ⟨(k : ℕ), by omega⟩
      have ht : (k : ℝ) ∈ Icc (k' : ℝ) ((k' : ℝ) + 1) := ⟨le_rfl, by linarith⟩
      rw [polyAt_eq_on_edge r k' ht]
      have hsub : (k : ℝ) - (k' : ℝ) = 0 := by simp [k']
      rw [hsub, sub_zero, one_smul, zero_smul, add_zero]
      congr 1

lemma polyAt_mem_segment {N : ℕ} (r : Fin (N + 1) → ℂ) (k : Fin N) {t : ℝ}
    (ht : t ∈ Icc (k : ℝ) ((k : ℝ) + 1)) :
    polyAt r t ∈ segment ℝ (r k.castSucc) (r k.succ) := by
  rw [polyAt_eq_on_edge r k ht]
  exact ⟨1 - (t - (k : ℝ)), t - (k : ℝ), by linarith [ht.2], by linarith [ht.1], by ring, rfl⟩

lemma polyAt_continuousOn_Icc {N : ℕ} (r : Fin (N + 1) → ℂ) :
    ContinuousOn (polyAt r) (Icc (0 : ℝ) (N : ℝ)) := by
  have hstep : ∀ m : ℕ, m ≤ N → ContinuousOn (polyAt r) (Icc (0 : ℝ) (m : ℝ)) := by
    intro m hm
    induction m with
    | zero =>
      simp only [Nat.cast_zero, Set.Icc_self]
      exact continuousOn_singleton _ _
    | succ m ih =>
      let k : Fin N := ⟨m, by omega⟩
      have hunion : Icc (0 : ℝ) (((m + 1 : ℕ) : ℝ)) =
          Icc (0 : ℝ) (m : ℝ) ∪ Icc (k : ℝ) ((k : ℝ) + 1) := by
        ext t
        simp only [Set.mem_Icc, Set.mem_union, k, Nat.cast_add, Nat.cast_one]
        constructor
        · intro ⟨h0, h1⟩
          rcases le_or_gt t (m : ℝ) with h | h
          · exact Or.inl ⟨h0, h⟩
          · exact Or.inr ⟨h.le, h1⟩
        · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
          · exact ⟨h0, by linarith⟩
          · exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) m], h1⟩
      rw [hunion]
      have hcont_k : ContinuousOn (polyAt r) (Icc (k : ℝ) ((k : ℝ) + 1)) := by
        have hlin : ContinuousOn (fun t : ℝ => (1 - (t - (k : ℝ))) • r k.castSucc + (t - (k : ℝ)) • r k.succ)
            (Icc (k : ℝ) ((k : ℝ) + 1)) := by
          fun_prop
        exact hlin.congr fun t ht => polyAt_eq_on_edge r k ht
      exact (ih (Nat.le_of_succ_le hm)).union_of_isClosed hcont_k isClosed_Icc isClosed_Icc
  exact hstep N le_rfl

lemma polyAt_mem_convexHull {N : ℕ} (r : Fin (N + 1) → ℂ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (N : ℝ)) :
    polyAt r t ∈ convexHull ℝ (Set.range r) := by
  by_cases hN : N = 0
  · subst hN
    have ht0 : t = 0 := le_antisymm (by simpa using ht.2) ht.1
    subst ht0
    rw [show (0 : ℝ) = ((⟨0, by omega⟩ : Fin 1) : ℝ) by simp, polyAt_nat]
    exact subset_convexHull ℝ _ ⟨_, rfl⟩
  · let kNat : ℕ := min (N - 1) ⌊t⌋₊
    let k : Fin N := ⟨kNat, by omega⟩
    have htk : t ∈ Icc (k : ℝ) ((k : ℝ) + 1) := by
      by_cases hlt : ⌊t⌋₊ < N
      · have hk_eq : kNat = ⌊t⌋₊ := min_eq_right (by omega)
        change (kNat : ℝ) ≤ t ∧ t ≤ (kNat : ℝ) + 1
        rw [hk_eq]
        exact ⟨Nat.floor_le ht.1, (Nat.lt_floor_add_one t).le⟩
      · have hge : (N : ℝ) ≤ t := by
          have : N ≤ ⌊t⌋₊ := not_lt.mp hlt
          exact (by exact_mod_cast this : (N : ℝ) ≤ (⌊t⌋₊ : ℝ)).trans (Nat.floor_le ht.1)
        have htN : t = (N : ℝ) := le_antisymm ht.2 hge
        have hk_eq : kNat = N - 1 := min_eq_left (by omega)
        change (kNat : ℝ) ≤ t ∧ t ≤ (kNat : ℝ) + 1
        rw [hk_eq, htN]
        have hN1 : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by norm_cast; omega
        exact ⟨by linarith, by linarith⟩
    have hmem := polyAt_mem_segment r k htk
    exact (convex_convexHull ℝ (Set.range r)).segment_subset
      (subset_convexHull ℝ _ ⟨k.castSucc, rfl⟩)
      (subset_convexHull ℝ _ ⟨k.succ, rfl⟩) hmem

lemma polyAt_injOn {N : ℕ} {r : Fin (N + 1) → ℂ} (hgp : GenPos r) (hsimp : IsSimplePoly r) :
    Set.InjOn (polyAt r) (Icc (0 : ℝ) (N : ℝ)) := by
  have hne_of_lt : ∀ s ∈ Icc (0 : ℝ) (N : ℝ), ∀ t ∈ Icc (0 : ℝ) (N : ℝ),
      s < t → polyAt r s ≠ polyAt r t := by
    intro s hs t ht hlt heq
    have hN : N ≠ 0 := by
      intro h0; subst h0; simp only [Nat.cast_zero, Set.mem_Icc] at hs ht; linarith
    have hs_ltN : s < (N : ℝ) := lt_of_lt_of_le hlt ht.2
    have hfl_s : ⌊s⌋₊ < N := (Nat.floor_lt hs.1).mpr hs_ltN
    let i : Fin N := ⟨⌊s⌋₊, hfl_s⟩
    have hsi : s ∈ Icc (i : ℝ) ((i : ℝ) + 1) :=
      ⟨Nat.floor_le hs.1, (Nat.lt_floor_add_one s).le⟩
    have hs_lt_i1 : s < (i : ℝ) + 1 := Nat.lt_floor_add_one s
    let jNat : ℕ := min (N - 1) ⌊t⌋₊
    let j : Fin N := ⟨jNat, by omega⟩
    have htj : t ∈ Icc (j : ℝ) ((j : ℝ) + 1) := by
      by_cases hltN : ⌊t⌋₊ < N
      · have hj_eq : jNat = ⌊t⌋₊ := min_eq_right (by omega)
        change (jNat : ℝ) ≤ t ∧ t ≤ (jNat : ℝ) + 1
        rw [hj_eq]
        exact ⟨Nat.floor_le ht.1, (Nat.lt_floor_add_one t).le⟩
      · have htN : t = (N : ℝ) := le_antisymm ht.2 ((by exact_mod_cast not_lt.mp hltN : (N : ℝ) ≤ ⌊t⌋₊).trans (Nat.floor_le ht.1))
        have hj_eq : jNat = N - 1 := min_eq_left (by omega)
        change (jNat : ℝ) ≤ t ∧ t ≤ (jNat : ℝ) + 1
        rw [hj_eq, htN]
        have hN1 : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by norm_cast; omega
        exact ⟨by linarith, by linarith⟩
    have hij_le : (i : ℕ) ≤ (j : ℕ) := by
      have h1 : ⌊s⌋₊ ≤ ⌊t⌋₊ := Nat.floor_mono hlt.le
      change ⌊s⌋₊ ≤ min (N - 1) ⌊t⌋₊
      omega
    by_cases hsame : (i : ℕ) = (j : ℕ)
    · have hij : i = j := Fin.ext hsame
      rw [← hij] at htj
      rw [polyAt_eq_on_edge r i hsi, polyAt_eq_on_edge r i htj] at heq
      have hdiff : (t - s) • (r i.succ - r i.castSucc) = 0 := by
        have h1 : ((1 - (t - (i : ℝ))) • r i.castSucc + (t - (i : ℝ)) • r i.succ) -
            ((1 - (s - (i : ℝ))) • r i.castSucc + (s - (i : ℝ)) • r i.succ) =
            (t - s) • (r i.succ - r i.castSucc) := by
          simp only [Complex.real_smul]; push_cast; ring
        rw [← h1, heq, sub_self]
      rcases smul_eq_zero.mp hdiff with h0 | h0
      · linarith
      · exact hgp.1 i.succ i.castSucc (by intro h; simp [Fin.ext_iff] at h) (sub_eq_zero.mp h0)
    · by_cases hadj : (i : ℕ) + 1 = (j : ℕ)
      · have h1 := polyAt_eq_on_edge r i hsi
        have h2 := polyAt_eq_on_edge r j htj
        have hmid_eq : i.succ = j.castSucc := Fin.ext (by simp [hadj])
        have hvec1 : polyAt r s - r i.succ = ((s - ((i : ℝ) + 1)) : ℝ) • (r i.succ - r i.castSucc) := by
          rw [h1]; simp only [Complex.real_smul]; push_cast; ring
        have hvec2 : polyAt r t - r i.succ = (t - (j : ℝ)) • (r j.succ - r i.succ) := by
          rw [h2, ← hmid_eq]; simp only [Complex.real_smul]; push_cast; ring
        have hcross0 : cross (polyAt r s - r i.succ) (polyAt r t - r i.succ) = 0 := by
          rw [heq, cross_self]
        rw [hvec1, hvec2, cross_smul_left, cross_smul_right] at hcross0
        have hne1 : s - ((i : ℝ) + 1) ≠ 0 := by linarith
        have hne2 : t - (j : ℝ) ≠ 0 := by
          intro ht0
          have hzero : ((s - ((i : ℝ) + 1)) : ℝ) • (r i.succ - r i.castSucc) = 0 := by
            rw [← hvec1, heq, hvec2, ht0, zero_smul]
          rcases smul_eq_zero.mp hzero with h0 | h0
          · exact hne1 h0
          · exact hgp.1 i.succ i.castSucc (by intro h; simp [Fin.ext_iff] at h) (sub_eq_zero.mp h0)
        have hcross_pts : cross (r i.succ - r i.castSucc) (r j.succ - r i.succ) = 0 :=
          (mul_eq_zero.mp ((mul_eq_zero.mp hcross0).resolve_left hne1)).resolve_left hne2
        have hcross_gp : cross (r i.succ - r i.castSucc) (r j.succ - r i.castSucc) = 0 := by
          have hsplit : r j.succ - r i.castSucc = (r j.succ - r i.succ) + (r i.succ - r i.castSucc) := by ring
          rw [hsplit, cross_add_right, hcross_pts, cross_self, add_zero]
        exact hgp.2 i.castSucc i.succ j.succ
          (by intro h; simp [Fin.ext_iff] at h)
          (by intro h; simp [Fin.ext_iff] at h; omega)
          (by intro h; simp [Fin.ext_iff] at h; omega) hcross_gp
      · have hfar : (i : ℕ) + 1 < (j : ℕ) := by omega
        have hmi := polyAt_mem_segment r i hsi
        have hmj := polyAt_mem_segment r j htj
        rw [heq] at hmi
        exact Set.disjoint_left.mp (hsimp i j hfar) hmi hmj
  intro s hs t ht heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hne_of_lt s hs t ht hlt heq
  · exact hne_of_lt t ht s hs hlt heq.symm

noncomputable def polySubpath {N : ℕ} (r : Fin (N + 1) → ℂ) (a b : Fin (N + 1)) (u : ℝ) : ℂ :=
  polyAt r ((1 - u) * (a : ℝ) + u * (b : ℝ))

lemma polySubpath_continuousOn {N : ℕ} (r : Fin (N + 1) → ℂ) (a b : Fin (N + 1)) :
    ContinuousOn (polySubpath r a b) (Icc (0 : ℝ) 1) := by
  refine (polyAt_continuousOn_Icc r).comp (by fun_prop) ?_
  intro u hu
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
  have haN : (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ a.isLt
  have hbN : (b : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ b.isLt
  exact ⟨by nlinarith [hu.1, hu.2], by nlinarith [hu.1, hu.2]⟩

lemma polySubpath_zero {N : ℕ} (r : Fin (N + 1) → ℂ) (a b : Fin (N + 1)) :
    polySubpath r a b 0 = r a := by
  simp [polySubpath, polyAt_nat]

lemma polySubpath_one {N : ℕ} (r : Fin (N + 1) → ℂ) (a b : Fin (N + 1)) :
    polySubpath r a b 1 = r b := by
  simp [polySubpath, polyAt_nat]

lemma polySubpath_mem_convexHull {N : ℕ} (r : Fin (N + 1) → ℂ) (a b : Fin (N + 1))
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    polySubpath r a b u ∈ convexHull ℝ (Set.range r) := by
  apply polyAt_mem_convexHull
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
  have haN : (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ a.isLt
  have hbN : (b : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ b.isLt
  exact ⟨by nlinarith [hu.1, hu.2], by nlinarith [hu.1, hu.2]⟩

lemma polyLen_sub_ge_norm {N : ℕ} (r : Fin (N + 1) → ℂ) {a b : Fin (N + 1)} (hab : a ≤ b) :
    ‖r b - r a‖ ≤ ∑ k ∈ (Finset.univ : Finset (Fin N)).filter (fun k : Fin N => (a : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) < (b : ℕ)),
      ‖r k.succ - r k.castSucc‖ := by
  have haux : ∀ d : ℕ, ∀ (ha : (a : ℕ) + d ≤ N),
      ‖r ⟨(a : ℕ) + d, by omega⟩ - r a‖ ≤
        ∑ k ∈ (Finset.univ : Finset (Fin N)).filter (fun k : Fin N => (a : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) < (a : ℕ) + d),
          ‖r k.succ - r k.castSucc‖ := by
    intro d
    induction d with
    | zero =>
      intro _
      have heq : (⟨(a : ℕ) + 0, by omega⟩ : Fin (N + 1)) = a := Fin.ext (by simp)
      rw [heq, sub_self, norm_zero]
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    | succ d ih =>
      intro hd
      let k0 : Fin N := ⟨(a : ℕ) + d, by omega⟩
      have hsplit_set :
          (Finset.univ : Finset (Fin N)).filter (fun k : Fin N => (a : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) < (a : ℕ) + (d + 1)) =
          insert k0 ((Finset.univ : Finset (Fin N)).filter (fun k : Fin N => (a : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) < (a : ℕ) + d)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, k0]
        omega
      have hk0_not : k0 ∉ (Finset.univ : Finset (Fin N)).filter (fun k : Fin N => (a : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) < (a : ℕ) + d) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, k0, Fin.val_mk]; omega
      rw [hsplit_set, Finset.sum_insert hk0_not]
      have htri : ‖r ⟨(a : ℕ) + (d + 1), by omega⟩ - r a‖ ≤
          ‖r k0.succ - r k0.castSucc‖ + ‖r ⟨(a : ℕ) + d, by omega⟩ - r a‖ := by
        have h1 : r ⟨(a : ℕ) + (d + 1), by omega⟩ - r a =
            (r k0.succ - r k0.castSucc) + (r ⟨(a : ℕ) + d, by omega⟩ - r a) := by
          have hs : k0.succ = ⟨(a : ℕ) + (d + 1), by omega⟩ := Fin.ext (by simp [k0]; omega)
          have hc : k0.castSucc = ⟨(a : ℕ) + d, by omega⟩ := Fin.ext (by simp [k0])
          rw [hs, hc]; ring
        rw [h1]
        exact norm_add_le _ _
      linarith [ih (by omega)]
  have hb_eq : b = ⟨(a : ℕ) + ((b : ℕ) - (a : ℕ)), by omega⟩ := Fin.ext (by simp; omega)
  have h1 := haux ((b : ℕ) - (a : ℕ)) (by omega)
  have h2 : (a : ℕ) + ((b : ℕ) - (a : ℕ)) = (b : ℕ) := by omega
  simpa [← hb_eq, h2] using h1

lemma norm_sub_le_polyLen {N : ℕ} (r : Fin (N + 1) → ℂ) (a b : Fin (N + 1)) :
    ‖r b - r a‖ ≤ polyLen r := by
  wlog hab : a ≤ b generalizing a b
  · rw [norm_sub_rev]
    exact this b a (le_of_not_ge hab)
  calc ‖r b - r a‖
      ≤ ∑ k ∈ (Finset.univ : Finset (Fin N)).filter (fun k : Fin N => (a : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) < (b : ℕ)),
          ‖r k.succ - r k.castSucc‖ := polyLen_sub_ge_norm r hab
    _ ≤ ∑ k ∈ (Finset.univ : Finset (Fin N)), ‖r k.succ - r k.castSucc‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)

lemma chain_le_polyLen {N : ℕ} (r : Fin (N + 1) → ℂ) :
    ∀ (l : List (Fin (N + 1))), l.IsChain (· ≤ ·) →
      (l.zipWith (fun x y => ‖r y - r x‖) l.tail).sum ≤ polyLen r := by
  have haux : ∀ (a : Fin (N + 1)) (l : List (Fin (N + 1))),
      (a :: l).IsChain (· ≤ ·) →
      ((a :: l).zipWith (fun x y => ‖r y - r x‖) l).sum ≤
        ∑ k ∈ (Finset.univ : Finset (Fin N)).filter
          (fun k : Fin N => (a : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) < ((a :: l).getLast (List.cons_ne_nil _ _) : ℕ)),
          ‖r k.succ - r k.castSucc‖ := by
    intro a l
    induction l generalizing a with
    | nil =>
      intro _
      simp only [List.zipWith_nil_right, List.sum_nil]
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    | cons b t ih =>
      intro hch
      have ⟨hab, ht_ch⟩ := List.isChain_cons_cons.mp hch
      have hb_le_last : b ≤ (b :: t).getLast (List.cons_ne_nil _ _) := by
        clear ih hab hch
        induction t generalizing b with
        | nil => simp
        | cons c t' ih' =>
          have ⟨hbc, hc_ch⟩ := List.isChain_cons_cons.mp ht_ch
          have hlast : (b :: c :: t').getLast (List.cons_ne_nil _ _) = (c :: t').getLast (List.cons_ne_nil _ _) := rfl
          rw [hlast]
          exact hbc.trans (ih' c hc_ch)
      have hstep1 := polyLen_sub_ge_norm r hab
      have hstep2 := ih b ht_ch
      have hlast_eq : (a :: b :: t).getLast (List.cons_ne_nil _ _) = (b :: t).getLast (List.cons_ne_nil _ _) := rfl
      rw [hlast_eq]
      let S1 := (Finset.univ : Finset (Fin N)).filter (fun k : Fin N => (a : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) < (b : ℕ))
      let S2 := (Finset.univ : Finset (Fin N)).filter (fun k : Fin N => (b : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) < ((b :: t).getLast (List.cons_ne_nil _ _) : ℕ))
      let S := (Finset.univ : Finset (Fin N)).filter (fun k : Fin N => (a : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) < ((b :: t).getLast (List.cons_ne_nil _ _) : ℕ))
      have hdisj : Disjoint S1 S2 := by
        rw [Finset.disjoint_left]
        intro k hk1 hk2
        simp only [S1, S2, Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
        omega
      have hunion : S1 ∪ S2 = S := by
        ext k
        simp only [S1, S2, S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        have h1 : (a : ℕ) ≤ (b : ℕ) := hab
        have h2 : (b : ℕ) ≤ ((b :: t).getLast (List.cons_ne_nil _ _) : ℕ) := hb_le_last
        omega
      have hsum_eq : (∑ k ∈ S1, ‖r k.succ - r k.castSucc‖) + (∑ k ∈ S2, ‖r k.succ - r k.castSucc‖) =
          ∑ k ∈ S, ‖r k.succ - r k.castSucc‖ := by
        rw [← Finset.sum_union hdisj, hunion]
      have hzip : ((a :: b :: t).zipWith (fun x y => ‖r y - r x‖) (b :: t)).sum =
          ‖r b - r a‖ + ((b :: t).zipWith (fun x y => ‖r y - r x‖) t).sum := by
        simp [List.zipWith_cons_cons, List.sum_cons]
      rw [hzip]
      linarith
  intro l hch
  cases l with
  | nil =>
    simp only [List.tail_nil, List.zipWith_nil_right, List.sum_nil]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  | cons a t =>
    calc ((a :: t).zipWith (fun x y => ‖r y - r x‖) t).sum
        ≤ ∑ k ∈ (Finset.univ : Finset (Fin N)).filter
            (fun k : Fin N => (a : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) < ((a :: t).getLast (List.cons_ne_nil _ _) : ℕ)),
            ‖r k.succ - r k.castSucc‖ := haux a t hch
      _ ≤ polyLen r :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)

/- Extreme points and CCW convex hull polygon -/

def IsExtreme {N : ℕ} (r : Fin (N + 1) → ℂ) (k : Fin (N + 1)) : Prop :=
  ∃ u : ℂ, u ≠ 0 ∧ ∀ i, i ≠ k → dotC u (r i - r k) < 0

lemma dotC_I_mul (u z : ℂ) : dotC (I * u) z = cross u z := by
  unfold dotC cross; simp; ring

lemma exists_extreme_max_dot {N : ℕ} {r : Fin (N + 1) → ℂ} (hgp : GenPos r)
    {u : ℂ} (hu : u ≠ 0) :
    ∃ k : Fin (N + 1), IsExtreme r k ∧ ∀ i, dotC u (r i) ≤ dotC u (r k) := by
  obtain ⟨k0, _, hk0_max⟩ := Finset.exists_max_image Finset.univ (fun i => dotC u (r i))
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  let M : ℝ := dotC u (r k0)
  let topSet := (Finset.univ : Finset (Fin (N + 1))).filter (fun i => dotC u (r i) = M)
  have htop_ne : topSet.Nonempty := ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  obtain ⟨k, hk_mem, hk_max⟩ := Finset.exists_max_image topSet (fun i => cross u (r i)) htop_ne
  have hk_eq : dotC u (r k) = M := (Finset.mem_filter.mp hk_mem).2
  have hle_all : ∀ i, dotC u (r i) ≤ dotC u (r k) := fun i => by
    rw [hk_eq]; exact hk0_max i (Finset.mem_univ i)
  have hlex : ∀ i, i ≠ k → dotC u (r i - r k) < 0 ∨ (dotC u (r i - r k) = 0 ∧ cross u (r i - r k) < 0) := by
    intro i hik
    have h1 : dotC u (r i - r k) ≤ 0 := by
      have : dotC u (r i - r k) = dotC u (r i) - dotC u (r k) := by unfold dotC; simp; ring
      linarith [hle_all i]
    rcases lt_or_eq_of_le h1 with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      have hi_top : i ∈ topSet := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        have : dotC u (r i - r k) = dotC u (r i) - dotC u (r k) := by unfold dotC; simp; ring
        linarith⟩
      have hcr_le : cross u (r i - r k) ≤ 0 := by
        rw [cross_sub_right]
        linarith [hk_max i hi_top]
      rcases lt_or_eq_of_le hcr_le with hlt | hcr0
      · exact hlt
      · exfalso
        have hsq := dotC_sq_add_cross_sq u (r i - r k)
        rw [heq, hcr0] at hsq
        norm_num at hsq
        rcases hsq with h0 | h0
        · exact hu h0
        · exact hgp.1 i k hik (sub_eq_zero.mp h0)
  let badSet := (Finset.univ : Finset (Fin (N + 1))).filter (fun i => dotC u (r i - r k) < 0)
  have hex_eps : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ badSet, dotC u (r i - r k) + ε * cross u (r i - r k) < 0 := by
    by_cases hne : badSet.Nonempty
    · obtain ⟨i1, hi1, hmax_c⟩ := Finset.exists_max_image badSet (fun i => |cross u (r i - r k)| + 1) hne
      obtain ⟨i2, hi2, hmax_d⟩ := Finset.exists_max_image badSet (fun i => dotC u (r i - r k)) hne
      have hd_neg : dotC u (r i2 - r k) < 0 := (Finset.mem_filter.mp hi2).2
      have hd_pos : 0 < -dotC u (r i2 - r k) := by linarith
      have hc_pos : 0 < |cross u (r i1 - r k)| + 1 := by positivity
      let ε := (-dotC u (r i2 - r k)) / (2 * (|cross u (r i1 - r k)| + 1))
      have hε_pos : 0 < ε := div_pos hd_pos (by linarith)
      refine ⟨ε, hε_pos, fun i hi => ?_⟩
      have hdi : dotC u (r i - r k) ≤ dotC u (r i2 - r k) := hmax_d i hi
      have hci : |cross u (r i - r k)| + 1 ≤ |cross u (r i1 - r k)| + 1 := hmax_c i hi
      have hci' : cross u (r i - r k) ≤ |cross u (r i1 - r k)| + 1 := by
        linarith [le_abs_self (cross u (r i - r k))]
      have hmul : ε * cross u (r i - r k) ≤ (-dotC u (r i2 - r k)) / 2 := by
        calc ε * cross u (r i - r k)
            ≤ ε * (|cross u (r i1 - r k)| + 1) := mul_le_mul_of_nonneg_left hci' hε_pos.le
          _ = (-dotC u (r i2 - r k)) / 2 := by dsimp [ε]; field_simp
      linarith
    · exact ⟨1, zero_lt_one, fun i hi => absurd ⟨i, hi⟩ hne⟩
  obtain ⟨ε, hε_pos, hε⟩ := hex_eps
  let u' : ℂ := u + (ε : ℂ) * (I * u)
  have hu'_ne : u' ≠ 0 := by
    have h1 : u' = (1 + (ε : ℂ) * I) * u := by dsimp [u']; ring
    rw [h1]
    apply mul_ne_zero _ hu
    intro h0
    have := congrArg Complex.re h0
    simp at this
  refine ⟨k, ⟨u', hu'_ne, fun i hik => ?_⟩, hle_all⟩
  have hdot_u' : dotC u' (r i - r k) = dotC u (r i - r k) + ε * cross u (r i - r k) := by
    unfold dotC cross u'
    simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  rw [hdot_u']
  rcases hlex i hik with hlt | ⟨heq, hcr⟩
  · exact hε i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
  · rw [heq, zero_add]; exact mul_neg_of_pos_of_neg hε_pos hcr

noncomputable def shiftArg (x : ℝ) : ℝ := if 0 ≤ x then x else x + 2 * Real.pi

lemma shiftArg_nonneg {x : ℝ} (hx : -2 * Real.pi < x) : 0 ≤ shiftArg x := by
  unfold shiftArg; split_ifs <;> linarith

lemma shiftArg_lt {x : ℝ} (hx : x < 2 * Real.pi) : shiftArg x < 2 * Real.pi := by
  unfold shiftArg; split_ifs <;> linarith

lemma exp_shiftArg_mul_I (x : ℝ) : Complex.exp ((shiftArg x : ℂ) * I) = Complex.exp ((x : ℂ) * I) := by
  unfold shiftArg
  split_ifs
  · rfl
  · rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    have h2pi : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by
      rw [Complex.exp_eq_one_iff]; exact ⟨1, by push_cast; ring⟩
    rw [h2pi, mul_one]

lemma shiftArg_sub_arg_eq_zero_iff {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    shiftArg (Complex.arg a - Complex.arg b) = 0 ↔ ∃ t : ℝ, 0 < t ∧ a = t • b := by
  have ha_m := Complex.arg_mem_Ioc a
  have hb_m := Complex.arg_mem_Ioc b
  have hlo : -2 * Real.pi < Complex.arg a - Complex.arg b := by linarith [ha_m.1, hb_m.2]
  have hhi : Complex.arg a - Complex.arg b < 2 * Real.pi := by linarith [ha_m.2, hb_m.1]
  constructor
  · intro h0
    have harg : Complex.arg a = Complex.arg b := by
      unfold shiftArg at h0
      split_ifs at h0 <;> linarith
    refine ⟨‖a‖ / ‖b‖, div_pos (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb), ?_⟩
    have hbn : (‖b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb)
    calc a = (‖a‖ : ℂ) * Complex.exp ((Complex.arg a : ℂ) * I) := (Complex.norm_mul_exp_arg_mul_I a).symm
      _ = ((‖a‖ : ℂ) / (‖b‖ : ℂ)) * ((‖b‖ : ℂ) * Complex.exp ((Complex.arg b : ℂ) * I)) := by
            rw [harg, ← mul_assoc, div_mul_cancel₀ _ hbn]
      _ = (‖a‖ / ‖b‖ : ℝ) • b := by
            rw [Complex.norm_mul_exp_arg_mul_I b, Complex.real_smul, Complex.ofReal_div]
  · rintro ⟨t, ht, rfl⟩
    have harg : Complex.arg (t • b) = Complex.arg b := by
      rw [Complex.real_smul, Complex.arg_real_mul _ ht]
    rw [harg, sub_self]
    simp [shiftArg]

lemma cross_pos_iff_shiftArg_lt_pi {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    0 < cross a b ↔ 0 < shiftArg (Complex.arg b - Complex.arg a) ∧
      shiftArg (Complex.arg b - Complex.arg a) < Real.pi := by
  set θ := shiftArg (Complex.arg b - Complex.arg a)
  have ha_m := Complex.arg_mem_Ioc a
  have hb_m := Complex.arg_mem_Ioc b
  have hθ0 : 0 ≤ θ := shiftArg_nonneg (by linarith [ha_m.2, hb_m.1])
  have hθ2 : θ < 2 * Real.pi := shiftArg_lt (by linarith [ha_m.1, hb_m.2])
  have hsin : Real.sin θ = cross a b / (‖a‖ * ‖b‖) := by
    have heq : Real.sin θ = Real.sin (Complex.arg b - Complex.arg a) := by
      have h1 := congrArg Complex.im (exp_shiftArg_mul_I (Complex.arg b - Complex.arg a))
      rw [Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im] at h1
      exact h1
    rw [heq, Real.sin_sub, Complex.sin_arg, Complex.cos_arg ha, Complex.cos_arg hb, Complex.sin_arg]
    unfold cross
    have ha0 : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have hb0 : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
    field_simp
  have hden : 0 < ‖a‖ * ‖b‖ := mul_pos (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb)
  constructor
  · intro hc
    have hsp : 0 < Real.sin θ := by rw [hsin]; exact div_pos hc hden
    constructor
    · rcases eq_or_lt_of_le hθ0 with h0 | hpos
      · exfalso; rw [← h0, Real.sin_zero] at hsp; linarith
      · exact hpos
    · by_contra hge
      push Not at hge
      have hle : Real.sin θ ≤ 0 := by
        have h1 : Real.sin (θ - Real.pi) ≥ 0 :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
        rw [Real.sin_sub_pi] at h1
        linarith
      linarith
  · rintro ⟨h1, h2⟩
    have hsp : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h1 h2
    rw [hsin, div_pos_iff_of_pos_right hden] at hsp
    exact hsp

lemma shiftArg_sub_cyclic_lt {a b c : ℝ}
    (hbc_diff : b - c < 2 * Real.pi)
    (h_between : (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b)) :
    shiftArg (b - a) < shiftArg (c - a) := by
  unfold shiftArg
  rcases h_between with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos (by linarith), if_pos (by linarith)]; linarith
  · rw [if_neg (by linarith), if_neg (by linarith)]; linarith
  · rw [if_pos (by linarith), if_neg (by linarith)]; linarith

lemma extreme_not_strict_comb {N : ℕ} {r : Fin (N + 1) → ℂ} {O : ℂ} {k0 k1 k2 : Fin (N + 1)}
    (hk0 : IsExtreme r k0)
    (hO : ∀ u : ℂ, (∀ i, i ≠ k0 → dotC u (r i - r k0) < 0) → dotC u (O - r k0) < 0)
    (h01 : k0 ≠ k1) (h02 : k0 ≠ k2)
    {gam mu lam : ℝ} (hgam : 0 < gam) (hmu : 0 ≤ mu) (hlam : 0 < lam)
    (hsum1 : lam + mu + gam = 1) (hcomb : r k0 = gam • O + mu • r k1 + lam • r k2) : False := by
  obtain ⟨un, _, hun⟩ := hk0
  have hnegO := hO un hun
  have hneg1 := hun k1 h01.symm
  have hneg2 := hun k2 h02.symm
  have hdiff : gam • (O - r k0) + mu • (r k1 - r k0) + lam • (r k2 - r k0) = 0 := by
    simp only [Complex.real_smul] at hcomb ⊢
    have hs : (lam : ℂ) + (mu : ℂ) + (gam : ℂ) = 1 := by exact_mod_cast hsum1
    linear_combination -hcomb - r k0 * hs
  have hdot0 : gam * dotC un (O - r k0) + mu * dotC un (r k1 - r k0) + lam * dotC un (r k2 - r k0) = 0 := by
    have h1 : dotC un (gam • (O - r k0) + mu • (r k1 - r k0) + lam • (r k2 - r k0)) = 0 := by
      rw [hdiff]; simp [dotC]
    have h2 : dotC un (gam • (O - r k0) + mu • (r k1 - r k0) + lam • (r k2 - r k0)) =
        gam * dotC un (O - r k0) + mu * dotC un (r k1 - r k0) + lam * dotC un (r k2 - r k0) := by
      unfold dotC; simp; ring
    linarith
  nlinarith

lemma cramer_triangle_eq (O P Q R : ℂ) {d : ℝ} (hd : d = cross (Q - O) (R - O)) (hd0 : d ≠ 0) :
    P = ((cross (Q - O) (R - O) - cross (P - O) (R - O) - cross (Q - O) (P - O)) / d) • O +
        (cross (P - O) (R - O) / d) • Q + (cross (Q - O) (P - O) / d) • R := by
  apply Complex.ext
  · simp only [add_re, smul_re, smul_eq_mul]
    rw [hd] at hd0 ⊢
    field_simp [hd0]
    unfold cross; simp; ring
  · simp only [add_im, smul_im, smul_eq_mul]
    rw [hd] at hd0 ⊢
    field_simp [hd0]
    unfold cross; simp; ring

lemma hull_polygon_exists {N : ℕ} {r : Fin (N + 1) → ℂ} (hN : 2 ≤ N) (hgp : GenPos r) :
    ∃ (m : ℕ) (hm : 3 ≤ m) (V : Fin m → Fin (N + 1)) (kH kT : Fin (N + 1)),
      kH < kT ∧ V ⟨0, by omega⟩ = kH ∧
      (∃ q : Fin m, 1 ≤ (q : ℕ) ∧ V q = kT) ∧
      Function.Injective V ∧
      (∀ idx : Fin m, IsExtreme r (V idx)) ∧
      (∀ idx : Fin m, kH ≤ V idx ∧ V idx ≤ kT) ∧
      (∀ idx : Fin m, ∀ i : Fin (N + 1),
        0 ≤ cross (r (V ⟨((idx : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩) - r (V idx)) (r i - r (V idx))) ∧
      (∀ a b c : Fin m, a < b → b < c →
        0 < cross (r (V b) - r (V a)) (r (V c) - r (V a))) := by
  classical
  let extSet : Finset (Fin (N + 1)) := Finset.univ.filter (fun k => IsExtreme r k)
  obtain ⟨k_max, hk_max_ext, hk_max_le⟩ := exists_extreme_max_dot hgp (u := 1) one_ne_zero
  obtain ⟨k_min, hk_min_ext, hk_min_le⟩ := exists_extreme_max_dot hgp (u := -1) (neg_ne_zero.mpr one_ne_zero)
  have h12_ne : ∃ a ∈ extSet, ∃ b ∈ extSet, a ≠ b := by
    by_cases h : k_max = k_min
    · obtain ⟨k_top, hk_top_ext, hk_top_le⟩ := exists_extreme_max_dot hgp (u := I) Complex.I_ne_zero
      obtain ⟨k_bot, hk_bot_ext, hk_bot_le⟩ := exists_extreme_max_dot hgp (u := -I) (neg_ne_zero.mpr Complex.I_ne_zero)
      refine ⟨k_top, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_top_ext⟩,
        k_bot, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_bot_ext⟩, ?_⟩
      intro heq
      have hsame_re : ∀ i, (r i).re = (r k_max).re := fun i => by
        have h1 := hk_max_le i
        have h2 := hk_min_le i
        rw [← h] at h2
        unfold dotC at h1 h2; simp at h1 h2; linarith
      have hsame_im : ∀ i, (r i).im = (r k_top).im := fun i => by
        have h1 := hk_top_le i
        have h2 := hk_bot_le i
        rw [← heq] at h2
        unfold dotC at h1 h2; simp at h1 h2; linarith
      have h01 : r ⟨0, by omega⟩ = r ⟨1, by omega⟩ :=
        Complex.ext ((hsame_re _).trans (hsame_re _).symm) ((hsame_im _).trans (hsame_im _).symm)
      exact hgp.1 ⟨0, by omega⟩ ⟨1, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this) h01
    · exact ⟨k_max, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_max_ext⟩,
        k_min, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_min_ext⟩, h⟩
  obtain ⟨e1, he1, e2, he2, he12⟩ := h12_ne
  have hext_ne : extSet.Nonempty := ⟨e1, he1⟩
  let kH : Fin (N + 1) := extSet.min' hext_ne
  let kT : Fin (N + 1) := extSet.max' hext_ne
  have hkH_mem : kH ∈ extSet := Finset.min'_mem extSet hext_ne
  have hkT_mem : kT ∈ extSet := Finset.max'_mem extSet hext_ne
  have hkHT_lt : kH < kT := by
    have hle1 : kH ≤ e1 := Finset.min'_le extSet e1 he1
    have hle2 : e1 ≤ kT := Finset.le_max' extSet e1 he1
    have hle3 : kH ≤ e2 := Finset.min'_le extSet e2 he2
    have hle4 : e2 ≤ kT := Finset.le_max' extSet e2 he2
    rcases eq_or_lt_of_le (hle1.trans hle2) with h | h
    · exfalso
      have he1_eq : e1 = kH := le_antisymm (h ▸ hle2) hle1
      have he2_eq : e2 = kH := le_antisymm (h ▸ hle4) hle3
      exact he12 (he1_eq.trans he2_eq.symm)
    · exact h
  have hex_k3 : ∃ k3 ∈ extSet, k3 ≠ kH ∧ k3 ≠ kT := by
    have hj0_ex : ∃ j0 : Fin (N + 1), j0 ≠ kH ∧ j0 ≠ kT := by
      have hcard : 3 ≤ Fintype.card (Fin (N + 1)) := by simp; omega
      have h2 : ({kH, kT} : Finset (Fin (N + 1))).card ≤ 2 := Finset.card_le_two
      have hlt : ({kH, kT} : Finset (Fin (N + 1))).card < (Finset.univ : Finset (Fin (N + 1))).card := by
        rw [Finset.card_univ]; omega
      obtain ⟨j0, _, hj0_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      exact ⟨j0, fun h => hj0_not (by simp [h]), fun h => hj0_not (by simp [h])⟩
    obtain ⟨j0, hj0H, hj0T⟩ := hj0_ex
    let u := I * (r kT - r kH)
    have hu_ne : u ≠ 0 := mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr (hgp.1 kT kH hkHT_lt.ne'))
    have hcr_ne : cross (r kT - r kH) (r j0 - r kH) ≠ 0 :=
      hgp.2 kH kT j0 hkHT_lt.ne hj0T.symm hj0H.symm
    rcases lt_or_gt_of_ne hcr_ne with hneg | hpos
    · obtain ⟨k3, hk3_ext, hk3_le⟩ := exists_extreme_max_dot hgp (u := -u) (neg_ne_zero.mpr hu_ne)
      refine ⟨k3, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk3_ext⟩, ?_, ?_⟩
      · intro heq
        have h1 := hk3_le j0
        rw [heq] at h1
        have hle0 : dotC (-u) (r j0 - r kH) ≤ 0 := by rw [dotC_sub_right]; linarith
        have hdiff : dotC (-u) (r j0 - r kH) = -cross (r kT - r kH) (r j0 - r kH) := by
          unfold dotC cross u; simp; ring
        linarith
      · intro heq
        have h1 := hk3_le j0
        rw [heq] at h1
        have hle0 : dotC (-u) (r j0 - r kT) ≤ 0 := by rw [dotC_sub_right]; linarith
        have hdiff : dotC (-u) (r j0 - r kT) = -cross (r kT - r kH) (r j0 - r kH) := by
          unfold dotC cross u; simp; ring
        linarith
    · obtain ⟨k3, hk3_ext, hk3_le⟩ := exists_extreme_max_dot hgp (u := u) hu_ne
      refine ⟨k3, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk3_ext⟩, ?_, ?_⟩
      · intro heq
        have h1 := hk3_le j0
        rw [heq] at h1
        have hle0 : dotC u (r j0 - r kH) ≤ 0 := by rw [dotC_sub_right]; linarith
        have hdiff : dotC u (r j0 - r kH) = cross (r kT - r kH) (r j0 - r kH) := by
          unfold dotC cross u; simp; ring
        linarith
      · intro heq
        have h1 := hk3_le j0
        rw [heq] at h1
        have hle0 : dotC u (r j0 - r kT) ≤ 0 := by rw [dotC_sub_right]; linarith
        have hdiff : dotC u (r j0 - r kT) = cross (r kT - r kH) (r j0 - r kH) := by
          unfold dotC cross u; simp; ring
        linarith
  obtain ⟨k3, hk3_mem, hk3H, hk3T⟩ := hex_k3
  let O : ℂ := ((1 / 3 : ℝ) • r kH + (1 / 3 : ℝ) • r kT + (1 / 3 : ℝ) • r k3)
  have hO_dot_neg : ∀ k ∈ extSet, ∀ u : ℂ, (∀ i, i ≠ k → dotC u (r i - r k) < 0) →
      dotC u (O - r k) < 0 := by
    intro k _ u hu
    have hsplit : O - r k = (1 / 3 : ℝ) • (r kH - r k) + (1 / 3 : ℝ) • (r kT - r k) + (1 / 3 : ℝ) • (r k3 - r k) := by
      simp only [O, Complex.real_smul]; push_cast; ring
    have hdot : dotC u (O - r k) =
        (1 / 3) * dotC u (r kH - r k) + (1 / 3) * dotC u (r kT - r k) + (1 / 3) * dotC u (r k3 - r k) := by
      rw [hsplit]; unfold dotC; simp; ring
    rw [hdot]
    have hleH : dotC u (r kH - r k) ≤ 0 := by
      by_cases h : kH = k
      · subst h; simp [dotC]
      · exact (hu kH h).le
    have hleT : dotC u (r kT - r k) ≤ 0 := by
      by_cases h : kT = k
      · subst h; simp [dotC]
      · exact (hu kT h).le
    have hle3 : dotC u (r k3 - r k) ≤ 0 := by
      by_cases h : k3 = k
      · subst h; simp [dotC]
      · exact (hu k3 h).le
    by_cases h : kH = k
    · have hltT : dotC u (r kT - r k) < 0 := hu kT (by rw [← h]; exact hkHT_lt.ne')
      linarith
    · have hltH : dotC u (r kH - r k) < 0 := hu kH h
      linarith
  have hO_ne : ∀ k ∈ extSet, r k - O ≠ 0 := by
    intro k hk h0
    obtain ⟨u, _, hu⟩ := (Finset.mem_filter.mp hk).2
    have hneg := hO_dot_neg k hk u hu
    have : O - r k = 0 := by rw [← neg_sub, h0, neg_zero]
    rw [this] at hneg; simp [dotC] at hneg
  have hO_ray_inj : ∀ k1 ∈ extSet, ∀ k2 ∈ extSet,
      (∃ t : ℝ, 0 < t ∧ r k2 - O = t • (r k1 - O)) → k1 = k2 := by
    intro k1 hk1 k2 hk2 ⟨t, ht, heq⟩
    by_contra hne
    wlog ht1 : t ≤ 1 generalizing k1 k2 t
    · have hgt : 1 < t := not_le.mp ht1
      exact this k2 hk2 k1 hk1 t⁻¹ (inv_pos.mpr ht) (by rw [heq, smul_smul, inv_mul_cancel₀ ht.ne', one_smul])
        (Ne.symm hne) (inv_le_one_of_one_le₀ hgt.le)
    rcases eq_or_lt_of_le ht1 with rfl | hlt
    · simp only [one_smul] at heq
      exact hne (by by_contra h; exact hgp.1 k2 k1 (Ne.symm h) (sub_left_inj.mp heq))
    · exact extreme_not_strict_comb (Finset.mem_filter.mp hk2).2 (hO_dot_neg k2 hk2)
        (Ne.symm hne) (Ne.symm hne) (sub_pos.mpr hlt) le_rfl ht (by ring)
        (by simp only [Complex.real_smul] at heq ⊢; push_cast at heq ⊢; linear_combination heq)
  have hO_pos_dir : ∀ u : ℂ, u ≠ 0 → ∃ k ∈ extSet, 0 < dotC u (r k - O) := by
    intro u hu
    have hsum : dotC u (r kH - O) + dotC u (r kT - O) + dotC u (r k3 - O) = 0 := by
      have h0 : (r kH - O) + (r kT - O) + (r k3 - O) = 0 := by
        simp only [O, Complex.real_smul]; push_cast; ring
      have h1 : dotC u ((r kH - O) + (r kT - O) + (r k3 - O)) = 0 := by rw [h0]; simp [dotC]
      rw [dotC_add_right, dotC_add_right] at h1
      exact h1
    by_contra h
    push Not at h
    have heqH : dotC u (r kH - O) = 0 := by linarith [h kH hkH_mem, h kT hkT_mem, h k3 hk3_mem]
    have heqT : dotC u (r kT - O) = 0 := by linarith [h kH hkH_mem, h kT hkT_mem, h k3 hk3_mem]
    have heq3 : dotC u (r k3 - O) = 0 := by linarith [h kH hkH_mem, h kT hkT_mem, h k3 hk3_mem]
    have hd1 : dotC u (r kT - r kH) = 0 := by
      have : r kT - r kH = (r kT - O) - (r kH - O) := by ring
      rw [this, dotC_sub_right, heqT, heqH, sub_self]
    have hd2 : dotC u (r k3 - r kH) = 0 := by
      have : r k3 - r kH = (r k3 - O) - (r kH - O) := by ring
      rw [this, dotC_sub_right, heq3, heqH, sub_self]
    have hcr0 : cross (r kT - r kH) (r k3 - r kH) = 0 := by
      have hmul : ‖u‖ ^ 2 * cross (r kT - r kH) (r k3 - r kH) = 0 := by
        have hid : (u.re * u.re + u.im * u.im) *
            ((r kT - r kH).re * (r k3 - r kH).im - (r kT - r kH).im * (r k3 - r kH).re) =
            (u.re * (r kT - r kH).re + u.im * (r kT - r kH).im) *
              (u.re * (r k3 - r kH).im - u.im * (r k3 - r kH).re) +
            (u.re * (r k3 - r kH).re + u.im * (r k3 - r kH).im) *
              (u.im * (r kT - r kH).re - u.re * (r kT - r kH).im) := by ring
        unfold dotC at hd1 hd2
        unfold cross
        rw [Complex.sq_norm, Complex.normSq_apply, hid, hd1, hd2]
        ring
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu))
    exact hgp.2 kH kT k3 hkHT_lt.ne hk3T.symm hk3H.symm hcr0
  let θH := Complex.arg (r kH - O)
  let angO (k : Fin (N + 1)) : ℝ := shiftArg (Complex.arg (r k - O) - θH)
  have hangO_inj : Set.InjOn angO (extSet : Set (Fin (N + 1))) := by
    intro k1 hk1 k2 hk2 heq
    have h1_m := Complex.arg_mem_Ioc (r k1 - O)
    have h2_m := Complex.arg_mem_Ioc (r k2 - O)
    have hexp : Complex.exp (((Complex.arg (r k1 - O) - Complex.arg (r k2 - O)) : ℝ) * I) = 1 := by
      have h1 := exp_shiftArg_mul_I (Complex.arg (r k1 - O) - θH)
      have h2 := exp_shiftArg_mul_I (Complex.arg (r k2 - O) - θH)
      have h3 : Complex.exp (((Complex.arg (r k1 - O) - θH) : ℝ) * I) =
          Complex.exp (((Complex.arg (r k2 - O) - θH) : ℝ) * I) := by
        rw [← h1, ← h2]; exact congrArg (fun x : ℝ => Complex.exp ((x : ℂ) * I)) heq
      have h4 := congrArg (· * Complex.exp (-(((Complex.arg (r k2 - O) - θH) : ℝ) * I))) h3
      rw [← Complex.exp_add, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero] at h4
      convert h4 using 2; push_cast; ring
    rw [Complex.exp_eq_one_iff] at hexp
    obtain ⟨z, hz⟩ := hexp
    have hreal : Complex.arg (r k1 - O) - Complex.arg (r k2 - O) = z * (2 * Real.pi) := by
      have := congrArg Complex.im hz; simp at this; linarith
    have hz0 : z = 0 := by
      have hpi := Real.pi_pos
      have h1' : (-1 : ℤ) < z := by exact_mod_cast (by nlinarith [h1_m.1, h2_m.2] : (-1 : ℝ) < (z : ℝ))
      have h2' : z < 1 := by exact_mod_cast (by nlinarith [h1_m.2, h2_m.1] : (z : ℝ) < 1)
      omega
    have harg_eq : Complex.arg (r k1 - O) = Complex.arg (r k2 - O) := by rw [hz0] at hreal; simp at hreal; linarith
    have hsh0 : shiftArg (Complex.arg (r k2 - O) - Complex.arg (r k1 - O)) = 0 := by
      rw [harg_eq, sub_self]; simp [shiftArg]
    exact hO_ray_inj k1 hk1 k2 hk2 ((shiftArg_sub_arg_eq_zero_iff (hO_ne k2 hk2) (hO_ne k1 hk1)).mp hsh0)
  let angImg : Finset ℝ := extSet.image angO
  have hm_eq : angImg.card = extSet.card := Finset.card_image_of_injOn hangO_inj
  let m : ℕ := extSet.card
  have hm3 : 3 ≤ m := by
    have hsub : ({kH, kT, k3} : Finset (Fin (N + 1))) ⊆ extSet := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc : ({kH, kT, k3} : Finset (Fin (N + 1))).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hk3T.symm]
      · simp [hkHT_lt.ne, hk3H.symm]
    exact hc ▸ Finset.card_le_card hsub
  let emb : Fin m ↪o ℝ := angImg.orderEmbOfFin hm_eq
  have hinv : ∀ idx : Fin m, ∃ k ∈ extSet, angO k = emb idx := fun idx =>
    Finset.mem_image.mp (Finset.orderEmbOfFin_mem angImg hm_eq idx)
  choose V hV_mem hV_ang using hinv
  have hV_strict : StrictMono (angO ∘ V) := fun i j hij => by
    simp only [Function.comp_apply, hV_ang]; exact emb.strictMono hij
  have hV_inj : Function.Injective V := fun i j hij => by
    have : angO (V i) = angO (V j) := congrArg angO hij
    rw [hV_ang, hV_ang] at this
    exact emb.injective this
  have hV_surj : ∀ k ∈ extSet, ∃ idx : Fin m, V idx = k := by
    intro k hk
    have hmem : angO k ∈ (angImg : Set ℝ) := Finset.mem_coe.mpr (Finset.mem_image_of_mem angO hk)
    rw [← Finset.range_orderEmbOfFin angImg hm_eq] at hmem
    obtain ⟨idx, hidx⟩ := hmem
    exact ⟨idx, hangO_inj (hV_mem idx) hk ((hV_ang idx).trans hidx)⟩
  have hV0 : V ⟨0, by omega⟩ = kH := by
    obtain ⟨idx, hidx⟩ := hV_surj kH hkH_mem
    have h0 : angO kH = 0 := by simp [angO, θH, shiftArg]
    have hnn : 0 ≤ angO (V ⟨0, by omega⟩) :=
      shiftArg_nonneg (by linarith [(Complex.arg_mem_Ioc (r (V ⟨0, by omega⟩) - O)).1, (Complex.arg_mem_Ioc (r kH - O)).2])
    have hle : angO (V ⟨0, by omega⟩) ≤ angO (V idx) := by
      rcases eq_or_lt_of_le (Nat.zero_le (idx : ℕ)) with h | h
      · have : (⟨0, by omega⟩ : Fin m) = idx := Fin.ext h; rw [this]
      · exact (hV_strict h).le
    rw [hidx, h0] at hle
    exact hangO_inj (hV_mem _) hkH_mem (by linarith)
  have hV_q : ∃ q : Fin m, 1 ≤ (q : ℕ) ∧ V q = kT := by
    obtain ⟨q, hq⟩ := hV_surj kT hkT_mem
    refine ⟨q, ?_, hq⟩
    by_contra h0
    have hq0 : q = ⟨0, by omega⟩ := Fin.ext (by simp; omega)
    rw [hq0, hV0] at hq
    exact hkHT_lt.ne hq
  have hangO_bounds : ∀ k : Fin (N + 1), 0 ≤ angO k ∧ angO k < 2 * Real.pi := fun k =>
    ⟨shiftArg_nonneg (by linarith [(Complex.arg_mem_Ioc (r k - O)).1, (Complex.arg_mem_Ioc (r kH - O)).2]),
     shiftArg_lt (by linarith [(Complex.arg_mem_Ioc (r k - O)).2, (Complex.arg_mem_Ioc (r kH - O)).1])⟩
  have hsh_rel : ∀ k1 ∈ extSet, ∀ k2 ∈ extSet,
      shiftArg (Complex.arg (r k2 - O) - Complex.arg (r k1 - O)) = shiftArg (angO k2 - angO k1) := by
    intro k1 _ k2 _
    have hL_nn : 0 ≤ shiftArg (Complex.arg (r k2 - O) - Complex.arg (r k1 - O)) :=
      shiftArg_nonneg (by linarith [(Complex.arg_mem_Ioc (r k2 - O)).1, (Complex.arg_mem_Ioc (r k1 - O)).2])
    have hL_lt : shiftArg (Complex.arg (r k2 - O) - Complex.arg (r k1 - O)) < 2 * Real.pi :=
      shiftArg_lt (by linarith [(Complex.arg_mem_Ioc (r k2 - O)).2, (Complex.arg_mem_Ioc (r k1 - O)).1])
    have hR_nn : 0 ≤ shiftArg (angO k2 - angO k1) :=
      shiftArg_nonneg (by linarith [(hangO_bounds k2).1, (hangO_bounds k1).2])
    have hR_lt : shiftArg (angO k2 - angO k1) < 2 * Real.pi :=
      shiftArg_lt (by linarith [(hangO_bounds k2).2, (hangO_bounds k1).1])
    have hexp_eq : Complex.exp ((shiftArg (Complex.arg (r k2 - O) - Complex.arg (r k1 - O)) : ℂ) * I) =
        Complex.exp ((shiftArg (angO k2 - angO k1) : ℂ) * I) := by
      rw [exp_shiftArg_mul_I, exp_shiftArg_mul_I, Complex.ofReal_sub, sub_mul, Complex.exp_sub,
        Complex.ofReal_sub, sub_mul, Complex.exp_sub]
      simp only [angO, exp_shiftArg_mul_I]
      rw [← Complex.exp_sub, ← Complex.exp_sub]
      congr 1; push_cast; ring
    have hdiv1 : Complex.exp (((shiftArg (Complex.arg (r k2 - O) - Complex.arg (r k1 - O)) -
        shiftArg (angO k2 - angO k1)) : ℝ) * I) = 1 := by
      rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, hexp_eq, div_self (Complex.exp_ne_zero _)]
    rw [Complex.exp_eq_one_iff] at hdiv1
    obtain ⟨z, hz⟩ := hdiv1
    have hreal : shiftArg (Complex.arg (r k2 - O) - Complex.arg (r k1 - O)) -
        shiftArg (angO k2 - angO k1) = z * (2 * Real.pi) := by
      have := congrArg Complex.im hz; simp at this; linarith
    have hz0 : z = 0 := by
      have hpi := Real.pi_pos
      have h1' : (-1 : ℤ) < z := by exact_mod_cast (by nlinarith : (-1 : ℝ) < (z : ℝ))
      have h2' : z < 1 := by exact_mod_cast (by nlinarith : (z : ℝ) < 1)
      omega
    rw [hz0] at hreal; simp at hreal; linarith
  have hcyc_next : ∀ (idx j : Fin m),
      let nxt : Fin m := ⟨((idx : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩
      j ≠ idx → j ≠ nxt → shiftArg (angO (V nxt) - angO (V idx)) < shiftArg (angO (V j) - angO (V idx)) := by
    intro idx j nxt hj_ne1 hj_ne2
    apply shiftArg_sub_cyclic_lt (by linarith [(hangO_bounds (V nxt)).2, (hangO_bounds (V j)).1])
    by_cases hlast : (idx : ℕ) + 1 < m
    · have hnxt_v : (nxt : ℕ) = (idx : ℕ) + 1 := Nat.mod_eq_of_lt hlast
      rcases lt_or_gt_of_ne hj_ne1 with hlt | hgt
      · exact Or.inr (Or.inr ⟨hV_strict hlt, hV_strict (show idx < nxt by change (idx : ℕ) < (nxt : ℕ); omega)⟩)
      · have hgt2 : nxt < j := by
          change (nxt : ℕ) < (j : ℕ)
          have : (j : ℕ) ≠ (nxt : ℕ) := fun h => hj_ne2 (Fin.ext h)
          change (idx : ℕ) < (j : ℕ) at hgt
          omega
        exact Or.inl ⟨hV_strict (show idx < nxt by change (idx : ℕ) < (nxt : ℕ); omega), hV_strict hgt2⟩
    · have hnxt_v : (nxt : ℕ) = 0 := by
        have : (idx : ℕ) + 1 = m := by omega
        dsimp [nxt]; rw [this, Nat.mod_self]
      have h1' : nxt < j := by
        change (nxt : ℕ) < (j : ℕ)
        have : (j : ℕ) ≠ 0 := fun h => hj_ne2 (Fin.ext (by omega))
        omega
      have h2' : j < idx := by
        change (j : ℕ) < (idx : ℕ)
        have : (j : ℕ) ≠ (idx : ℕ) := fun h => hj_ne1 (Fin.ext h)
        omega
      exact Or.inr (Or.inl ⟨hV_strict h1', hV_strict h2'⟩)
  have hnext_cross : ∀ idx : Fin m,
      0 < cross (r (V idx) - O) (r (V ⟨((idx : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩) - O) := by
    intro idx
    let nxt : Fin m := ⟨((idx : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩
    have hidx_ne : r (V idx) - O ≠ 0 := hO_ne (V idx) (hV_mem idx)
    have hnxt_ne : r (V nxt) - O ≠ 0 := hO_ne (V nxt) (hV_mem nxt)
    obtain ⟨k, hk_mem, hk_pos⟩ := hO_pos_dir (I * (r (V idx) - O)) (mul_ne_zero Complex.I_ne_zero hidx_ne)
    rw [dotC_I_mul] at hk_pos
    obtain ⟨j, rfl⟩ := hV_surj k hk_mem
    have hj_ang := (cross_pos_iff_shiftArg_lt_pi hidx_ne (hO_ne (V j) (hV_mem j))).mp hk_pos
    rw [cross_pos_iff_shiftArg_lt_pi hidx_ne hnxt_ne]
    rw [hsh_rel (V idx) (hV_mem idx) (V j) (hV_mem j)] at hj_ang
    rw [hsh_rel (V idx) (hV_mem idx) (V nxt) (hV_mem nxt)]
    have hne_nxt : idx ≠ nxt := by
      intro h; have := congrArg Fin.val h; dsimp [nxt] at this
      by_cases hlast : (idx : ℕ) + 1 < m
      · rw [Nat.mod_eq_of_lt hlast] at this; omega
      · have h1 : (idx : ℕ) + 1 = m := by omega
        rw [h1, Nat.mod_self] at this; omega
    have hpos_nxt : 0 < shiftArg (angO (V nxt) - angO (V idx)) := by
      have hnn := shiftArg_nonneg (x := angO (V nxt) - angO (V idx))
        (by linarith [(hangO_bounds (V nxt)).1, (hangO_bounds (V idx)).2])
      rcases eq_or_lt_of_le hnn with h0 | hpos
      · exfalso
        rw [← hsh_rel (V idx) (hV_mem idx) (V nxt) (hV_mem nxt)] at h0
        exact hne_nxt (hV_inj (hO_ray_inj (V idx) (hV_mem idx) (V nxt) (hV_mem nxt)
          ((shiftArg_sub_arg_eq_zero_iff hnxt_ne hidx_ne).mp h0.symm)))
      · exact hpos
    refine ⟨hpos_nxt, ?_⟩
    by_cases hj_eq : j = nxt
    · subst hj_eq; exact hj_ang.2
    · have hj_ne_idx : j ≠ idx := by intro h; subst h; rw [cross_self] at hk_pos; linarith
      linarith [hcyc_next idx j hj_ne_idx hj_eq, hj_ang.2]
  have hedge : ∀ idx : Fin m, ∀ i : Fin (N + 1),
      0 ≤ cross (r (V ⟨((idx : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩) - r (V idx)) (r i - r (V idx)) := by
    intro idx
    let nxt : Fin m := ⟨((idx : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩
    have hidx_ne_nxt : idx ≠ nxt := by
      intro h; have := congrArg Fin.val h; dsimp [nxt] at this
      by_cases hlast : (idx : ℕ) + 1 < m
      · rw [Nat.mod_eq_of_lt hlast] at this; omega
      · have h1 : (idx : ℕ) + 1 = m := by omega
        rw [h1, Nat.mod_self] at this; omega
    let u := -I * (r (V nxt) - r (V idx))
    have hu_ne : u ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (sub_ne_zero.mpr (hgp.1 (V nxt) (V idx) (fun h => hidx_ne_nxt (hV_inj h).symm)))
    obtain ⟨k_star, hk_star_ext, hk_star_max⟩ := exists_extreme_max_dot hgp hu_ne
    have hstar_mem : k_star ∈ extSet := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_star_ext⟩
    obtain ⟨j, hj_eq⟩ := hV_surj k_star hstar_mem
    have hstar_nn : 0 ≤ cross (r (V nxt) - r (V idx)) (r k_star - r (V idx)) := by
      by_contra hneg
      push Not at hneg
      have h0 : 0 < cross (r (V idx) - O) (r (V nxt) - O) := hnext_cross idx
      have hsum_id : cross (r (V idx) - O) (r k_star - O) + cross (r k_star - O) (r (V nxt) - O) =
          cross (r (V idx) - O) (r (V nxt) - O) - cross (r (V nxt) - r (V idx)) (r k_star - r (V idx)) := by
        unfold cross; simp; ring
      have hnot_both : ¬ (0 < cross (r (V idx) - O) (r k_star - O) ∧ 0 < cross (r k_star - O) (r (V nxt) - O)) := by
        rintro ⟨hc1, hc2⟩
        have h1 := (cross_pos_iff_shiftArg_lt_pi (hO_ne (V idx) (hV_mem idx)) (hO_ne k_star hstar_mem)).mp hc1
        have h2 := (cross_pos_iff_shiftArg_lt_pi (hO_ne k_star hstar_mem) (hO_ne (V nxt) (hV_mem nxt))).mp hc2
        have h0' := (cross_pos_iff_shiftArg_lt_pi (hO_ne (V idx) (hV_mem idx)) (hO_ne (V nxt) (hV_mem nxt))).mp h0
        have hj_ne1 : j ≠ idx := by intro h; subst h; rw [hj_eq, cross_self] at hc1; linarith
        have hj_ne2 : j ≠ nxt := by intro h; subst h; rw [hj_eq, cross_self] at hc2; linarith
        set a1 := shiftArg (Complex.arg (r k_star - O) - Complex.arg (r (V idx) - O))
        set a2 := shiftArg (Complex.arg (r (V nxt) - O) - Complex.arg (r k_star - O))
        set a3 := shiftArg (Complex.arg (r (V nxt) - O) - Complex.arg (r (V idx) - O))
        have hexp : Complex.exp (((a1 + a2 - a3) : ℝ) * I) = 1 := by
          rw [Complex.ofReal_sub, Complex.ofReal_add, sub_mul, add_mul, Complex.exp_sub, Complex.exp_add]
          simp only [a1, a2, a3, exp_shiftArg_mul_I]
          rw [← Complex.exp_add, ← Complex.exp_sub]
          convert Complex.exp_zero using 2; push_cast; ring
        rw [Complex.exp_eq_one_iff] at hexp
        obtain ⟨z, hz⟩ := hexp
        have hreal : a1 + a2 - a3 = z * (2 * Real.pi) := by
          have := congrArg Complex.im hz; simp at this; linarith
        have hz0 : z = 0 := by
          have hpi := Real.pi_pos
          have ha1_lo : 0 < a1 := h1.1; have ha1_hi : a1 < Real.pi := h1.2
          have ha2_lo : 0 < a2 := h2.1; have ha2_hi : a2 < Real.pi := h2.2
          have ha3_lo : 0 < a3 := h0'.1; have ha3_hi : a3 < Real.pi := h0'.2
          have h1' : (-1 : ℤ) < z := by exact_mod_cast (by nlinarith : (-1 : ℝ) < (z : ℝ))
          have h2' : z < 1 := by exact_mod_cast (by nlinarith : (z : ℝ) < 1)
          omega
        have hsum_a : a1 + a2 = a3 := by rw [hz0] at hreal; simp at hreal; linarith
        have hlt_a : a1 < a3 := by linarith [h2.1]
        have ha1_eq : a1 = shiftArg (angO (V j) - angO (V idx)) := by
          dsimp [a1]; rw [← hj_eq]; exact hsh_rel (V idx) (hV_mem idx) (V j) (hV_mem j)
        have ha3_eq : a3 = shiftArg (angO (V nxt) - angO (V idx)) :=
          hsh_rel (V idx) (hV_mem idx) (V nxt) (hV_mem nxt)
        linarith [hcyc_next idx j hj_ne1 hj_ne2]
      by_cases hc1 : 0 < cross (r (V idx) - O) (r k_star - O)
      · have hc2 : cross (r k_star - O) (r (V nxt) - O) ≤ 0 := by by_contra h; exact hnot_both ⟨hc1, not_le.mp h⟩
        have hne_s : V nxt ≠ k_star := by intro h; rw [← h, cross_self] at hneg; linarith
        have hcomb := cramer_triangle_eq O (r (V nxt)) (r (V idx)) (r k_star) rfl hc1.ne'
        have hcr_swap : cross (r (V nxt) - O) (r k_star - O) = -cross (r k_star - O) (r (V nxt) - O) := cross_antisymm _ _
        have hgam_eq : cross (r (V idx) - O) (r k_star - O) - cross (r (V nxt) - O) (r k_star - O) -
            cross (r (V idx) - O) (r (V nxt) - O) = -cross (r (V nxt) - r (V idx)) (r k_star - r (V idx)) := by
          linarith [hsum_id, hcr_swap]
        exact extreme_not_strict_comb (Finset.mem_filter.mp (hV_mem nxt)).2 (hO_dot_neg (V nxt) (hV_mem nxt))
          (fun h => hidx_ne_nxt (hV_inj h).symm) hne_s
          (div_pos (by linarith) hc1) (div_nonneg (by linarith) hc1.le) (div_pos h0 hc1)
          (by field_simp [hc1.ne']; ring) hcomb
      · have hc1_le : cross (r (V idx) - O) (r k_star - O) ≤ 0 := not_lt.mp hc1
        have hc2 : 0 < cross (r k_star - O) (r (V nxt) - O) := by linarith [hsum_id]
        have hne_s : V idx ≠ k_star := by
          intro h; rw [← h, sub_self] at hneg; unfold cross at hneg; simp at hneg
        have hcomb := cramer_triangle_eq O (r (V idx)) (r k_star) (r (V nxt)) rfl hc2.ne'
        have hcr_swap : cross (r k_star - O) (r (V idx) - O) = -cross (r (V idx) - O) (r k_star - O) := cross_antisymm _ _
        have hgam_eq : cross (r k_star - O) (r (V nxt) - O) - cross (r (V idx) - O) (r (V nxt) - O) -
            cross (r k_star - O) (r (V idx) - O) = -cross (r (V nxt) - r (V idx)) (r k_star - r (V idx)) := by
          linarith [hsum_id, hcr_swap]
        have hcomb_swapped : r (V idx) =
            ((cross (r k_star - O) (r (V nxt) - O) - cross (r (V idx) - O) (r (V nxt) - O) -
                cross (r k_star - O) (r (V idx) - O)) / cross (r k_star - O) (r (V nxt) - O)) • O +
            (cross (r k_star - O) (r (V idx) - O) / cross (r k_star - O) (r (V nxt) - O)) • r (V nxt) +
            (cross (r (V idx) - O) (r (V nxt) - O) / cross (r k_star - O) (r (V nxt) - O)) • r k_star := by
          rw [add_right_comm]; exact hcomb
        exact extreme_not_strict_comb (Finset.mem_filter.mp (hV_mem idx)).2 (hO_dot_neg (V idx) (hV_mem idx))
          (fun h => hidx_ne_nxt (hV_inj h)) hne_s
          (div_pos (by linarith) hc2) (div_nonneg (by linarith [hcr_swap]) hc2.le) (div_pos h0 hc2)
          (by field_simp [hc2.ne']; ring) hcomb_swapped
    intro i
    have hmax := hk_star_max i
    have h1 : dotC u (r i) - dotC u (r (V idx)) = -cross (r (V nxt) - r (V idx)) (r i - r (V idx)) := by
      unfold dotC cross u; simp; ring
    have h2 : dotC u (r k_star) - dotC u (r (V idx)) = -cross (r (V nxt) - r (V idx)) (r k_star - r (V idx)) := by
      unfold dotC cross u; simp; ring
    linarith
  have htriple_pos : ∀ a b c : Fin m, a < b → b < c →
      0 < cross (r (V b) - r (V a)) (r (V c) - r (V a)) := by
    intro a b c hab hbc
    have hne : cross (r (V b) - r (V a)) (r (V c) - r (V a)) ≠ 0 :=
      hgp.2 (V a) (V b) (V c) (fun h => hab.ne (hV_inj h))
        (fun h => hbc.ne (hV_inj h)) (fun h => (hab.trans hbc).ne (hV_inj h))
    by_contra hle
    have hneg : cross (r (V b) - r (V a)) (r (V c) - r (V a)) < 0 :=
      lt_of_le_of_ne (not_lt.mp hle) hne
    set s1 := cross (r (V a) - O) (r (V b) - O)
    set s2 := cross (r (V b) - O) (r (V c) - O)
    set s3 := cross (r (V c) - O) (r (V a) - O)
    have hsum_s : s1 + s2 + s3 = cross (r (V b) - r (V a)) (r (V c) - r (V a)) := by
      dsimp [s1, s2, s3]; unfold cross; simp; ring
    have hab_ang : angO (V a) < angO (V b) := hV_strict hab
    have hbc_ang : angO (V b) < angO (V c) := hV_strict hbc
    have hac_ang : angO (V a) < angO (V c) := hV_strict (hab.trans hbc)
    have hd1 : shiftArg (Complex.arg (r (V b) - O) - Complex.arg (r (V a) - O)) = angO (V b) - angO (V a) := by
      rw [hsh_rel (V a) (hV_mem a) (V b) (hV_mem b)]
      unfold shiftArg; rw [if_pos (by linarith)]
    have hd2 : shiftArg (Complex.arg (r (V c) - O) - Complex.arg (r (V b) - O)) = angO (V c) - angO (V b) := by
      rw [hsh_rel (V b) (hV_mem b) (V c) (hV_mem c)]
      unfold shiftArg; rw [if_pos (by linarith)]
    have hd3 : shiftArg (Complex.arg (r (V a) - O) - Complex.arg (r (V c) - O)) = angO (V a) - angO (V c) + 2 * Real.pi := by
      rw [hsh_rel (V c) (hV_mem c) (V a) (hV_mem a)]
      unfold shiftArg; rw [if_neg (by linarith)]
    have hd1_pos : 0 < angO (V b) - angO (V a) := by linarith
    have hd2_pos : 0 < angO (V c) - angO (V b) := by linarith
    have hd3_pos : 0 < angO (V a) - angO (V c) + 2 * Real.pi := by
      linarith [(hangO_bounds (V a)).1, (hangO_bounds (V c)).2]
    have hcramer : ∀ (k0 k1 k2 : Fin (N + 1)), k0 ∈ extSet → k0 ≠ k1 → k0 ≠ k2 →
        0 < cross (r k1 - O) (r k0 - O) → 0 < cross (r k0 - O) (r k2 - O) →
        cross (r k2 - O) (r k1 - O) < 0 →
        cross (r k1 - O) (r k0 - O) + cross (r k0 - O) (r k2 - O) + cross (r k2 - O) (r k1 - O) < 0 →
        False := by
      intro k0 k1 k2 hk0 h01 h02 hp1 hp2 hn htot
      have hd_pos : 0 < cross (r k1 - O) (r k2 - O) := by
        rw [cross_antisymm]; linarith
      have hcomb := cramer_triangle_eq O (r k0) (r k1) (r k2) rfl hd_pos.ne'
      have hcr1 : cross (r k0 - O) (r k2 - O) > 0 := hp2
      have hcr2 : cross (r k1 - O) (r k0 - O) > 0 := hp1
      have hgam_pos : 0 < cross (r k1 - O) (r k2 - O) - cross (r k0 - O) (r k2 - O) - cross (r k1 - O) (r k0 - O) := by
        rw [cross_antisymm (r k1 - O) (r k2 - O)]; linarith
      exact extreme_not_strict_comb (Finset.mem_filter.mp hk0).2 (hO_dot_neg k0 hk0) h01 h02
        (div_pos hgam_pos hd_pos) (div_nonneg hcr1.le hd_pos.le) (div_pos hcr2 hd_pos)
        (by field_simp [hd_pos.ne']; ring) hcomb
    by_cases h1 : angO (V b) - angO (V a) < Real.pi
    · have hs1 : 0 < s1 := (cross_pos_iff_shiftArg_lt_pi (hO_ne (V a) (hV_mem a)) (hO_ne (V b) (hV_mem b))).mpr
        (by rw [hd1]; exact ⟨hd1_pos, h1⟩)
      by_cases h2 : angO (V c) - angO (V b) < Real.pi
      · have hs2 : 0 < s2 := (cross_pos_iff_shiftArg_lt_pi (hO_ne (V b) (hV_mem b)) (hO_ne (V c) (hV_mem c))).mpr
          (by rw [hd2]; exact ⟨hd2_pos, h2⟩)
        have hs3 : s3 < 0 := by linarith
        exact hcramer (V b) (V a) (V c) (hV_mem b) (fun h => hab.ne (hV_inj h).symm)
          (fun h => hbc.ne (hV_inj h)) hs1 hs2 hs3 (by linarith)
      · have h3 : angO (V a) - angO (V c) + 2 * Real.pi < Real.pi := by linarith
        have hs3 : 0 < s3 := (cross_pos_iff_shiftArg_lt_pi (hO_ne (V c) (hV_mem c)) (hO_ne (V a) (hV_mem a))).mpr
          (by rw [hd3]; exact ⟨hd3_pos, h3⟩)
        have hs2 : s2 < 0 := by linarith
        exact hcramer (V a) (V c) (V b) (hV_mem a) (fun h => (hab.trans hbc).ne (hV_inj h))
          (fun h => hab.ne (hV_inj h)) hs3 hs1 hs2 (by linarith)
    · have h2 : angO (V c) - angO (V b) < Real.pi := by linarith
      have h3 : angO (V a) - angO (V c) + 2 * Real.pi < Real.pi := by linarith
      have hs2 : 0 < s2 := (cross_pos_iff_shiftArg_lt_pi (hO_ne (V b) (hV_mem b)) (hO_ne (V c) (hV_mem c))).mpr
        (by rw [hd2]; exact ⟨hd2_pos, h2⟩)
      have hs3 : 0 < s3 := (cross_pos_iff_shiftArg_lt_pi (hO_ne (V c) (hV_mem c)) (hO_ne (V a) (hV_mem a))).mpr
        (by rw [hd3]; exact ⟨hd3_pos, h3⟩)
      have hs1 : s1 < 0 := by linarith
      exact hcramer (V c) (V b) (V a) (hV_mem c) (fun h => hbc.ne (hV_inj h).symm)
        (fun h => (hab.trans hbc).ne (hV_inj h).symm) hs2 hs3 hs1 (by linarith)
  exact ⟨m, hm3, V, kH, kT, hkHT_lt, hV0, hV_q, hV_inj,
    fun idx => (Finset.mem_filter.mp (hV_mem idx)).2,
    fun idx => ⟨Finset.min'_le extSet (V idx) (hV_mem idx), Finset.le_max' extSet (V idx) (hV_mem idx)⟩,
    hedge, htriple_pos⟩

/- Section 4B: Upper/Lower Hull Chains, Monotonicity, and Two-Pointer Extraction of Cases 1, 2/4, 3 -/

noncomputable def dir (φ : ℝ) : ℂ := Complex.exp ((φ : ℂ) * I)

lemma dir_norm (φ : ℝ) : ‖dir φ‖ = 1 := by
  simp [dir]

lemma dir_ne_zero (φ : ℝ) : dir φ ≠ 0 := Complex.exp_ne_zero _

lemma dir_add (φ ψ : ℝ) : dir (φ + ψ) = dir φ * dir ψ := by
  simp only [dir, Complex.ofReal_add, add_mul, Complex.exp_add]

lemma dir_sub (φ ψ : ℝ) : dir (φ - ψ) = dir φ * dir (-ψ) := by
  rw [← dir_add]; ring_nf

lemma dir_neg (φ : ℝ) : dir (-φ) = starRingEnd ℂ (dir φ) := by
  apply Complex.ext
  · change (Complex.exp (((-φ : ℝ) : ℂ) * I)).re = (Complex.exp ((φ : ℂ) * I)).re
    rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  · change (Complex.exp (((-φ : ℝ) : ℂ) * I)).im = -(Complex.exp ((φ : ℂ) * I)).im
    rw [Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

lemma dir_zero : dir 0 = 1 := by simp [dir]

lemma dir_pi : dir Real.pi = -1 := by
  simp [dir]

lemma dir_re (φ : ℝ) : (dir φ).re = Real.cos φ := by
  simp [dir]

lemma dir_im (φ : ℝ) : (dir φ).im = Real.sin φ := by
  simp [dir]

lemma cross_dir_dir (φ ψ : ℝ) : cross (dir φ) (dir ψ) = Real.sin (ψ - φ) := by
  unfold cross
  rw [dir_re, dir_im, dir_re, dir_im, Real.sin_sub]
  ring

lemma dotC_dir_dir (φ ψ : ℝ) : dotC (dir φ) (dir ψ) = Real.cos (ψ - φ) := by
  unfold dotC
  rw [dir_re, dir_im, dir_re, dir_im, Real.cos_sub]
  ring

lemma cross_rotC (θ : ℝ) (a b : ℂ) : cross (rotC θ a) (rotC θ b) = cross a b := by
  simp only [rotC_apply]
  rw [cross_mul_unit, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

lemma dotC_rotC (θ : ℝ) (a b : ℂ) : dotC (rotC θ a) (rotC θ b) = dotC a b := by
  simp only [rotC_apply]
  unfold dotC
  simp only [mul_re, mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hsc := Real.sin_sq_add_cos_sq θ
  linear_combination (a.re * b.re + a.im * b.im) * hsc

lemma dotC_conj (a b : ℂ) : dotC (starRingEnd ℂ a) (starRingEnd ℂ b) = dotC a b := by
  unfold dotC; simp

lemma dotC_smul_right (u : ℂ) (t : ℝ) (z : ℂ) : dotC u (t • z) = t * dotC u z := by
  unfold dotC; simp; ring

lemma cross_zero_right (a : ℂ) : cross a 0 = 0 := by
  unfold cross; simp

lemma dir_arg_eq_smul (z : ℂ) : z = ‖z‖ • dir (Complex.arg z) := by
  rw [Complex.real_smul]
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

lemma cross_dir_arg_eq {z w : ℂ} (hz : z ≠ 0) :
    cross (dir (Complex.arg z)) w = cross z w / ‖z‖ := by
  have h := dir_arg_eq_smul z
  have h1 : cross z w = ‖z‖ * cross (dir (Complex.arg z)) w := by
    conv_lhs => rw [h]
    exact cross_smul_left _ _ _
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  field_simp [hzn]; linarith

lemma cross_dir_interp (θ₁ θ₂ θ : ℝ) (w : ℂ) :
    Real.sin (θ₂ - θ₁) * cross (dir θ) w =
      Real.sin (θ - θ₁) * cross (dir θ₂) w + Real.sin (θ₂ - θ) * cross (dir θ₁) w := by
  unfold cross
  simp only [dir_re, dir_im]
  have h1 : Real.sin (θ₂ - θ₁) * Real.cos θ =
      Real.sin (θ - θ₁) * Real.cos θ₂ + Real.sin (θ₂ - θ) * Real.cos θ₁ := by
    rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]; ring
  have h2 : Real.sin (θ₂ - θ₁) * Real.sin θ =
      Real.sin (θ - θ₁) * Real.sin θ₂ + Real.sin (θ₂ - θ) * Real.sin θ₁ := by
    rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]; ring
  linear_combination w.im * h1 - w.re * h2

lemma cross_dir_le_of_between {θ₁ θ₂ θ₃ : ℝ} {w : ℂ}
    (h12 : θ₁ < θ₂) (h23 : θ₂ ≤ θ₃) (h13 : θ₃ - θ₁ < Real.pi)
    (hw1 : 0 ≤ cross (dir θ₁) w) (hw2 : cross (dir θ₂) w ≤ 0) :
    cross (dir θ₃) w ≤ 0 := by
  have hid := cross_dir_interp θ₁ θ₃ θ₂ w
  have hs12 : 0 < Real.sin (θ₂ - θ₁) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs13 : 0 < Real.sin (θ₃ - θ₁) := Real.sin_pos_of_pos_of_lt_pi (by linarith) h13
  have hs23 : 0 ≤ Real.sin (θ₃ - θ₂) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  nlinarith

lemma cross_dir_le_of_between_both {θ₁ θ₂ θ : ℝ} {w : ℂ}
    (h12 : θ₁ < θ₂) (hpi : θ₂ - θ₁ < Real.pi) (h1 : θ₁ ≤ θ) (h2 : θ ≤ θ₂)
    (hw1 : cross (dir θ₁) w ≤ 0) (hw2 : cross (dir θ₂) w ≤ 0) :
    cross (dir θ) w ≤ 0 := by
  have hid := cross_dir_interp θ₁ θ₂ θ w
  have hs12 : 0 < Real.sin (θ₂ - θ₁) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hpi
  have hs1 : 0 ≤ Real.sin (θ - θ₁) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs2 : 0 ≤ Real.sin (θ₂ - θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  nlinarith

lemma cross_dir_ge_of_between_both {θ₁ θ₂ θ : ℝ} {w : ℂ}
    (h12 : θ₁ < θ₂) (hpi : θ₂ - θ₁ < Real.pi) (h1 : θ₁ ≤ θ) (h2 : θ ≤ θ₂)
    (hw1 : 0 ≤ cross (dir θ₁) w) (hw2 : 0 ≤ cross (dir θ₂) w) :
    0 ≤ cross (dir θ) w := by
  have hid := cross_dir_interp θ₁ θ₂ θ w
  have hs12 : 0 < Real.sin (θ₂ - θ₁) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hpi
  have hs1 : 0 ≤ Real.sin (θ - θ₁) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs2 : 0 ≤ Real.sin (θ₂ - θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  nlinarith

lemma cross_dir_ge_of_between_left {θ₀ θ₁ θ₂ : ℝ} {w : ℂ}
    (h01 : θ₀ ≤ θ₁) (h12 : θ₁ < θ₂) (h02 : θ₂ - θ₀ < Real.pi)
    (hw1 : 0 ≤ cross (dir θ₁) w) (hw2 : cross (dir θ₂) w ≤ 0) :
    0 ≤ cross (dir θ₀) w := by
  have hid := cross_dir_interp θ₀ θ₂ θ₁ w
  have hs12 : 0 < Real.sin (θ₂ - θ₁) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs02 : 0 < Real.sin (θ₂ - θ₀) := Real.sin_pos_of_pos_of_lt_pi (by linarith) h02
  have hs01 : 0 ≤ Real.sin (θ₁ - θ₀) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  nlinarith

def CoveredUnit {N : ℕ} (r : Fin (N + 1) → ℂ) : Prop :=
  ∃ (θ : ℝ) (v : ℂ), ∀ k : Fin (N + 1), rotC θ (r k) + v ∈ sectorC 1

lemma coveredUnit_of_rot_trans {N : ℕ} {r : Fin (N + 1) → ℂ} (θ0 : ℝ) (c0 : ℂ)
    (h : CoveredUnit (fun k => rotC θ0 (r k) + c0)) : CoveredUnit r := by
  obtain ⟨θ, v, hcov⟩ := h
  refine ⟨θ + θ0, rotC θ c0 + v, fun k => ?_⟩
  have heq : rotC (θ + θ0) (r k) + (rotC θ c0 + v) = rotC θ (rotC θ0 (r k) + c0) + v := by
    simp only [rotC_apply, Complex.ofReal_add, add_mul, Complex.exp_add]; ring
  rw [heq]; exact hcov k

lemma coveredUnit_of_conj {N : ℕ} {r : Fin (N + 1) → ℂ}
    (h : CoveredUnit (fun k => starRingEnd ℂ (r k))) : CoveredUnit r := by
  obtain ⟨θ, v, hcov⟩ := h
  refine ⟨-θ, starRingEnd ℂ v, fun k => ?_⟩
  have h1 := sectorC_conj (hcov k)
  have heq : starRingEnd ℂ (rotC θ (starRingEnd ℂ (r k)) + v) = rotC (-θ) (r k) + starRingEnd ℂ v := by
    simp only [rotC_apply, map_add, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    have hexp : starRingEnd ℂ (Complex.exp ((θ : ℂ) * I)) = Complex.exp (((-θ : ℝ) : ℂ) * I) := by
      simpa [dir] using (dir_neg θ).symm
    rw [hexp]
  rw [← heq]; exact h1

lemma coveredUnit_of_rev {N : ℕ} {r : Fin (N + 1) → ℂ}
    (h : CoveredUnit (fun k => r k.rev)) : CoveredUnit r := by
  obtain ⟨θ, v, hcov⟩ := h
  refine ⟨θ, v, fun k => ?_⟩
  simpa using hcov k.rev

lemma coveredUnit_of_wedge_and_ball {N : ℕ} {r : Fin (N + 1) → ℂ} {U : ℂ} {β : ℝ}
    (hball : ∀ k, ‖r k - U‖ ≤ 1)
    (hbot : ∀ k, 0 ≤ cross (dir β) (r k - U))
    (htop : ∀ k, cross (dir (β + Real.pi / 6)) (r k - U) ≤ 0) :
    CoveredUnit r := by
  let θ := -(β + Real.pi / 12)
  refine ⟨θ, -rotC θ U, fun k => ?_⟩
  have hshift : rotC θ (r k) + -rotC θ U = rotC θ (r k - U) := by
    simp only [map_sub]; ring
  rw [hshift]
  set z := rotC θ (r k - U)
  have hnorm : ‖z‖ ≤ 1 := by
    change ‖rotC θ (r k - U)‖ ≤ 1
    rw [(rotC θ).norm_map]
    exact hball k
  have hbot' : 0 ≤ cross (dir (-(Real.pi / 12))) z := by
    have h1 : rotC θ (dir β) = dir (-(Real.pi / 12)) := by
      simp only [rotC_apply, dir, θ, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [← h1, cross_rotC]
    exact hbot k
  have htop' : cross (dir (Real.pi / 12)) z ≤ 0 := by
    have h1 : rotC θ (dir (β + Real.pi / 6)) = dir (Real.pi / 12) := by
      simp only [rotC_apply, dir, θ, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [← h1, cross_rotC]
    exact htop k
  unfold cross at hbot' htop'
  rw [dir_re, dir_im, Real.cos_neg, Real.sin_neg] at hbot'
  rw [dir_re, dir_im] at htop'
  have hcos_pos : 0 < Real.cos (Real.pi / 12) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have htan : Real.sin (Real.pi / 12) = tan15 * Real.cos (Real.pi / 12) := by
    have h1 := tan_pi_div_twelve
    rw [Real.tan_eq_sin_div_cos] at h1
    exact (div_eq_iff hcos_pos.ne').mp h1
  rw [htan] at hbot' htop'
  refine ⟨hnorm, ?_⟩
  rw [abs_le]
  constructor <;> nlinarith

lemma wedge_has_far_point {N : ℕ} {r : Fin (N + 1) → ℂ} {U : ℂ} {β : ℝ}
    (huncov : ¬ CoveredUnit r)
    (hbot : ∀ k, 0 ≤ cross (dir β) (r k - U))
    (htop : ∀ k, cross (dir (β + Real.pi / 6)) (r k - U) ≤ 0) :
    ∃ k : Fin (N + 1), 1 < ‖r k - U‖ := by
  by_contra h
  push Not at h
  exact huncov (coveredUnit_of_wedge_and_ball h hbot htop)

lemma genPos_of_rot_trans {N : ℕ} {r : Fin (N + 1) → ℂ} (hgp : GenPos r) (θ : ℝ) (c : ℂ) :
    GenPos (fun k => rotC θ (r k) + c) := by
  refine ⟨fun i j hij h => hgp.1 i j hij ((rotC θ).injective (add_right_cancel h)),
    fun i j k hij hjk hik h => hgp.2 i j k hij hjk hik ?_⟩
  have h1 : (rotC θ (r j) + c) - (rotC θ (r i) + c) = rotC θ (r j - r i) := by
    simp only [map_sub]; ring
  have h2 : (rotC θ (r k) + c) - (rotC θ (r i) + c) = rotC θ (r k - r i) := by
    simp only [map_sub]; ring
  rw [h1, h2, cross_rotC] at h
  exact h

lemma genPos_of_conj {N : ℕ} {r : Fin (N + 1) → ℂ} (hgp : GenPos r) :
    GenPos (fun k => starRingEnd ℂ (r k)) := by
  refine ⟨fun i j hij h => hgp.1 i j hij (starRingEnd ℂ |>.injective h),
    fun i j k hij hjk hik h => hgp.2 i j k hij hjk hik ?_⟩
  rw [← map_sub, ← map_sub, cross_conj, neg_eq_zero] at h
  exact h

lemma genPos_of_rev {N : ℕ} {r : Fin (N + 1) → ℂ} (hgp : GenPos r) :
    GenPos (fun k => r k.rev) :=
  ⟨fun i j hij => hgp.1 i.rev j.rev (fun h => hij (Fin.rev_injective h)),
   fun i j k hij hjk hik => hgp.2 i.rev j.rev k.rev
     (fun h => hij (Fin.rev_injective h))
     (fun h => hjk (Fin.rev_injective h))
     (fun h => hik (Fin.rev_injective h))⟩

lemma isSimplePoly_of_rot_trans {N : ℕ} {r : Fin (N + 1) → ℂ} (hsimp : IsSimplePoly r)
    (θ : ℝ) (c : ℂ) : IsSimplePoly (fun k => rotC θ (r k) + c) := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro x ⟨a1, b1, ha1, hb1, hab1, hx1⟩ ⟨a2, b2, ha2, hb2, hab2, hx2⟩
  let y := rotC (-θ) (x - c)
  have hinv : ∀ p q : ℂ, ∀ a b : ℝ, a + b = 1 →
      a • (rotC θ p + c) + b • (rotC θ q + c) = x → a • p + b • q = y := by
    intro p q a b hab hx
    have hx' : rotC θ (a • p + b • q) + c = x := by
      rw [map_add, map_smul, map_smul]
      have hc : (a : ℂ) * c + (b : ℂ) * c = c := by
        have h1 : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
        linear_combination c * h1
      simp only [Complex.real_smul, smul_add] at hx ⊢
      linear_combination hx - hc
    have hsub : rotC θ (a • p + b • q) = x - c := eq_sub_of_add_eq hx'
    calc a • p + b • q = rotC (-θ) (rotC θ (a • p + b • q)) := by
          simp only [rotC_apply, ← mul_assoc, ← Complex.exp_add]
          have : (((-θ : ℝ) : ℂ) * I + (θ : ℂ) * I) = 0 := by push_cast; ring
          rw [this, Complex.exp_zero, one_mul]
      _ = y := by rw [hsub]
  exact Set.disjoint_left.mp (hsimp i j hij)
    ⟨a1, b1, ha1, hb1, hab1, hinv _ _ a1 b1 hab1 hx1⟩
    ⟨a2, b2, ha2, hb2, hab2, hinv _ _ a2 b2 hab2 hx2⟩

lemma isSimplePoly_of_conj {N : ℕ} {r : Fin (N + 1) → ℂ} (hsimp : IsSimplePoly r) :
    IsSimplePoly (fun k => starRingEnd ℂ (r k)) := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro x ⟨a1, b1, ha1, hb1, hab1, hx1⟩ ⟨a2, b2, ha2, hb2, hab2, hx2⟩
  have hinv : ∀ p q : ℂ, ∀ a b : ℝ,
      a • starRingEnd ℂ p + b • starRingEnd ℂ q = x → a • p + b • q = starRingEnd ℂ x := by
    intro p q a b hx
    have := congrArg (starRingEnd ℂ) hx
    simpa [Complex.real_smul] using this
  exact Set.disjoint_left.mp (hsimp i j hij)
    ⟨a1, b1, ha1, hb1, hab1, hinv _ _ a1 b1 hx1⟩
    ⟨a2, b2, ha2, hb2, hab2, hinv _ _ a2 b2 hx2⟩

lemma isSimplePoly_of_rev {N : ℕ} {r : Fin (N + 1) → ℂ} (hsimp : IsSimplePoly r) :
    IsSimplePoly (fun k => r k.rev) := by
  intro i j hij
  dsimp only
  have h1 : i.castSucc.rev = i.rev.succ := by
    apply Fin.ext; simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]; omega
  have h2 : i.succ.rev = i.rev.castSucc := by
    apply Fin.ext; simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]; omega
  have h3 : j.castSucc.rev = j.rev.succ := by
    apply Fin.ext; simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]; omega
  have h4 : j.succ.rev = j.rev.castSucc := by
    apply Fin.ext; simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]; omega
  rw [h1, h2, h3, h4, segment_symm, segment_symm ℝ (r j.rev.succ)]
  have hlt : (j.rev : ℕ) + 1 < (i.rev : ℕ) := by simp only [Fin.val_rev]; omega
  exact (hsimp j.rev i.rev hlt).symm

lemma polyLen_of_rot_trans {N : ℕ} (r : Fin (N + 1) → ℂ) (θ : ℝ) (c : ℂ) :
    polyLen (fun k => rotC θ (r k) + c) = polyLen r := by
  unfold polyLen
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : (rotC θ (r k.succ) + c) - (rotC θ (r k.castSucc) + c) = rotC θ (r k.succ - r k.castSucc) := by
    simp only [map_sub]; ring
  rw [h, (rotC θ).norm_map]

lemma polyLen_of_conj {N : ℕ} (r : Fin (N + 1) → ℂ) :
    polyLen (fun k => starRingEnd ℂ (r k)) = polyLen r := by
  unfold polyLen
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_sub, Complex.norm_conj]

lemma polyLen_of_rev {N : ℕ} (r : Fin (N + 1) → ℂ) :
    polyLen (fun k => r k.rev) = polyLen r := by
  unfold polyLen
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k => ?_
  have h1 : k.succ.rev = k.rev.castSucc := by
    apply Fin.ext; simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega
  have h2 : k.castSucc.rev = k.rev.succ := by
    apply Fin.ext; simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega
  simp only [Fin.revPerm_apply, h1, h2, norm_sub_rev]

lemma dotC_le_convexHull {N : ℕ} {r : Fin (N + 1) → ℂ} {u c : ℂ}
    (h : ∀ i : Fin (N + 1), dotC u (r i - c) ≤ 0) :
    ∀ z ∈ convexHull ℝ (Set.range r), dotC u (z - c) ≤ 0 := by
  have hconv : Convex ℝ {z : ℂ | dotC u (z - c) ≤ 0} := by
    intro x hx y hy a b ha hb hab
    show dotC u ((a • x + b • y) - c) ≤ 0
    have hsplit : (a • x + b • y) - c = a • (x - c) + b • (y - c) := by
      simp only [Complex.real_smul]
      have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
      linear_combination c * hab'
    rw [hsplit]
    have hdot : dotC u (a • (x - c) + b • (y - c)) = a * dotC u (x - c) + b * dotC u (y - c) := by
      unfold dotC; simp; ring
    rw [hdot]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx) (mul_nonpos_of_nonneg_of_nonpos hb hy)
  exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact h i) hconv

/- Normalized two-wedge configuration output by Section 4B -/

structure TwoWedgeBase {N : ℕ} (r : Fin (N + 1) → ℂ) where
  L : ℝ
  u_lo : ℝ
  v_lo : ℝ
  hL : 0 < L
  hu_lo0 : 0 ≤ u_lo
  hu_lo_le : u_lo ≤ Real.pi / 6
  hv_lo0 : 0 ≤ v_lo
  hv_lo_le : v_lo ≤ Real.pi / 6
  hU_bot : ∀ k, 0 ≤ cross (dir (-u_lo)) (r k)
  hU_top : ∀ k, cross (dir (Real.pi / 6 - u_lo)) (r k) ≤ 0
  hV_top : ∀ k, cross (dir (-(Real.pi / 6 - v_lo))) (r k - (L : ℂ)) ≤ 0
  hV_bot : ∀ k, 0 ≤ cross (dir v_lo) (r k - (L : ℂ))

def OnUbot {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r) (k : Fin (N + 1)) (t : ℝ) : Prop :=
  0 ≤ t ∧ r k = t • dir (-W.u_lo)

def OnUtop {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r) (k : Fin (N + 1)) (t : ℝ) : Prop :=
  0 ≤ t ∧ r k = t • dir (Real.pi / 6 - W.u_lo)

def OnVtop {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r) (k : Fin (N + 1)) (t : ℝ) : Prop :=
  0 ≤ t ∧ r k = (W.L : ℂ) - t • dir (-(Real.pi / 6 - W.v_lo))

def OnVbot {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r) (k : Fin (N + 1)) (t : ℝ) : Prop :=
  0 ≤ t ∧ r k = (W.L : ℂ) - t • dir W.v_lo

def IsCase1 {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r) : Prop :=
  W.u_lo = 0 ∧ W.v_lo = 0 ∧
  ∃ (A B C D : Fin (N + 1)) (tA tB tC tD : ℝ),
    A < B ∧ B ≤ C ∧ C < D ∧ tA < tD ∧
    OnUbot W A tA ∧ OnUtop W B tB ∧ OnVtop W C tC ∧ OnUbot W D tD

def IsCase3 {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r) : Prop :=
  ∃ (A B C D E F : Fin (N + 1)) (tA tB tC tD tE tF : ℝ),
    A < B ∧ B < C ∧ C ≤ D ∧ D < E ∧ E < F ∧ tA < tC ∧ tF < tD ∧
    OnUbot W A tA ∧ OnUtop W B tB ∧ OnUbot W C tC ∧
    OnVbot W D tD ∧ OnVtop W E tE ∧ OnVbot W F tF

def IsCase24 {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r) : Prop :=
  ∃ (A B QU QV E F : Fin (N + 1)) (tA tB tQU tQV tE tF : ℝ),
    A < B ∧ B < QU ∧ QU ≤ E ∧ B ≤ QV ∧ QV < E ∧ E < F ∧ tA < tQU ∧ tF < tQV ∧
    OnUbot W A tA ∧ OnUtop W B tB ∧ OnUbot W QU tQU ∧
    OnVtop W QV tQV ∧ OnVbot W E tE ∧ OnVtop W F tF

lemma line_intersect_dir {P Q : ℂ} {φ ψ : ℝ} (hsin : Real.sin (ψ - φ) ≠ 0) :
    ∃ Z : ℂ, cross (dir φ) (Z - P) = 0 ∧ cross (dir ψ) (Z - Q) = 0 := by
  let t : ℝ := cross (Q - P) (dir ψ) / Real.sin (ψ - φ)
  refine ⟨P + t • dir φ, ?_, ?_⟩
  · rw [add_sub_cancel_left, cross_smul_right, cross_self, mul_zero]
  · have h1 : P + t • dir φ - Q = t • dir φ - (Q - P) := by ring
    rw [h1, cross_sub_right, cross_smul_right, cross_dir_dir]
    have hcr2 : cross (dir ψ) (Q - P) = -cross (Q - P) (dir ψ) := cross_antisymm _ _
    have hsn : Real.sin (φ - ψ) = -Real.sin (ψ - φ) := by rw [← Real.sin_neg]; congr 1; ring
    rw [hsn, hcr2]
    dsimp [t]
    field_simp [hsin]
    ring

lemma cross_dir_eq_zero_iff {φ : ℝ} {w : ℂ} :
    cross (dir φ) w = 0 ↔ ∃ t : ℝ, w = t • dir φ := by
  constructor
  · intro h
    refine ⟨dotC (dir φ) w, ?_⟩
    unfold cross at h
    have hsc : (dir φ).re ^ 2 + (dir φ).im ^ 2 = 1 := by
      rw [dir_re, dir_im]; exact Real.cos_sq_add_sin_sq φ
    apply Complex.ext
    · simp only [smul_re, smul_eq_mul]; unfold dotC
      linear_combination -w.re * hsc - (dir φ).im * h
    · simp only [smul_im, smul_eq_mul]; unfold dotC
      linear_combination -w.im * hsc + (dir φ).re * h
  · rintro ⟨t, rfl⟩
    rw [cross_smul_right, cross_self, mul_zero]

lemma wedge_coord_decomp (β : ℝ) (w : ℂ) :
    w = (-2 * cross (dir (β + Real.pi / 6)) w) • dir β +
        (2 * cross (dir β) w) • dir (β + Real.pi / 6) := by
  have hs : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
  have hcr : cross (dir β) (dir (β + Real.pi / 6)) = 1 / 2 := by
    rw [cross_dir_dir, add_sub_cancel_left]; exact hs
  unfold cross at hcr
  apply Complex.ext
  · simp only [add_re, smul_re, smul_eq_mul]; unfold cross
    linear_combination -2 * w.re * hcr
  · simp only [add_im, smul_im, smul_eq_mul]; unfold cross
    linear_combination -2 * w.im * hcr

lemma wedge_u_lo_of_sin_bounds {x : ℝ} (hlo : Real.sin x ≤ 0)
    (hhi : 0 ≤ Real.sin (x + Real.pi / 6)) :
    ∃ u_lo : ℝ, 0 ≤ u_lo ∧ u_lo ≤ Real.pi / 6 ∧ dir (-u_lo) = dir x := by
  have hcos : 0 < Real.cos x := by
    have hadd : Real.sin (x + Real.pi / 6) = Real.sin x * (Real.sqrt 3 / 2) + Real.cos x * (1 / 2) := by
      rw [Real.sin_add, Real.cos_pi_div_six, Real.sin_pi_div_six]
    have hsq3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hnn : 0 ≤ Real.cos x := by nlinarith
    rcases eq_or_lt_of_le hnn with h0 | hpos
    · exfalso
      have hs0 : Real.sin x = 0 := by nlinarith
      have hsq := Real.sin_sq_add_cos_sq x
      rw [← h0, hs0] at hsq; norm_num at hsq
    · exact hpos
  let u_lo := -Complex.arg (dir x)
  have hu_dir : dir (-u_lo) = dir x := by
    dsimp [u_lo]; rw [neg_neg]
    have h1 := dir_arg_eq_smul (dir x)
    rw [dir_norm, one_smul] at h1; exact h1.symm
  have hu0 : 0 ≤ u_lo := by
    have him : (dir x).im ≤ 0 := by rw [dir_im]; exact hlo
    have harg : Complex.arg (dir x) ≤ 0 := by
      rcases lt_or_eq_of_le him with hlt | heq
      · exact (Complex.arg_neg_iff.mpr hlt).le
      · exact (Complex.arg_eq_zero_iff.mpr ⟨by rw [dir_re]; exact hcos.le, heq⟩).le
    dsimp [u_lo]; linarith
  have hu_le : u_lo ≤ Real.pi / 6 := by
    have harg_lo : -(Real.pi / 2) < Complex.arg (dir x) := by
      have h := abs_arg_le_pi_div_two_of_re_nonneg (dir_ne_zero x) (by rw [dir_re]; exact hcos.le)
      rw [abs_le] at h
      rcases eq_or_lt_of_le h.1 with heq | hlt
      · exfalso
        have hc := Complex.cos_arg (dir_ne_zero x)
        rw [← heq, Real.cos_neg, Real.cos_pi_div_two, dir_norm, div_one, dir_re] at hc
        linarith
      · exact hlt
    have hs : 0 ≤ Real.sin (Real.pi / 6 - u_lo) := by
      have h1 : dir (Real.pi / 6 - u_lo) = dir (x + Real.pi / 6) := by
        rw [show Real.pi / 6 - u_lo = -u_lo + Real.pi / 6 by ring, dir_add, hu_dir, ← dir_add]
      have h2 := congrArg Complex.im h1
      rw [dir_im, dir_im] at h2; linarith
    by_contra hgt; push Not at hgt
    have hneg : Real.sin (Real.pi / 6 - u_lo) < 0 := by
      have := Real.sin_pos_of_pos_of_lt_pi (show 0 < u_lo - Real.pi / 6 by linarith)
        (show u_lo - Real.pi / 6 < Real.pi by dsimp [u_lo]; linarith [Real.pi_pos])
      rw [show Real.pi / 6 - u_lo = -(u_lo - Real.pi / 6) by ring, Real.sin_neg]; linarith
    linarith
  exact ⟨u_lo, hu0, hu_le, hu_dir⟩

lemma wedge_v_lo_of_sin_bounds {x : ℝ} (hlo : 0 ≤ Real.sin x)
    (hhi : Real.sin (x - Real.pi / 6) ≤ 0) :
    ∃ v_lo : ℝ, 0 ≤ v_lo ∧ v_lo ≤ Real.pi / 6 ∧ dir v_lo = dir x := by
  have hlo' : Real.sin (-x) ≤ 0 := by rw [Real.sin_neg]; linarith
  have hhi' : 0 ≤ Real.sin (-x + Real.pi / 6) := by
    have : -x + Real.pi / 6 = -(x - Real.pi / 6) := by ring
    rw [this, Real.sin_neg]; linarith
  obtain ⟨v_lo, hv0, hvle, hvdir⟩ := wedge_u_lo_of_sin_bounds hlo' hhi'
  refine ⟨v_lo, hv0, hvle, ?_⟩
  have h1 := congrArg (starRingEnd ℂ) hvdir
  rw [← dir_neg, ← dir_neg, neg_neg, neg_neg] at h1
  exact h1

lemma build_twoWedgeBase_apexes {N : ℕ} {r : Fin (N + 1) → ℂ} (hgp : GenPos r)
    {βU αU βV αV : ℝ}
    (hU_ang : αU = βU + Real.pi / 6) (hV_ang : βV = αV + Real.pi / 6)
    (hδtop : 0 ≤ αU - αV) (hδbot : 0 ≤ βV - βU)
    {kA kB kE kF : Fin (N + 1)} (hAB_ne : kA ≠ kB)
    (hU_bot : ∀ k, 0 ≤ cross (dir βU) (r k - r kA))
    (hU_top : ∀ k, cross (dir αU) (r k - r kB) ≤ 0)
    (hV_top : ∀ k, cross (dir αV) (r k - r kE) ≤ 0)
    (hV_bot : ∀ k, 0 ≤ cross (dir βV) (r k - r kF)) :
    ∃ (pU pV : ℂ),
      cross (dir βU) (pU - r kA) = 0 ∧ cross (dir αU) (pU - r kB) = 0 ∧
      cross (dir αV) (pV - r kE) = 0 ∧ cross (dir βV) (pV - r kF) = 0 ∧
      cross (dir αU) (pV - pU) ≤ 0 ∧ 0 ≤ cross (dir βU) (pV - pU) ∧
      cross (dir αV) (pU - pV) ≤ 0 ∧ 0 ≤ cross (dir βV) (pU - pV) ∧
      pV - pU ≠ 0 := by
  have hsin6 : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
  have hsinU : Real.sin (αU - βU) ≠ 0 := by rw [hU_ang, add_sub_cancel_left, hsin6]; norm_num
  have hsinV : Real.sin (βV - αV) ≠ 0 := by rw [hV_ang, add_sub_cancel_left, hsin6]; norm_num
  obtain ⟨pU, hpU_bot, hpU_top⟩ := line_intersect_dir (P := r kA) (Q := r kB) hsinU
  obtain ⟨pV, hpV_top, hpV_bot⟩ := line_intersect_dir (P := r kE) (Q := r kF) hsinV
  have hU_bot' : ∀ k, 0 ≤ cross (dir βU) (r k - pU) := fun k => by
    have h1 : r k - pU = (r k - r kA) - (pU - r kA) := by ring
    rw [h1, cross_sub_right, hpU_bot, sub_zero]; exact hU_bot k
  have hU_top' : ∀ k, cross (dir αU) (r k - pU) ≤ 0 := fun k => by
    have h1 : r k - pU = (r k - r kB) - (pU - r kB) := by ring
    rw [h1, cross_sub_right, hpU_top, sub_zero]; exact hU_top k
  have hV_top' : ∀ k, cross (dir αV) (r k - pV) ≤ 0 := fun k => by
    have h1 : r k - pV = (r k - r kE) - (pV - r kE) := by ring
    rw [h1, cross_sub_right, hpV_top, sub_zero]; exact hV_top k
  have hV_bot' : ∀ k, 0 ≤ cross (dir βV) (r k - pV) := fun k => by
    have h1 : r k - pV = (r k - r kF) - (pV - r kF) := by ring
    rw [h1, cross_sub_right, hpV_bot, sub_zero]; exact hV_bot k
  have hray_Ubot : ∀ k, cross (dir βU) (r k - r kA) = 0 → ∃ t : ℝ, 0 ≤ t ∧ r k - pU = t • dir βU := by
    intro k hk
    have hcr0 : cross (dir βU) (r k - pU) = 0 := by
      have : r k - pU = (r k - r kA) - (pU - r kA) := by ring
      rw [this, cross_sub_right, hk, hpU_bot, sub_zero]
    have hdec := wedge_coord_decomp βU (r k - pU)
    rw [← hU_ang, hcr0, mul_zero, zero_smul, add_zero] at hdec
    exact ⟨-2 * cross (dir αU) (r k - pU), by linarith [hU_top' k], hdec⟩
  have hray_Utop : ∀ k, cross (dir αU) (r k - r kB) = 0 → ∃ t : ℝ, 0 ≤ t ∧ r k - pU = t • dir αU := by
    intro k hk
    have hcr0 : cross (dir αU) (r k - pU) = 0 := by
      have : r k - pU = (r k - r kB) - (pU - r kB) := by ring
      rw [this, cross_sub_right, hk, hpU_top, sub_zero]
    have hdec := wedge_coord_decomp βU (r k - pU)
    rw [← hU_ang, hcr0, mul_zero, zero_smul, zero_add] at hdec
    exact ⟨2 * cross (dir βU) (r k - pU), by linarith [hU_bot' k], hdec⟩
  have hray_Vtop : ∀ k, cross (dir αV) (r k - r kE) = 0 → ∃ t : ℝ, 0 ≤ t ∧ r k - pV = -(t • dir αV) := by
    intro k hk
    have hcr0 : cross (dir αV) (r k - pV) = 0 := by
      have : r k - pV = (r k - r kE) - (pV - r kE) := by ring
      rw [this, cross_sub_right, hk, hpV_top, sub_zero]
    have hdec := wedge_coord_decomp αV (r k - pV)
    rw [← hV_ang, hcr0, mul_zero, zero_smul, add_zero] at hdec
    refine ⟨2 * cross (dir βV) (r k - pV), by linarith [hV_bot' k], ?_⟩
    conv_lhs => rw [hdec]
    simp only [Complex.real_smul]; push_cast; ring
  have hray_Vbot : ∀ k, cross (dir βV) (r k - r kF) = 0 → ∃ t : ℝ, 0 ≤ t ∧ r k - pV = -(t • dir βV) := by
    intro k hk
    have hcr0 : cross (dir βV) (r k - pV) = 0 := by
      have : r k - pV = (r k - r kF) - (pV - r kF) := by ring
      rw [this, cross_sub_right, hk, hpV_bot, sub_zero]
    have hdec := wedge_coord_decomp αV (r k - pV)
    rw [← hV_ang, hcr0, mul_zero, zero_smul, zero_add] at hdec
    refine ⟨-2 * cross (dir αV) (r k - pV), by linarith [hV_top' k], ?_⟩
    conv_lhs => rw [hdec]
    simp only [Complex.real_smul]; push_cast; ring
  have hδsum : (αU - αV) + (βV - βU) = Real.pi / 3 := by linarith
  have hpV_in_U_top : cross (dir αU) (pV - pU) ≤ 0 := by
    by_cases h0 : αU - αV = 0
    · have hEq : αU = αV := by linarith
      have h1 : cross (dir αU) (pV - pU) = cross (dir αU) (r kE - pU) - cross (dir αV) (r kE - pV) := by
        rw [hEq]; unfold cross; simp; ring
      have hE0 : cross (dir αV) (r kE - pV) = 0 := by
        have : r kE - pV = -(pV - r kE) := by ring
        rw [this, cross_neg_right, hpV_top, neg_zero]
      linarith [hU_top' kE]
    · have hpos : 0 < αU - αV := lt_of_le_of_ne hδtop (Ne.symm h0)
      have hsin_t : 0 < Real.sin (αU - αV) := Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)
      obtain ⟨pT, hpT_U, hpT_V⟩ := line_intersect_dir (P := pU) (Q := pV)
        (show Real.sin (αV - αU) ≠ 0 by rw [show αV - αU = -(αU - αV) by ring, Real.sin_neg]; linarith)
      obtain ⟨tU, htU⟩ := cross_dir_eq_zero_iff.mp hpT_U
      obtain ⟨tV', htV'⟩ := cross_dir_eq_zero_iff.mp hpT_V
      let tV := -tV'
      have hpT_V' : pT - pV = -(tV • dir αV) := by
        rw [htV', Complex.real_smul, Complex.real_smul]; dsimp only [tV]; push_cast; ring
      obtain ⟨tE, htE0, htE⟩ := hray_Vtop kE (by rw [sub_self, cross_zero_right])
      have hcrE : cross (dir αU) (r kE - pT) ≤ 0 := by
        have : r kE - pT = (r kE - pU) - (pT - pU) := by ring
        rw [this, cross_sub_right, hpT_U, sub_zero]; exact hU_top' kE
      have hdiffE : r kE - pT = (tV - tE) • dir αV := by
        have : r kE - pT = (r kE - pV) - (pT - pV) := by ring
        rw [this, htE, hpT_V']; simp only [Complex.real_smul]; push_cast; ring
      rw [hdiffE, cross_smul_right, cross_dir_dir] at hcrE
      have hs_neg : Real.sin (αV - αU) = -Real.sin (αU - αV) := by
        rw [show αV - αU = -(αU - αV) by ring, Real.sin_neg]
      rw [hs_neg] at hcrE
      have htV_nn : 0 ≤ tV := by nlinarith
      have hpVU : pV - pU = tU • dir αU + tV • dir αV := by
        have : pV - pU = (pT - pU) - (pT - pV) := by ring
        rw [this, htU, hpT_V']; ring
      rw [hpVU, cross_add_right, cross_smul_right, cross_self, mul_zero, zero_add,
        cross_smul_right, cross_dir_dir, hs_neg]
      nlinarith
  have hpV_in_U_bot : 0 ≤ cross (dir βU) (pV - pU) := by
    by_cases h0 : βV - βU = 0
    · have hEq : βV = βU := by linarith
      have h1 : cross (dir βU) (pV - pU) = cross (dir βU) (r kF - pU) - cross (dir βV) (r kF - pV) := by
        rw [hEq]; unfold cross; simp; ring
      have hF0 : cross (dir βV) (r kF - pV) = 0 := by
        have : r kF - pV = -(pV - r kF) := by ring
        rw [this, cross_neg_right, hpV_bot, neg_zero]
      linarith [hU_bot' kF]
    · have hpos : 0 < βV - βU := lt_of_le_of_ne hδbot (Ne.symm h0)
      have hsin_b : 0 < Real.sin (βV - βU) := Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)
      obtain ⟨pS, hpS_U, hpS_V⟩ := line_intersect_dir (P := pU) (Q := pV) hsin_b.ne'
      obtain ⟨sU, hsU⟩ := cross_dir_eq_zero_iff.mp hpS_U
      obtain ⟨sV', hsV'⟩ := cross_dir_eq_zero_iff.mp hpS_V
      let sV := -sV'
      have hpS_V' : pS - pV = -(sV • dir βV) := by
        rw [hsV', Complex.real_smul, Complex.real_smul]; dsimp only [sV]; push_cast; ring
      obtain ⟨sF, hsF0, hsF⟩ := hray_Vbot kF (by rw [sub_self, cross_zero_right])
      have hcrF : 0 ≤ cross (dir βU) (r kF - pS) := by
        have : r kF - pS = (r kF - pU) - (pS - pU) := by ring
        rw [this, cross_sub_right, hpS_U, sub_zero]; exact hU_bot' kF
      have hdiffF : r kF - pS = (sV - sF) • dir βV := by
        have : r kF - pS = (r kF - pV) - (pS - pV) := by ring
        rw [this, hsF, hpS_V']; simp only [Complex.real_smul]; push_cast; ring
      rw [hdiffF, cross_smul_right, cross_dir_dir] at hcrF
      have hsV_nn : 0 ≤ sV := by nlinarith
      have hpVU : pV - pU = sU • dir βU + sV • dir βV := by
        have : pV - pU = (pS - pU) - (pS - pV) := by ring
        rw [this, hsU, hpS_V']; ring
      rw [hpVU, cross_add_right, cross_smul_right, cross_self, mul_zero, zero_add,
        cross_smul_right, cross_dir_dir]
      nlinarith
  have hpU_in_V_top : cross (dir αV) (pU - pV) ≤ 0 := by
    by_cases h0 : αU - αV = 0
    · have hEq : αU = αV := by linarith
      have h1 : cross (dir αV) (pU - pV) = cross (dir αV) (r kB - pV) - cross (dir αU) (r kB - pU) := by
        rw [hEq]; unfold cross; simp; ring
      have hB0 : cross (dir αU) (r kB - pU) = 0 := by
        have : r kB - pU = -(pU - r kB) := by ring
        rw [this, cross_neg_right, hpU_top, neg_zero]
      linarith [hV_top' kB]
    · have hpos : 0 < αU - αV := lt_of_le_of_ne hδtop (Ne.symm h0)
      have hsin_t : 0 < Real.sin (αU - αV) := Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)
      obtain ⟨pT, hpT_U, hpT_V⟩ := line_intersect_dir (P := pU) (Q := pV)
        (show Real.sin (αV - αU) ≠ 0 by rw [show αV - αU = -(αU - αV) by ring, Real.sin_neg]; linarith)
      obtain ⟨tU, htU⟩ := cross_dir_eq_zero_iff.mp hpT_U
      obtain ⟨tV', htV'⟩ := cross_dir_eq_zero_iff.mp hpT_V
      obtain ⟨tB, htB0, htB⟩ := hray_Utop kB (by rw [sub_self, cross_zero_right])
      have hcrB : cross (dir αV) (r kB - pT) ≤ 0 := by
        have : r kB - pT = (r kB - pV) - (pT - pV) := by ring
        rw [this, cross_sub_right, hpT_V, sub_zero]; exact hV_top' kB
      have hdiffB : r kB - pT = (tB - tU) • dir αU := by
        have : r kB - pT = (r kB - pU) - (pT - pU) := by ring
        rw [this, htB, htU]; simp only [Complex.real_smul]; push_cast; ring
      rw [hdiffB, cross_smul_right, cross_dir_dir] at hcrB
      have htU_nn : 0 ≤ tU := by nlinarith
      have hpUV : pU - pV = -(tU • dir αU) + tV' • dir αV := by
        have : pU - pV = (pT - pV) - (pT - pU) := by ring
        rw [this, htU, htV']; ring
      rw [hpUV, cross_add_right, cross_neg_right, cross_smul_right, cross_dir_dir,
        cross_smul_right, cross_self, mul_zero, add_zero]
      nlinarith
  have hpU_in_V_bot : 0 ≤ cross (dir βV) (pU - pV) := by
    by_cases h0 : βV - βU = 0
    · have hEq : βV = βU := by linarith
      have h1 : cross (dir βV) (pU - pV) = cross (dir βV) (r kA - pV) - cross (dir βU) (r kA - pU) := by
        rw [hEq]; unfold cross; simp; ring
      have hA0 : cross (dir βU) (r kA - pU) = 0 := by
        have : r kA - pU = -(pU - r kA) := by ring
        rw [this, cross_neg_right, hpU_bot, neg_zero]
      linarith [hV_bot' kA]
    · have hpos : 0 < βV - βU := lt_of_le_of_ne hδbot (Ne.symm h0)
      have hsin_b : 0 < Real.sin (βV - βU) := Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)
      obtain ⟨pS, hpS_U, hpS_V⟩ := line_intersect_dir (P := pU) (Q := pV) hsin_b.ne'
      obtain ⟨sU, hsU⟩ := cross_dir_eq_zero_iff.mp hpS_U
      obtain ⟨sV', hsV'⟩ := cross_dir_eq_zero_iff.mp hpS_V
      obtain ⟨sA, hsA0, hsA⟩ := hray_Ubot kA (by rw [sub_self, cross_zero_right])
      have hcrA : 0 ≤ cross (dir βV) (r kA - pS) := by
        have : r kA - pS = (r kA - pV) - (pS - pV) := by ring
        rw [this, cross_sub_right, hpS_V, sub_zero]; exact hV_bot' kA
      have hdiffA : r kA - pS = (sA - sU) • dir βU := by
        have : r kA - pS = (r kA - pU) - (pS - pU) := by ring
        rw [this, hsA, hsU]; simp only [Complex.real_smul]; push_cast; ring
      rw [hdiffA, cross_smul_right, cross_dir_dir] at hcrA
      have hs_neg : Real.sin (βU - βV) = -Real.sin (βV - βU) := by
        rw [show βU - βV = -(βV - βU) by ring, Real.sin_neg]
      rw [hs_neg] at hcrA
      have hsU_nn : 0 ≤ sU := by nlinarith
      have hpUV : pU - pV = -(sU • dir βU) + sV' • dir βV := by
        have : pU - pV = (pS - pV) - (pS - pU) := by ring
        rw [this, hsU, hsV']; ring
      rw [hpUV, cross_add_right, cross_neg_right, cross_smul_right, cross_dir_dir, hs_neg,
        cross_smul_right, cross_self, mul_zero, add_zero]
      nlinarith
  have hpUV_ne : pV - pU ≠ 0 := by
    intro h0
    have hpEq : pV = pU := sub_eq_zero.mp h0
    have hall : ∀ k, r k = pU := fun k => by
      have h1 := hU_bot' k
      have h2 := hU_top' k
      have h3 : cross (dir αV) (r k - pU) ≤ 0 := hpEq ▸ hV_top' k
      have h4 : 0 ≤ cross (dir βV) (r k - pU) := hpEq ▸ hV_bot' k
      let a := -2 * cross (dir αU) (r k - pU)
      let b := 2 * cross (dir βU) (r k - pU)
      have ha : 0 ≤ a := by dsimp [a]; linarith
      have hb : 0 ≤ b := by dsimp [b]; linarith
      have hdec : r k - pU = a • dir βU + b • dir αU := by
        have := wedge_coord_decomp βU (r k - pU); rwa [← hU_ang] at this
      let c := 2 * cross (dir βV) (r k - pU)
      let d := -2 * cross (dir αV) (r k - pU)
      have hc : 0 ≤ c := by dsimp [c]; linarith
      have hd : 0 ≤ d := by dsimp [d]; linarith
      have hdecV : r k - pU = (-c) • dir αV + (-d) • dir βV := by
        have := wedge_coord_decomp αV (r k - pU)
        rw [← hV_ang] at this
        convert this using 2 <;> (dsimp [c, d]; ring)
      have heq_vec : a • dir βU + b • dir αU + c • dir αV + d • dir βV = 0 := by
        have hnegV : -(r k - pU) = c • dir αV + d • dir βV := by
          rw [hdecV]; simp only [Complex.real_smul]; push_cast; ring
        have hsum : (r k - pU) + (-(r k - pU)) = 0 := by ring
        rw [add_assoc, ← hnegV, ← hdec]; exact hsum
      let mid := βU + Real.pi / 12
      have hdot0 : dotC (dir mid) (a • dir βU + b • dir αU + c • dir αV + d • dir βV) = 0 := by
        rw [heq_vec]; simp [dotC]
      have hexp : dotC (dir mid) (a • dir βU + b • dir αU + c • dir αV + d • dir βV) =
          a * Real.cos (βU - mid) + b * Real.cos (αU - mid) +
          c * Real.cos (αV - mid) + d * Real.cos (βV - mid) := by
        simp only [dotC_add_right, dotC_smul_right, dotC_dir_dir]
      have hc1 : 0 < Real.cos (βU - mid) :=
        Real.cos_pos_of_mem_Ioo ⟨by dsimp [mid]; linarith [Real.pi_pos], by dsimp [mid]; linarith [Real.pi_pos]⟩
      have hc2 : 0 < Real.cos (αU - mid) :=
        Real.cos_pos_of_mem_Ioo ⟨by dsimp [mid]; linarith [Real.pi_pos], by dsimp [mid]; linarith [Real.pi_pos]⟩
      have hc3 : 0 < Real.cos (αV - mid) :=
        Real.cos_pos_of_mem_Ioo ⟨by dsimp [mid]; linarith [Real.pi_pos], by dsimp [mid]; linarith [Real.pi_pos]⟩
      have hc4 : 0 < Real.cos (βV - mid) :=
        Real.cos_pos_of_mem_Ioo ⟨by dsimp [mid]; linarith [Real.pi_pos], by dsimp [mid]; linarith [Real.pi_pos]⟩
      have ha0 : a = 0 := by nlinarith
      have hb0 : b = 0 := by nlinarith
      have : r k - pU = 0 := by rw [hdec, ha0, hb0, zero_smul, zero_smul, add_zero]
      exact sub_eq_zero.mp this
    exact hgp.1 kA kB hAB_ne ((hall kA).trans (hall kB).symm)
  exact ⟨pU, pV, hpU_bot, hpU_top, hpV_top, hpV_bot,
    hpV_in_U_top, hpV_in_U_bot, hpU_in_V_top, hpU_in_V_bot, hpUV_ne⟩

lemma build_twoWedgeBase {N : ℕ} {r : Fin (N + 1) → ℂ}
    (hgp : GenPos r)
    {βU αU βV αV : ℝ}
    (hU_ang : αU = βU + Real.pi / 6) (hV_ang : βV = αV + Real.pi / 6)
    (hδtop : 0 ≤ αU - αV) (hδbot : 0 ≤ βV - βU)
    {kA kB kE kF : Fin (N + 1)} (hAB_ne : kA ≠ kB)
    (hU_bot : ∀ k, 0 ≤ cross (dir βU) (r k - r kA))
    (hU_top : ∀ k, cross (dir αU) (r k - r kB) ≤ 0)
    (hV_top : ∀ k, cross (dir αV) (r k - r kE) ≤ 0)
    (hV_bot : ∀ k, 0 ≤ cross (dir βV) (r k - r kF)) :
    ∃ (θ0 : ℝ) (c0 : ℂ) (W : TwoWedgeBase (fun k => rotC θ0 (r k) + c0)),
      (∀ k, cross (dir βU) (r k - r kA) = 0 → ∃ t, OnUbot W k t ∧ t = ‖(rotC θ0 (r k) + c0)‖) ∧
      (∀ k, cross (dir αU) (r k - r kB) = 0 → ∃ t, OnUtop W k t ∧ t = ‖(rotC θ0 (r k) + c0)‖) ∧
      (∀ k, cross (dir αV) (r k - r kE) = 0 → ∃ t, OnVtop W k t ∧ t = ‖(rotC θ0 (r k) + c0) - (W.L : ℂ)‖) ∧
      (∀ k, cross (dir βV) (r k - r kF) = 0 → ∃ t, OnVbot W k t ∧ t = ‖(rotC θ0 (r k) + c0) - (W.L : ℂ)‖) ∧
      (βU = βV → cross (dir βU) (r kF - r kA) = 0 → W.u_lo = 0 ∧ W.v_lo = 0) := by
  obtain ⟨pU, pV, hpU_bot, hpU_top, hpV_top, hpV_bot,
      hpV_in_U_top, hpV_in_U_bot, hpU_in_V_top, hpU_in_V_bot, hpUV_ne⟩ :=
    build_twoWedgeBase_apexes hgp hU_ang hV_ang hδtop hδbot hAB_ne hU_bot hU_top hV_top hV_bot
  have hU_bot' : ∀ k, 0 ≤ cross (dir βU) (r k - pU) := fun k => by
    have : r k - pU = (r k - r kA) - (pU - r kA) := by ring
    rw [this, cross_sub_right, hpU_bot, sub_zero]; exact hU_bot k
  have hU_top' : ∀ k, cross (dir αU) (r k - pU) ≤ 0 := fun k => by
    have : r k - pU = (r k - r kB) - (pU - r kB) := by ring
    rw [this, cross_sub_right, hpU_top, sub_zero]; exact hU_top k
  have hV_top' : ∀ k, cross (dir αV) (r k - pV) ≤ 0 := fun k => by
    have : r k - pV = (r k - r kE) - (pV - r kE) := by ring
    rw [this, cross_sub_right, hpV_top, sub_zero]; exact hV_top k
  have hV_bot' : ∀ k, 0 ≤ cross (dir βV) (r k - pV) := fun k => by
    have : r k - pV = (r k - r kF) - (pV - r kF) := by ring
    rw [this, cross_sub_right, hpV_bot, sub_zero]; exact hV_bot k
  let φ0 := Complex.arg (pV - pU)
  let θ0 := -φ0
  let c0 := -rotC θ0 pU
  let L := ‖pV - pU‖
  have hL : 0 < L := norm_pos_iff.mpr hpUV_ne
  have hrot_UV : rotC θ0 (pV - pU) = (L : ℂ) := by
    have h1 := dir_arg_eq_smul (pV - pU)
    conv_lhs => rw [h1]
    simp only [rotC_apply, dir, θ0, φ0, Complex.real_smul, L]
    calc Complex.exp (((-Complex.arg (pV - pU) : ℝ) : ℂ) * I) *
            ((‖pV - pU‖ : ℂ) * Complex.exp ((Complex.arg (pV - pU) : ℂ) * I))
        = (‖pV - pU‖ : ℂ) * (Complex.exp (((-Complex.arg (pV - pU) : ℝ) : ℂ) * I) *
            Complex.exp ((Complex.arg (pV - pU) : ℂ) * I)) := by ring
      _ = (‖pV - pU‖ : ℂ) * Complex.exp 0 := by rw [← Complex.exp_add]; congr 2; push_cast; ring
      _ = (‖pV - pU‖ : ℂ) := by rw [Complex.exp_zero, mul_one]
  have hU_vec : rotC θ0 (dir βU) = dir (βU + θ0) := by
    simp only [rotC_apply, dir, ← Complex.exp_add]; congr 1; push_cast; ring
  have hU_top_vec : rotC θ0 (dir αU) = dir (αU + θ0) := by
    simp only [rotC_apply, dir, ← Complex.exp_add]; congr 1; push_cast; ring
  have hV_top_vec : rotC θ0 (dir αV) = dir (αV + θ0) := by
    simp only [rotC_apply, dir, ← Complex.exp_add]; congr 1; push_cast; ring
  have hV_bot_vec : rotC θ0 (dir βV) = dir (βV + θ0) := by
    simp only [rotC_apply, dir, ← Complex.exp_add]; congr 1; push_cast; ring
  have hsin_Ubot : Real.sin (βU + θ0) ≤ 0 := by
    have h1 := hpV_in_U_bot
    rw [← cross_rotC θ0, hU_vec, hrot_UV] at h1
    unfold cross at h1; rw [dir_re, dir_im] at h1; simp at h1
    nlinarith
  have hsin_Utop : 0 ≤ Real.sin (βU + θ0 + Real.pi / 6) := by
    have h1 := hpV_in_U_top
    rw [← cross_rotC θ0, hU_top_vec, hrot_UV, hU_ang] at h1
    unfold cross at h1; rw [dir_re, dir_im] at h1; simp at h1
    have : βU + Real.pi / 6 + θ0 = βU + θ0 + Real.pi / 6 := by ring
    rw [this] at h1; nlinarith
  obtain ⟨u_lo, hu_lo0, hu_lo_le, hu_dir⟩ := wedge_u_lo_of_sin_bounds hsin_Ubot hsin_Utop
  have hrot_VU : rotC θ0 (pU - pV) = -(L : ℂ) := by
    rw [show pU - pV = -(pV - pU) by ring, map_neg, hrot_UV]
  have hsin_Vbot : 0 ≤ Real.sin (βV + θ0) := by
    have h1 := hpU_in_V_bot
    rw [← cross_rotC θ0, hV_bot_vec, hrot_VU] at h1
    unfold cross at h1; rw [dir_re, dir_im] at h1; simp at h1
    nlinarith
  have hsin_Vtop : Real.sin (βV + θ0 - Real.pi / 6) ≤ 0 := by
    have h1 := hpU_in_V_top
    rw [← cross_rotC θ0, hV_top_vec, hrot_VU] at h1
    unfold cross at h1; rw [dir_re, dir_im] at h1; simp at h1
    have : αV + θ0 = βV + θ0 - Real.pi / 6 := by linarith
    rw [this] at h1; nlinarith
  obtain ⟨v_lo, hv_lo0, hv_lo_le, hv_dir⟩ := wedge_v_lo_of_sin_bounds hsin_Vbot hsin_Vtop
  have hU_top_dir : dir (Real.pi / 6 - u_lo) = dir (αU + θ0) := by
    rw [show Real.pi / 6 - u_lo = -u_lo + Real.pi / 6 by ring, dir_add, hu_dir, ← dir_add]
    congr 1; linarith
  have hV_top_dir : dir (-(Real.pi / 6 - v_lo)) = dir (αV + θ0) := by
    rw [show -(Real.pi / 6 - v_lo) = v_lo + -(Real.pi / 6) by ring, dir_add, hv_dir, ← dir_add]
    congr 1; linarith
  have hshift_U : ∀ k, rotC θ0 (r k) + c0 = rotC θ0 (r k - pU) := fun k => by
    simp only [c0, map_sub]; ring
  have hshift_V : ∀ k, (rotC θ0 (r k) + c0) - (L : ℂ) = rotC θ0 (r k - pV) := fun k => by
    rw [hshift_U, ← hrot_UV, ← map_sub]; congr 1; ring
  let W : TwoWedgeBase (fun k => rotC θ0 (r k) + c0) :=
    { L := L, u_lo := u_lo, v_lo := v_lo, hL := hL,
      hu_lo0 := hu_lo0, hu_lo_le := hu_lo_le, hv_lo0 := hv_lo0, hv_lo_le := hv_lo_le,
      hU_bot := fun k => by rw [hshift_U, hu_dir, ← hU_vec, cross_rotC]; exact hU_bot' k,
      hU_top := fun k => by rw [hshift_U, hU_top_dir, ← hU_top_vec, cross_rotC]; exact hU_top' k,
      hV_top := fun k => by rw [hshift_V, hV_top_dir, ← hV_top_vec, cross_rotC]; exact hV_top' k,
      hV_bot := fun k => by rw [hshift_V, hv_dir, ← hV_bot_vec, cross_rotC]; exact hV_bot' k }
  refine ⟨θ0, c0, W, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hcr0 : cross (dir βU) (r k - pU) = 0 := by
      have : r k - pU = (r k - r kA) - (pU - r kA) := by ring
      rw [this, cross_sub_right, hk, hpU_bot, sub_zero]
    have hdec := wedge_coord_decomp βU (r k - pU)
    rw [← hU_ang, hcr0, mul_zero, zero_smul, add_zero] at hdec
    set t := -2 * cross (dir αU) (r k - pU)
    have ht0 : 0 ≤ t := by dsimp [t]; linarith [hU_top' k]
    refine ⟨t, ⟨ht0, ?_⟩, ?_⟩
    · dsimp only; rw [hshift_U, hdec, map_smul, hU_vec, ← hu_dir]
    · rw [hshift_U, hdec, map_smul, hU_vec, ← hu_dir, norm_smul, Real.norm_of_nonneg ht0, dir_norm, mul_one]
  · intro k hk
    have hcr0 : cross (dir αU) (r k - pU) = 0 := by
      have : r k - pU = (r k - r kB) - (pU - r kB) := by ring
      rw [this, cross_sub_right, hk, hpU_top, sub_zero]
    have hdec := wedge_coord_decomp βU (r k - pU)
    rw [← hU_ang, hcr0, mul_zero, zero_smul, zero_add] at hdec
    set t := 2 * cross (dir βU) (r k - pU)
    have ht0 : 0 ≤ t := by dsimp [t]; linarith [hU_bot' k]
    refine ⟨t, ⟨ht0, ?_⟩, ?_⟩
    · dsimp only; rw [hshift_U, hdec, map_smul, hU_top_vec, ← hU_top_dir]
    · rw [hshift_U, hdec, map_smul, hU_top_vec, ← hU_top_dir, norm_smul, Real.norm_of_nonneg ht0, dir_norm, mul_one]
  · intro k hk
    have hcr0 : cross (dir αV) (r k - pV) = 0 := by
      have : r k - pV = (r k - r kE) - (pV - r kE) := by ring
      rw [this, cross_sub_right, hk, hpV_top, sub_zero]
    have hdec := wedge_coord_decomp αV (r k - pV)
    rw [← hV_ang, hcr0, mul_zero, zero_smul, add_zero] at hdec
    set t := 2 * cross (dir βV) (r k - pV)
    have ht0 : 0 ≤ t := by dsimp [t]; linarith [hV_bot' k]
    have ht_eq : r k - pV = -(t • dir αV) := by
      conv_lhs => rw [hdec]
      simp only [t, Complex.real_smul]; push_cast; ring
    refine ⟨t, ⟨ht0, ?_⟩, ?_⟩
    · have h1 := hshift_V k
      rw [ht_eq, map_neg, map_smul, hV_top_vec, ← hV_top_dir] at h1
      dsimp only; exact eq_sub_of_add_eq (by linear_combination h1)
    · rw [hshift_V, ht_eq, map_neg, map_smul, norm_neg, norm_smul, Real.norm_of_nonneg ht0,
        (rotC θ0).norm_map, dir_norm, mul_one]
  · intro k hk
    have hcr0 : cross (dir βV) (r k - pV) = 0 := by
      have : r k - pV = (r k - r kF) - (pV - r kF) := by ring
      rw [this, cross_sub_right, hk, hpV_bot, sub_zero]
    have hdec := wedge_coord_decomp αV (r k - pV)
    rw [← hV_ang, hcr0, mul_zero, zero_smul, zero_add] at hdec
    set t := -2 * cross (dir αV) (r k - pV)
    have ht0 : 0 ≤ t := by dsimp [t]; linarith [hV_top' k]
    have ht_eq : r k - pV = -(t • dir βV) := by
      conv_lhs => rw [hdec]
      simp only [t, Complex.real_smul]; push_cast; ring
    refine ⟨t, ⟨ht0, ?_⟩, ?_⟩
    · have h1 := hshift_V k
      rw [ht_eq, map_neg, map_smul, hV_bot_vec, ← hv_dir] at h1
      dsimp only; exact eq_sub_of_add_eq (by linear_combination h1)
    · rw [hshift_V, ht_eq, map_neg, map_smul, norm_neg, norm_smul, Real.norm_of_nonneg ht0,
        (rotC θ0).norm_map, dir_norm, mul_one]
  · intro hβeq hF_on
    have hpV_bot' : cross (dir βU) (pV - r kF) = 0 := by rw [hβeq]; exact hpV_bot
    have hcr0 : cross (dir βU) (pV - pU) = 0 := by
      have h1 : pV - pU = (pV - r kF) + (r kF - r kA) - (pU - r kA) := by ring
      rw [h1, cross_sub_right, cross_add_right, hpV_bot', hF_on, hpU_bot]; ring
    rw [← cross_rotC θ0, hU_vec, ← hu_dir, hrot_UV] at hcr0
    unfold cross at hcr0; rw [dir_re, dir_im, Real.sin_neg] at hcr0; simp at hcr0
    have hsin0 : Real.sin u_lo = 0 := hcr0.resolve_right hL.ne'
    have hu0 : u_lo = 0 := by
      by_contra hne
      have hpos : 0 < Real.sin u_lo :=
        Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_ne hu_lo0 (Ne.symm hne)) (by linarith [Real.pi_pos])
      linarith
    have hv0 : v_lo = 0 := by
      have hdir_eq : dir v_lo = dir (-u_lo) := by rw [hv_dir, hu_dir, hβeq]
      rw [hu0, neg_zero] at hdir_eq
      have h2 := congrArg Complex.im hdir_eq
      rw [dir_im, dir_im, Real.sin_zero] at h2
      by_contra hne
      have hpos : 0 < Real.sin v_lo :=
        Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_ne hv_lo0 (Ne.symm hne)) (by linarith [Real.pi_pos])
      linarith
    exact ⟨hu0, hv0⟩

lemma solve_raw_two_wedge {N : ℕ} (r0 : Fin (N + 1) → ℂ)
    (hgp0 : GenPos r0) (hsimp0 : IsSimplePoly r0) (hlen0 : polyLen r0 ≤ 1) (huncov0 : ¬ CoveredUnit r0)
    (βU αU βV αV : ℝ)
    (hUang : αU = βU + Real.pi / 6) (hVang : βV = αV + Real.pi / 6)
    (hδt : 0 ≤ αU - αV) (hδb : 0 ≤ βV - βU)
    (kA kB kQ1 : Fin (N + 1)) (hAB : kA < kB) (hBQ1 : kB < kQ1)
    (hUbot : ∀ k, 0 ≤ cross (dir βU) (r0 k - r0 kA))
    (hQ1_on : cross (dir βU) (r0 kQ1 - r0 kA) = 0)
    (hQ1_dir : 0 < dotC (dir βU) (r0 kQ1 - r0 kA))
    (hUtop : ∀ k, cross (dir αU) (r0 k - r0 kB) ≤ 0)
    (hVcases :
      (∃ (kD kE kF : Fin (N + 1)), kD < kE ∧ kE < kF ∧ kB ≤ kE ∧
          (∀ k, 0 ≤ cross (dir βV) (r0 k - r0 kD)) ∧
          cross (dir βV) (r0 kF - r0 kD) = 0 ∧
          0 < dotC (dir βV) (r0 kF - r0 kD) ∧
          (∀ k, cross (dir αV) (r0 k - r0 kE) ≤ 0) ∧
          ((βU = βV ∧ kD = kA ∧ kF = kQ1) ∨ kQ1 ≤ kD)) ∨
      (∃ (kQV kE kF : Fin (N + 1)), kQV < kE ∧ kE < kF ∧ kB ≤ kQV ∧ kQ1 ≤ kE ∧
          (∀ k, cross (dir αV) (r0 k - r0 kQV) ≤ 0) ∧
          cross (dir αV) (r0 kF - r0 kQV) = 0 ∧
          0 < dotC (dir αV) (r0 kF - r0 kQV) ∧
          (∀ k, 0 ≤ cross (dir βV) (r0 k - r0 kE)))) :
    ∃ (r' : Fin (N + 1) → ℂ) (W : TwoWedgeBase r'),
      GenPos r' ∧ IsSimplePoly r' ∧ polyLen r' ≤ 1 ∧ ¬ CoveredUnit r' ∧
      (IsCase1 W ∨ IsCase3 W ∨ IsCase24 W) := by
  have hcr_AQ1 : 0 < cross (r0 kQ1 - r0 kA) (r0 kB - r0 kA) := by
    obtain ⟨s, hs⟩ := cross_dir_eq_zero_iff.mp hQ1_on
    have hs_pos : 0 < s := by
      have h1 := hQ1_dir
      rw [hs, dotC_smul_right, dotC_dir_dir, sub_self, Real.cos_zero, mul_one] at h1; exact h1
    rw [hs, cross_smul_left]
    have hne : cross (r0 kQ1 - r0 kA) (r0 kB - r0 kA) ≠ 0 :=
      hgp0.2 kA kQ1 kB (hAB.trans hBQ1).ne hBQ1.ne' hAB.ne
    rw [hs, cross_smul_left] at hne
    have hposB : 0 < cross (dir βU) (r0 kB - r0 kA) :=
      lt_of_le_of_ne (hUbot kB) (fun h => hne (by rw [← h, mul_zero]))
    exact mul_pos hs_pos hposB
  rcases hVcases with ⟨kD, kE, kF, hDE, hEF, hBE, hVbot, hF_on, hF_dir, hVtop, h13⟩ |
                      ⟨kQV, kE, kF, hQVE, hEF, hBQV, hQ1E, hVtop, hF_on, hF_dir, hVbot⟩
  · have hVbotF : ∀ k, 0 ≤ cross (dir βV) (r0 k - r0 kF) := fun k => by
      have h1 : r0 k - r0 kF = (r0 k - r0 kD) - (r0 kF - r0 kD) := by ring
      rw [h1, cross_sub_right, hF_on, sub_zero]; exact hVbot k
    obtain ⟨θ0, c0, W, hOnUb, hOnUt, hOnVt, hOnVb, hSameLine⟩ :=
      build_twoWedgeBase hgp0 hUang hVang hδt hδb hAB.ne hUbot hUtop hVtop hVbotF
    let r' : Fin (N + 1) → ℂ := fun k => rotC θ0 (r0 k) + c0
    obtain ⟨tA, htA, _⟩ := hOnUb kA (by rw [sub_self, cross_zero_right])
    obtain ⟨tB, htB, _⟩ := hOnUt kB (by rw [sub_self, cross_zero_right])
    obtain ⟨tQ1, htQ1, _⟩ := hOnUb kQ1 hQ1_on
    obtain ⟨tD, htD, _⟩ := hOnVb kD (by
      have h1 : r0 kD - r0 kF = -(r0 kF - r0 kD) := by ring
      rw [h1, cross_neg_right, hF_on, neg_zero])
    obtain ⟨tE, htE, _⟩ := hOnVt kE (by rw [sub_self, cross_zero_right])
    obtain ⟨tF, htF, _⟩ := hOnVb kF (by rw [sub_self, cross_zero_right])
    have htAQ1 : tA < tQ1 := by
      have hdiff : r' kQ1 - r' kA = (tQ1 - tA) • dir (-W.u_lo) := by
        rw [show r' kQ1 = tQ1 • dir (-W.u_lo) from htQ1.2, show r' kA = tA • dir (-W.u_lo) from htA.2]
        simp only [Complex.real_smul]; push_cast; ring
      have hcr_eq : cross (r' kQ1 - r' kA) (r' kB - r' kA) = cross (r0 kQ1 - r0 kA) (r0 kB - r0 kA) := by
        rw [show r' kQ1 - r' kA = rotC θ0 (r0 kQ1 - r0 kA) by simp only [r', map_sub]; ring,
          show r' kB - r' kA = rotC θ0 (r0 kB - r0 kA) by simp only [r', map_sub]; ring, cross_rotC]
      rw [hdiff, cross_smul_left] at hcr_eq
      have hcrB_eq : cross (dir (-W.u_lo)) (r' kB - r' kA) = cross (dir (-W.u_lo)) (r' kB) := by
        rw [cross_sub_right, show r' kA = tA • dir (-W.u_lo) from htA.2, cross_smul_right, cross_self, mul_zero, sub_zero]
      rw [hcrB_eq] at hcr_eq
      have hnn := W.hU_bot kB
      nlinarith
    have htFD : tF < tD := by
      have hdiff : r' kF - r' kD = (tD - tF) • dir W.v_lo := by
        rw [show r' kF = (W.L : ℂ) - tF • dir W.v_lo from htF.2, show r' kD = (W.L : ℂ) - tD • dir W.v_lo from htD.2]
        simp only [Complex.real_smul]; push_cast; ring
      have hcr_pos : 0 < cross (r0 kF - r0 kD) (r0 kE - r0 kD) := by
        obtain ⟨s, hs⟩ := cross_dir_eq_zero_iff.mp hF_on
        have hs_pos : 0 < s := by
          have h1 := hF_dir
          rw [hs, dotC_smul_right, dotC_dir_dir, sub_self, Real.cos_zero, mul_one] at h1; exact h1
        rw [hs, cross_smul_left]
        have hne : cross (r0 kF - r0 kD) (r0 kE - r0 kD) ≠ 0 :=
          hgp0.2 kD kF kE (hDE.trans hEF).ne hEF.ne' hDE.ne
        rw [hs, cross_smul_left] at hne
        have hposE : 0 < cross (dir βV) (r0 kE - r0 kD) :=
          lt_of_le_of_ne (hVbot kE) (fun h => hne (by rw [← h, mul_zero]))
        exact mul_pos hs_pos hposE
      have hcr_eq : cross (r' kF - r' kD) (r' kE - r' kD) = cross (r0 kF - r0 kD) (r0 kE - r0 kD) := by
        rw [show r' kF - r' kD = rotC θ0 (r0 kF - r0 kD) by simp only [r', map_sub]; ring,
          show r' kE - r' kD = rotC θ0 (r0 kE - r0 kD) by simp only [r', map_sub]; ring, cross_rotC]
      rw [hdiff, cross_smul_left] at hcr_eq
      have hcrE_eq : cross (dir W.v_lo) (r' kE - r' kD) = cross (dir W.v_lo) (r' kE - (W.L : ℂ)) := by
        have : r' kE - r' kD = (r' kE - (W.L : ℂ)) + tD • dir W.v_lo := by
          rw [show r' kD = (W.L : ℂ) - tD • dir W.v_lo from htD.2]; ring
        rw [this, cross_add_right, cross_smul_right, cross_self, mul_zero, add_zero]
      rw [hcrE_eq] at hcr_eq
      have hnn := W.hV_bot kE
      nlinarith
    refine ⟨r', W, genPos_of_rot_trans hgp0 _ _, isSimplePoly_of_rot_trans hsimp0 _ _,
      by rw [polyLen_of_rot_trans]; exact hlen0, fun h => huncov0 (coveredUnit_of_rot_trans _ _ h), ?_⟩
    rcases h13 with ⟨hβeq, hDA, hFQ1⟩ | hQ1D
    · left
      obtain ⟨hu0, hv0⟩ := hSameLine hβeq (by rw [hFQ1]; exact hQ1_on)
      exact ⟨hu0, hv0, kA, kB, kE, kQ1, tA, tB, tE, tQ1, hAB, hBE, hFQ1 ▸ hEF, htAQ1, htA, htB, htE, htQ1⟩
    · right; left
      exact ⟨kA, kB, kQ1, kD, kE, kF, tA, tB, tQ1, tD, tE, tF, hAB, hBQ1, hQ1D, hDE, hEF,
        htAQ1, htFD, htA, htB, htQ1, htD, htE, htF⟩
  · have hVtopF : ∀ k, cross (dir αV) (r0 k - r0 kF) ≤ 0 := fun k => by
      have h1 : r0 k - r0 kF = (r0 k - r0 kQV) - (r0 kF - r0 kQV) := by ring
      rw [h1, cross_sub_right, hF_on, sub_zero]; exact hVtop k
    obtain ⟨θ0, c0, W, hOnUb, hOnUt, hOnVt, hOnVb, _⟩ :=
      build_twoWedgeBase hgp0 hUang hVang hδt hδb hAB.ne hUbot hUtop hVtopF hVbot
    let r' : Fin (N + 1) → ℂ := fun k => rotC θ0 (r0 k) + c0
    obtain ⟨tA, htA, _⟩ := hOnUb kA (by rw [sub_self, cross_zero_right])
    obtain ⟨tB, htB, _⟩ := hOnUt kB (by rw [sub_self, cross_zero_right])
    obtain ⟨tQ1, htQ1, _⟩ := hOnUb kQ1 hQ1_on
    obtain ⟨tQV, htQV, _⟩ := hOnVt kQV (by
      have h1 : r0 kQV - r0 kF = -(r0 kF - r0 kQV) := by ring
      rw [h1, cross_neg_right, hF_on, neg_zero])
    obtain ⟨tE, htE, _⟩ := hOnVb kE (by rw [sub_self, cross_zero_right])
    obtain ⟨tF, htF, _⟩ := hOnVt kF (by rw [sub_self, cross_zero_right])
    have htAQ1 : tA < tQ1 := by
      have hdiff : r' kQ1 - r' kA = (tQ1 - tA) • dir (-W.u_lo) := by
        rw [show r' kQ1 = tQ1 • dir (-W.u_lo) from htQ1.2, show r' kA = tA • dir (-W.u_lo) from htA.2]
        simp only [Complex.real_smul]; push_cast; ring
      have hcr_eq : cross (r' kQ1 - r' kA) (r' kB - r' kA) = cross (r0 kQ1 - r0 kA) (r0 kB - r0 kA) := by
        rw [show r' kQ1 - r' kA = rotC θ0 (r0 kQ1 - r0 kA) by simp only [r', map_sub]; ring,
          show r' kB - r' kA = rotC θ0 (r0 kB - r0 kA) by simp only [r', map_sub]; ring, cross_rotC]
      rw [hdiff, cross_smul_left] at hcr_eq
      have hcrB_eq : cross (dir (-W.u_lo)) (r' kB - r' kA) = cross (dir (-W.u_lo)) (r' kB) := by
        rw [cross_sub_right, show r' kA = tA • dir (-W.u_lo) from htA.2, cross_smul_right, cross_self, mul_zero, sub_zero]
      rw [hcrB_eq] at hcr_eq
      have hnn := W.hU_bot kB
      nlinarith
    have htFQV : tF < tQV := by
      have hdiff : r' kF - r' kQV = (tQV - tF) • dir (-(Real.pi / 6 - W.v_lo)) := by
        rw [show r' kF = (W.L : ℂ) - tF • dir (-(Real.pi / 6 - W.v_lo)) from htF.2,
          show r' kQV = (W.L : ℂ) - tQV • dir (-(Real.pi / 6 - W.v_lo)) from htQV.2]
        simp only [Complex.real_smul]; push_cast; ring
      have hcr_neg : cross (r0 kF - r0 kQV) (r0 kE - r0 kQV) < 0 := by
        obtain ⟨s, hs⟩ := cross_dir_eq_zero_iff.mp hF_on
        have hs_pos : 0 < s := by
          have h1 := hF_dir
          rw [hs, dotC_smul_right, dotC_dir_dir, sub_self, Real.cos_zero, mul_one] at h1; exact h1
        rw [hs, cross_smul_left]
        have hne : cross (r0 kF - r0 kQV) (r0 kE - r0 kQV) ≠ 0 :=
          hgp0.2 kQV kF kE (hQVE.trans hEF).ne hEF.ne' hQVE.ne
        rw [hs, cross_smul_left] at hne
        have hnegE : cross (dir αV) (r0 kE - r0 kQV) < 0 :=
          lt_of_le_of_ne (hVtop kE) (fun h => hne (by rw [h, mul_zero]))
        exact mul_neg_of_pos_of_neg hs_pos hnegE
      have hcr_eq : cross (r' kF - r' kQV) (r' kE - r' kQV) = cross (r0 kF - r0 kQV) (r0 kE - r0 kQV) := by
        rw [show r' kF - r' kQV = rotC θ0 (r0 kF - r0 kQV) by simp only [r', map_sub]; ring,
          show r' kE - r' kQV = rotC θ0 (r0 kE - r0 kQV) by simp only [r', map_sub]; ring, cross_rotC]
      rw [hdiff, cross_smul_left] at hcr_eq
      have hcrE_eq : cross (dir (-(Real.pi / 6 - W.v_lo))) (r' kE - r' kQV) =
          cross (dir (-(Real.pi / 6 - W.v_lo))) (r' kE - (W.L : ℂ)) := by
        have : r' kE - r' kQV = (r' kE - (W.L : ℂ)) + tQV • dir (-(Real.pi / 6 - W.v_lo)) := by
          rw [show r' kQV = (W.L : ℂ) - tQV • dir (-(Real.pi / 6 - W.v_lo)) from htQV.2]; ring
        rw [this, cross_add_right, cross_smul_right, cross_self, mul_zero, add_zero]
      rw [hcrE_eq] at hcr_eq
      have hnp := W.hV_top kE
      nlinarith
    refine ⟨r', W, genPos_of_rot_trans hgp0 _ _, isSimplePoly_of_rot_trans hsimp0 _ _,
      by rw [polyLen_of_rot_trans]; exact hlen0, fun h => huncov0 (coveredUnit_of_rot_trans _ _ h), ?_⟩
    right; right
    exact ⟨kA, kB, kQ1, kQV, kE, kF, tA, tB, tQ1, tQV, tE, tF, hAB, hBQ1, hQ1E, hBQV, hQVE, hEF,
      htAQ1, htFQV, htA, htB, htQ1, htQV, htE, htF⟩

structure HullMonoData {N : ℕ} (r1 : Fin (N + 1) → ℂ) where
  pN : ℕ
  qN : ℕ
  hpN1 : 1 ≤ pN
  hqN1 : 1 ≤ qN
  hsum3 : 3 ≤ pN + qN
  kH : Fin (N + 1)
  kT : Fin (N + 1)
  hr1_H : r1 kH = 0
  hr1_T_re : 0 < (r1 kT).re
  hr1_T_im : (r1 kT).im = 0
  U : Fin (pN + 1) → Fin (N + 1)
  L : Fin (qN + 1) → Fin (N + 1)
  hU0 : U ⟨0, by omega⟩ = kH
  hUp : U ⟨pN, by omega⟩ = kT
  hL0 : L ⟨0, by omega⟩ = kH
  hLq : L ⟨qN, by omega⟩ = kT
  hU_im_pos : ∀ i : Fin (pN + 1), 0 < (i : ℕ) → (i : ℕ) < pN → 0 < (r1 (U i)).im
  hL_im_neg : ∀ j : Fin (qN + 1), 0 < (j : ℕ) → (j : ℕ) < qN → (r1 (L j)).im < 0
  hUL_ne : ∀ (i : Fin (pN + 1)) (j : Fin (qN + 1)),
    0 < (i : ℕ) → (i : ℕ) < pN → 0 < (j : ℕ) → (j : ℕ) < qN → U i ≠ L j
  hU_mono : StrictMono U
  hL_mono : StrictMono L
  heU_sup : ∀ (i : Fin pN) (k : Fin (N + 1)),
    cross (r1 (U i.succ) - r1 (U i.castSucc)) (r1 k - r1 (U i.castSucc)) ≤ 0
  heL_sup : ∀ (j : Fin qN) (k : Fin (N + 1)),
    0 ≤ cross (r1 (L j.succ) - r1 (L j.castSucc)) (r1 k - r1 (L j.castSucc))
  heU_turn : ∀ (i : ℕ) (hi : i + 1 < pN),
    cross (r1 (U (⟨i, by omega⟩ : Fin pN).succ) - r1 (U (⟨i, by omega⟩ : Fin pN).castSucc))
      (r1 (U (⟨i + 1, hi⟩ : Fin pN).succ) - r1 (U (⟨i + 1, hi⟩ : Fin pN).castSucc)) < 0
  heL_turn : ∀ (j : ℕ) (hj : j + 1 < qN),
    0 < cross (r1 (L (⟨j, by omega⟩ : Fin qN).succ) - r1 (L (⟨j, by omega⟩ : Fin qN).castSucc))
      (r1 (L (⟨j + 1, hj⟩ : Fin qN).succ) - r1 (L (⟨j + 1, hj⟩ : Fin qN).castSucc))
  hcrH : 0 < cross (r1 (L (⟨0, by omega⟩ : Fin qN).succ) - r1 (L (⟨0, by omega⟩ : Fin qN).castSucc))
    (r1 (U (⟨0, by omega⟩ : Fin pN).succ) - r1 (U (⟨0, by omega⟩ : Fin pN).castSucc))
  hcrT : 0 < cross (r1 (U (⟨pN - 1, by omega⟩ : Fin pN).succ) - r1 (U (⟨pN - 1, by omega⟩ : Fin pN).castSucc))
    (r1 (L (⟨qN - 1, by omega⟩ : Fin qN).succ) - r1 (L (⟨qN - 1, by omega⟩ : Fin qN).castSucc))

structure HullAlignedData {N : ℕ} (r1 : Fin (N + 1) → ℂ) where
  m : ℕ
  hm3 : 3 ≤ m
  V : Fin m → Fin (N + 1)
  kH : Fin (N + 1)
  kT : Fin (N + 1)
  q : Fin m
  hq1 : 1 ≤ (q : ℕ)
  hV0 : V ⟨0, by omega⟩ = kH
  hVq : V q = kT
  hV_inj : Function.Injective V
  hV_range : ∀ idx : Fin m, kH ≤ V idx ∧ V idx ≤ kT
  hr1_H : r1 kH = 0
  hr1_T_re : 0 < (r1 kT).re
  hr1_T_im : (r1 kT).im = 0
  hedge1 : ∀ idx : Fin m, ∀ i : Fin (N + 1),
    0 ≤ cross (r1 (V ⟨((idx : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩) - r1 (V idx)) (r1 i - r1 (V idx))
  htriple1 : ∀ a b c : Fin m, a < b → b < c →
    0 < cross (r1 (V b) - r1 (V a)) (r1 (V c) - r1 (V a))
  hull_no_cross : ∀ (a b c d : Fin m), a < b → b < c → c < d →
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - s) * (V a : ℝ) + s * (V c : ℝ) ≠ (1 - t) * (V b : ℝ) + t * (V d : ℝ)) → False

lemma extract_hull_aligned {N : ℕ} {r : Fin (N + 1) → ℂ} (hN : 2 ≤ N)
    (hgp : GenPos r) (hsimp : IsSimplePoly r) (hlen : polyLen r ≤ 1) (huncov : ¬ CoveredUnit r) :
    ∃ (r1 : Fin (N + 1) → ℂ),
      GenPos r1 ∧ IsSimplePoly r1 ∧ polyLen r1 ≤ 1 ∧ ¬ CoveredUnit r1 ∧ Nonempty (HullAlignedData r1) := by
  obtain ⟨m, hm3, V, kH, kT, hkHT_lt, hV0, ⟨q, hq1, hVq⟩, hV_inj, hV_ext, hV_range, hedge, htriple⟩ :=
    hull_polygon_exists hN hgp
  have hHT_ne : r kT - r kH ≠ 0 := sub_ne_zero.mpr (hgp.1 kT kH hkHT_lt.ne')
  let φHT := Complex.arg (r kT - r kH)
  let r1 : Fin (N + 1) → ℂ := fun k => rotC (-φHT) (r k) + (-rotC (-φHT) (r kH))
  have hr1_eq : ∀ k, r1 k = rotC (-φHT) (r k - r kH) := fun k => by
    simp only [r1, map_sub]; ring
  have hgp1 : GenPos r1 := genPos_of_rot_trans hgp (-φHT) (-rotC (-φHT) (r kH))
  have hsimp1 : IsSimplePoly r1 := isSimplePoly_of_rot_trans hsimp (-φHT) (-rotC (-φHT) (r kH))
  have hlen1 : polyLen r1 ≤ 1 := by rw [polyLen_of_rot_trans]; exact hlen
  have huncov1 : ¬ CoveredUnit r1 := fun h => huncov (coveredUnit_of_rot_trans _ _ h)
  have hr1_H : r1 kH = 0 := by rw [hr1_eq, sub_self, map_zero]
  have hr1_T : r1 kT = (‖r kT - r kH‖ : ℂ) := by
    rw [hr1_eq]
    have h1 := dir_arg_eq_smul (r kT - r kH)
    conv_lhs => rw [h1]
    simp only [rotC_apply, dir, φHT, Complex.real_smul]
    calc Complex.exp (((-Complex.arg (r kT - r kH) : ℝ) : ℂ) * I) *
            ((‖r kT - r kH‖ : ℂ) * Complex.exp ((Complex.arg (r kT - r kH) : ℂ) * I))
        = (‖r kT - r kH‖ : ℂ) * (Complex.exp (((-Complex.arg (r kT - r kH) : ℝ) : ℂ) * I) *
            Complex.exp ((Complex.arg (r kT - r kH) : ℂ) * I)) := by ring
      _ = (‖r kT - r kH‖ : ℂ) * Complex.exp 0 := by rw [← Complex.exp_add]; congr 2; push_cast; ring
      _ = (‖r kT - r kH‖ : ℂ) := by rw [Complex.exp_zero, mul_one]
  have hr1_T_re : 0 < (r1 kT).re := by rw [hr1_T, Complex.ofReal_re]; exact norm_pos_iff.mpr hHT_ne
  have hr1_T_im : (r1 kT).im = 0 := by rw [hr1_T, Complex.ofReal_im]
  have hdiff1 : ∀ i j, r1 i - r1 j = rotC (-φHT) (r i - r j) := fun i j => by
    rw [hr1_eq, hr1_eq, ← map_sub]; congr 1; ring
  have hedge1 : ∀ idx : Fin m, ∀ i : Fin (N + 1),
      0 ≤ cross (r1 (V ⟨((idx : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩) - r1 (V idx)) (r1 i - r1 (V idx)) := by
    intro idx i; rw [hdiff1, hdiff1, cross_rotC]; exact hedge idx i
  have htriple1 : ∀ a b c : Fin m, a < b → b < c →
      0 < cross (r1 (V b) - r1 (V a)) (r1 (V c) - r1 (V a)) := by
    intro a b c hab hbc; rw [hdiff1, hdiff1, cross_rotC]; exact htriple a b c hab hbc
  have hV_ext1 : ∀ idx : Fin m, IsExtreme r1 (V idx) := fun idx => by
    obtain ⟨u, hu, hdot⟩ := hV_ext idx
    refine ⟨rotC (-φHT) u, fun h0 => hu ((rotC (-φHT)).injective (by simpa using h0)), fun i hi => ?_⟩
    rw [hdiff1, dotC_rotC]; exact hdot i hi
  have hull_no_cross : ∀ (a b c d : Fin m), a < b → b < c → c < d →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        (1 - s) * (V a : ℝ) + s * (V c : ℝ) ≠ (1 - t) * (V b : ℝ) + t * (V d : ℝ)) → False := by
    intro a b c d hab hbc hcd hdisj
    obtain ⟨nA, hnA, hA⟩ := hV_ext1 a
    obtain ⟨nB, hnB, hB⟩ := hV_ext1 b
    obtain ⟨nC, hnC, hC⟩ := hV_ext1 c
    obtain ⟨nD, hnD, hD⟩ := hV_ext1 d
    have hsup : ∀ (idx : Fin m) (u : ℂ), (∀ i, i ≠ V idx → dotC u (r1 i - r1 (V idx)) < 0) →
        ∀ z ∈ convexHull ℝ (Set.range r1), dotC u (z - r1 (V idx)) ≤ 0 := fun idx u hu =>
      dotC_le_convexHull fun i => by
        by_cases h : i = V idx
        · subst h; simp [dotC]
        · exact (hu i h).le
    have hAB : cross (r1 (V a) - r1 (V b)) (r1 (V c) - r1 (V b)) < 0 := by
      have h1 := htriple1 a b c hab hbc
      have hid : cross (r1 (V a) - r1 (V b)) (r1 (V c) - r1 (V b)) =
          -cross (r1 (V b) - r1 (V a)) (r1 (V c) - r1 (V a)) := by unfold cross; simp; ring
      linarith
    have hBC : cross (r1 (V c) - r1 (V b)) (r1 (V c) - r1 (V d)) < 0 := by
      have h1 := htriple1 b c d hbc hcd
      have hid : cross (r1 (V c) - r1 (V b)) (r1 (V c) - r1 (V d)) =
          -cross (r1 (V c) - r1 (V b)) (r1 (V d) - r1 (V b)) := by unfold cross; simp; ring
      linarith
    have hCD : cross (r1 (V c) - r1 (V d)) (r1 (V a) - r1 (V d)) < 0 := by
      have h1 := htriple1 a c d (hab.trans hbc) hcd
      have hid : cross (r1 (V c) - r1 (V d)) (r1 (V a) - r1 (V d)) =
          -cross (r1 (V c) - r1 (V a)) (r1 (V d) - r1 (V a)) := by unfold cross; simp; ring
      linarith
    have hDA : cross (r1 (V a) - r1 (V d)) (r1 (V a) - r1 (V b)) < 0 := by
      have h1 := htriple1 a b d hab (hbc.trans hcd)
      have hid : cross (r1 (V a) - r1 (V d)) (r1 (V a) - r1 (V b)) =
          -cross (r1 (V b) - r1 (V a)) (r1 (V d) - r1 (V a)) := by unfold cross; simp; ring
      linarith
    obtain ⟨s, hs, t, ht, heq⟩ := crossing_lemma hnA hnB hnC hnD
      (hsup a nA hA) (hsup b nB hB) (hsup c nC hC) (hsup d nD hD)
      hAB hBC hCD hDA
      (polySubpath_continuousOn r1 (V a) (V c)) (polySubpath_continuousOn r1 (V b) (V d))
      (fun u hu => polySubpath_mem_convexHull r1 (V a) (V c) hu)
      (fun u hu => polySubpath_mem_convexHull r1 (V b) (V d) hu)
      (polySubpath_zero r1 _ _) (polySubpath_one r1 _ _)
      (polySubpath_zero r1 _ _) (polySubpath_one r1 _ _)
    have hinj := polyAt_injOn hgp1 hsimp1
    have hmemI : ∀ (x y : Fin (N + 1)) (u : ℝ), u ∈ Icc (0 : ℝ) 1 →
        (1 - u) * (x : ℝ) + u * (y : ℝ) ∈ Icc (0 : ℝ) (N : ℝ) := fun x y u hu => by
      have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg _
      have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg _
      have hxN : (x : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ x.isLt
      have hyN : (y : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ y.isLt
      exact ⟨by nlinarith [hu.1, hu.2], by nlinarith [hu.1, hu.2]⟩
    exact hdisj s hs t ht (hinj (hmemI _ _ s hs) (hmemI _ _ t ht) heq)
  exact ⟨r1, hgp1, hsimp1, hlen1, huncov1, ⟨{
    m := m, hm3 := hm3, V := V, kH := kH, kT := kT, q := q, hq1 := hq1,
    hV0 := hV0, hVq := hVq, hV_inj := hV_inj, hV_range := hV_range,
    hr1_H := hr1_H, hr1_T_re := hr1_T_re, hr1_T_im := hr1_T_im,
    hedge1 := hedge1, htriple1 := htriple1, hull_no_cross := hull_no_cross
  }⟩⟩

lemma extract_hull_mono {N : ℕ} {r : Fin (N + 1) → ℂ} (hN : 2 ≤ N)
    (hgp : GenPos r) (hsimp : IsSimplePoly r) (hlen : polyLen r ≤ 1) (huncov : ¬ CoveredUnit r) :
    ∃ (r1 : Fin (N + 1) → ℂ),
      GenPos r1 ∧ IsSimplePoly r1 ∧ polyLen r1 ≤ 1 ∧ ¬ CoveredUnit r1 ∧ Nonempty (HullMonoData r1) := by
  obtain ⟨r1, hgp1, hsimp1, hlen1, huncov1, ⟨A⟩⟩ := extract_hull_aligned hN hgp hsimp hlen huncov
  rcases A with ⟨m, hm3, V, kH, kT, q, hq1, hV0, hVq, hV_inj, hV_range, hr1_H, hr1_T_re, hr1_T_im,
    hedge1, htriple1, hull_no_cross⟩
  let qN : ℕ := q
  have hqN_lt : qN < m := q.isLt
  let pN : ℕ := m - qN
  have hpN1 : 1 ≤ pN := by omega
  let L : Fin (qN + 1) → Fin (N + 1) := fun j => V ⟨(j : ℕ), by omega⟩
  let U : Fin (pN + 1) → Fin (N + 1) := fun i =>
    if h : (i : ℕ) = 0 then kH else V ⟨m - (i : ℕ), by omega⟩
  have hL0 : L ⟨0, by omega⟩ = kH := hV0
  have hLq : L ⟨qN, by omega⟩ = kT := hVq
  have hU0 : U ⟨0, by omega⟩ = kH := by simp [U]
  have hUp : U ⟨pN, by omega⟩ = kT := by
    have hp0 : pN ≠ 0 := by omega
    simp only [U, hp0, ↓reduceDIte]
    have heq : (⟨m - pN, by omega⟩ : Fin m) = q := Fin.ext (by dsimp [pN, qN]; omega)
    rw [heq]; exact hVq
  have hL_im_neg : ∀ j : Fin (qN + 1), 0 < (j : ℕ) → (j : ℕ) < qN → (r1 (L j)).im < 0 := by
    intro j hj0 hjq
    have hcr := htriple1 ⟨0, by omega⟩ ⟨(j : ℕ), by omega⟩ q
      (by change 0 < (j : ℕ); exact hj0) (by change (j : ℕ) < qN; exact hjq)
    rw [hV0, hVq, hr1_H, sub_zero, sub_zero] at hcr
    unfold cross at hcr; rw [hr1_T_im] at hcr
    change (r1 (V ⟨(j : ℕ), by omega⟩)).im < 0
    nlinarith
  have hU_im_pos : ∀ i : Fin (pN + 1), 0 < (i : ℕ) → (i : ℕ) < pN → 0 < (r1 (U i)).im := by
    intro i hi0 hip
    have hcr := htriple1 ⟨0, by omega⟩ q ⟨m - (i : ℕ), by omega⟩
      (by change 0 < qN; omega) (by change qN < m - (i : ℕ); omega)
    rw [hV0, hVq, hr1_H, sub_zero, sub_zero] at hcr
    unfold cross at hcr; rw [hr1_T_im] at hcr
    have hi_ne : (i : ℕ) ≠ 0 := by omega
    simp only [U, hi_ne, ↓reduceDIte]
    nlinarith
  have hUL_ne : ∀ (i : Fin (pN + 1)) (j : Fin (qN + 1)),
      0 < (i : ℕ) → (i : ℕ) < pN → 0 < (j : ℕ) → (j : ℕ) < qN → U i ≠ L j := by
    intro i j hi0 hip hj0 hjq heq
    have h1 := hU_im_pos i hi0 hip
    have h2 := hL_im_neg j hj0 hjq
    rw [heq] at h1; linarith
  have hL_mono : StrictMono L := by
    intro j1 j2 h12
    by_contra hle; push Not at hle
    have hne : L j1 ≠ L j2 := fun h => by
      have hv := congrArg Fin.val (hV_inj h)
      exact h12.ne (Fin.ext hv)
    have hlt : L j2 < L j1 := lt_of_le_of_ne hle hne.symm
    have hj1_pos : 0 < (j1 : ℕ) := by
      by_contra h0
      have hj10 : j1 = ⟨0, by omega⟩ := Fin.ext (by change (j1 : ℕ) = 0; omega)
      rw [hj10, hL0] at hlt
      exact not_lt_of_ge (hV_range ⟨(j2 : ℕ), by omega⟩).1 hlt
    have hj2_lt : (j2 : ℕ) < qN := by
      by_contra h0
      have hj2q : j2 = ⟨qN, by omega⟩ := Fin.ext (by change (j2 : ℕ) = qN; omega)
      rw [hj2q, hLq] at hlt
      exact not_lt_of_ge (hV_range ⟨(j1 : ℕ), by omega⟩).2 hlt
    apply hull_no_cross ⟨0, by omega⟩ ⟨(j1 : ℕ), by omega⟩ ⟨(j2 : ℕ), by omega⟩ q
      (by change 0 < (j1 : ℕ); exact hj1_pos)
      (by change (j1 : ℕ) < (j2 : ℕ); exact h12)
      (by change (j2 : ℕ) < qN; exact hj2_lt)
    intro s hs t ht
    have h1 : (V ⟨0, by omega⟩ : ℝ) ≤ (V ⟨(j2 : ℕ), by omega⟩ : ℝ) := by
      rw [hV0]; exact_mod_cast (hV_range ⟨(j2 : ℕ), by omega⟩).1
    have h2 : (V ⟨(j2 : ℕ), by omega⟩ : ℝ) < (V ⟨(j1 : ℕ), by omega⟩ : ℝ) := by exact_mod_cast hlt
    have h3 : (V ⟨(j1 : ℕ), by omega⟩ : ℝ) ≤ (V q : ℝ) := by
      rw [hVq]; exact_mod_cast (hV_range ⟨(j1 : ℕ), by omega⟩).2
    have hL_le : (1 - s) * (V ⟨0, by omega⟩ : ℝ) + s * (V ⟨(j2 : ℕ), by omega⟩ : ℝ) ≤
        (V ⟨(j2 : ℕ), by omega⟩ : ℝ) := by nlinarith [hs.1, hs.2]
    have hR_ge : (V ⟨(j1 : ℕ), by omega⟩ : ℝ) ≤
        (1 - t) * (V ⟨(j1 : ℕ), by omega⟩ : ℝ) + t * (V q : ℝ) := by nlinarith [ht.1, ht.2]
    linarith
  have hU_mono : StrictMono U := by
    intro i1 i2 h12
    by_contra hle; push Not at hle
    have hne : U i1 ≠ U i2 := by
      intro heq
      by_cases hi1 : (i1 : ℕ) = 0
      · have hi2 : (i2 : ℕ) ≠ 0 := by omega
        simp only [U, hi1, hi2, ↓reduceDIte] at heq
        rw [← hV0] at heq
        have := congrArg Fin.val (hV_inj heq); simp at this; omega
      · have hi2 : (i2 : ℕ) ≠ 0 := by omega
        simp only [U, hi1, hi2, ↓reduceDIte] at heq
        have := congrArg Fin.val (hV_inj heq); simp at this
        exact h12.ne (Fin.ext (by omega))
    have hlt : U i2 < U i1 := lt_of_le_of_ne hle hne.symm
    have hi1_pos : 0 < (i1 : ℕ) := by
      by_contra h0
      have hi10 : i1 = ⟨0, by omega⟩ := Fin.ext (by change (i1 : ℕ) = 0; omega)
      rw [hi10, hU0] at hlt
      have hi2_ne : (i2 : ℕ) ≠ 0 := by omega
      simp only [U, hi2_ne, ↓reduceDIte] at hlt
      exact not_lt_of_ge (hV_range ⟨m - (i2 : ℕ), by omega⟩).1 hlt
    have hi2_lt : (i2 : ℕ) < pN := by
      by_contra h0
      have hi2p : i2 = ⟨pN, by omega⟩ := Fin.ext (by change (i2 : ℕ) = pN; omega)
      rw [hi2p, hUp] at hlt
      have hi1_ne : (i1 : ℕ) ≠ 0 := by omega
      simp only [U, hi1_ne, ↓reduceDIte] at hlt
      exact not_lt_of_ge (hV_range ⟨m - (i1 : ℕ), by omega⟩).2 hlt
    have hi1_ne : (i1 : ℕ) ≠ 0 := by omega
    have hi2_ne : (i2 : ℕ) ≠ 0 := by omega
    simp only [U, hi1_ne, hi2_ne, ↓reduceDIte] at hlt
    apply hull_no_cross ⟨0, by omega⟩ q ⟨m - (i2 : ℕ), by omega⟩ ⟨m - (i1 : ℕ), by omega⟩
      (by change 0 < qN; omega)
      (by change qN < m - (i2 : ℕ); omega)
      (by change m - (i2 : ℕ) < m - (i1 : ℕ); change (i1 : ℕ) < (i2 : ℕ) at h12; omega)
    intro s hs t ht
    have h1 : (V ⟨0, by omega⟩ : ℝ) ≤ (V ⟨m - (i2 : ℕ), by omega⟩ : ℝ) := by
      rw [hV0]; exact_mod_cast (hV_range ⟨m - (i2 : ℕ), by omega⟩).1
    have h2 : (V ⟨m - (i2 : ℕ), by omega⟩ : ℝ) < (V ⟨m - (i1 : ℕ), by omega⟩ : ℝ) := by exact_mod_cast hlt
    have h3 : (V ⟨m - (i1 : ℕ), by omega⟩ : ℝ) ≤ (V q : ℝ) := by
      rw [hVq]; exact_mod_cast (hV_range ⟨m - (i1 : ℕ), by omega⟩).2
    have hL_le : (1 - s) * (V ⟨0, by omega⟩ : ℝ) + s * (V ⟨m - (i2 : ℕ), by omega⟩ : ℝ) ≤
        (V ⟨m - (i2 : ℕ), by omega⟩ : ℝ) := by nlinarith [hs.1, hs.2]
    have hR_ge : (V ⟨m - (i1 : ℕ), by omega⟩ : ℝ) ≤
        (1 - t) * (V q : ℝ) + t * (V ⟨m - (i1 : ℕ), by omega⟩ : ℝ) := by nlinarith [ht.1, ht.2]
    linarith
  have heU_sup : ∀ (i : Fin pN) (k : Fin (N + 1)),
      cross (r1 (U i.succ) - r1 (U i.castSucc)) (r1 k - r1 (U i.castSucc)) ≤ 0 := by
    intro i k
    let idx : Fin m := ⟨m - ((i : ℕ) + 1), by omega⟩
    have hnxt_val : (((idx : ℕ) + 1) % m) = if (i : ℕ) = 0 then 0 else m - (i : ℕ) := by
      dsimp [idx]
      by_cases h0 : (i : ℕ) = 0
      · rw [if_pos h0, h0]
        have hm_eq : m - (0 + 1) + 1 = m := by omega
        rw [hm_eq, Nat.mod_self]
      · rw [if_neg h0, Nat.mod_eq_of_lt (by omega)]; omega
    have hV_idx : V idx = U i.succ := by
      simp only [U, Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte, idx]
    have hV_nxt : V ⟨((idx : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩ = U i.castSucc := by
      by_cases h0 : (i : ℕ) = 0
      · have h1 : (⟨((idx : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = ⟨0, by omega⟩ :=
          Fin.ext (by simp [hnxt_val, h0])
        rw [h1, hV0]; simp only [U, Fin.val_castSucc, h0, ↓reduceDIte]
      · have h1 : (⟨((idx : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = ⟨m - (i : ℕ), by omega⟩ :=
          Fin.ext (by simp [hnxt_val, h0])
        rw [h1]; simp only [U, Fin.val_castSucc, h0, ↓reduceDIte]
    have hsup := hedge1 idx k
    rw [hV_idx, hV_nxt] at hsup
    have hid : cross (r1 (U i.succ) - r1 (U i.castSucc)) (r1 k - r1 (U i.castSucc)) =
        -cross (r1 (U i.castSucc) - r1 (U i.succ)) (r1 k - r1 (U i.succ)) := by unfold cross; simp; ring
    linarith
  have heL_sup : ∀ (j : Fin qN) (k : Fin (N + 1)),
      0 ≤ cross (r1 (L j.succ) - r1 (L j.castSucc)) (r1 k - r1 (L j.castSucc)) := by
    intro j k
    let idx : Fin m := ⟨(j : ℕ), by omega⟩
    have hnxt_eq : (⟨((idx : ℕ) + 1) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = ⟨(j : ℕ) + 1, by omega⟩ := by
      apply Fin.ext; dsimp [idx]; exact Nat.mod_eq_of_lt (by omega)
    have hsup := hedge1 idx k
    rw [hnxt_eq] at hsup; exact hsup
  have heU_turn : ∀ (i : ℕ) (hi : i + 1 < pN),
      cross (r1 (U (⟨i, by omega⟩ : Fin pN).succ) - r1 (U (⟨i, by omega⟩ : Fin pN).castSucc))
        (r1 (U (⟨i + 1, hi⟩ : Fin pN).succ) - r1 (U (⟨i + 1, hi⟩ : Fin pN).castSucc)) < 0 := by
    intro i hi
    have hsup := heU_sup ⟨i, by omega⟩ (U ⟨i + 2, by omega⟩)
    have hid : cross (r1 (U (⟨i, by omega⟩ : Fin pN).succ) - r1 (U (⟨i, by omega⟩ : Fin pN).castSucc))
        (r1 (U (⟨i + 1, hi⟩ : Fin pN).succ) - r1 (U (⟨i + 1, hi⟩ : Fin pN).castSucc)) =
        cross (r1 (U ⟨i + 1, by omega⟩) - r1 (U ⟨i, by omega⟩))
          (r1 (U ⟨i + 2, by omega⟩) - r1 (U ⟨i, by omega⟩)) := by
      unfold cross; simp; ring
    have hne : cross (r1 (U ⟨i + 1, by omega⟩) - r1 (U ⟨i, by omega⟩))
        (r1 (U ⟨i + 2, by omega⟩) - r1 (U ⟨i, by omega⟩)) ≠ 0 :=
      hgp1.2 _ _ _
        (hU_mono (show (⟨i, by omega⟩ : Fin (pN + 1)) < ⟨i + 1, by omega⟩ by simp)).ne
        (hU_mono (show (⟨i + 1, by omega⟩ : Fin (pN + 1)) < ⟨i + 2, by omega⟩ by simp)).ne
        (hU_mono (show (⟨i, by omega⟩ : Fin (pN + 1)) < ⟨i + 2, by omega⟩ by simp)).ne
    rw [hid]
    exact lt_of_le_of_ne hsup hne
  have heL_turn : ∀ (j : ℕ) (hj : j + 1 < qN),
      0 < cross (r1 (L (⟨j, by omega⟩ : Fin qN).succ) - r1 (L (⟨j, by omega⟩ : Fin qN).castSucc))
        (r1 (L (⟨j + 1, hj⟩ : Fin qN).succ) - r1 (L (⟨j + 1, hj⟩ : Fin qN).castSucc)) := by
    intro j hj
    have hsup := heL_sup ⟨j, by omega⟩ (L ⟨j + 2, by omega⟩)
    have hid : cross (r1 (L (⟨j, by omega⟩ : Fin qN).succ) - r1 (L (⟨j, by omega⟩ : Fin qN).castSucc))
        (r1 (L (⟨j + 1, hj⟩ : Fin qN).succ) - r1 (L (⟨j + 1, hj⟩ : Fin qN).castSucc)) =
        cross (r1 (L ⟨j + 1, by omega⟩) - r1 (L ⟨j, by omega⟩))
          (r1 (L ⟨j + 2, by omega⟩) - r1 (L ⟨j, by omega⟩)) := by
      unfold cross; simp; ring
    have hne : cross (r1 (L ⟨j + 1, by omega⟩) - r1 (L ⟨j, by omega⟩))
        (r1 (L ⟨j + 2, by omega⟩) - r1 (L ⟨j, by omega⟩)) ≠ 0 :=
      hgp1.2 _ _ _
        (hL_mono (show (⟨j, by omega⟩ : Fin (qN + 1)) < ⟨j + 1, by omega⟩ by simp)).ne
        (hL_mono (show (⟨j + 1, by omega⟩ : Fin (qN + 1)) < ⟨j + 2, by omega⟩ by simp)).ne
        (hL_mono (show (⟨j, by omega⟩ : Fin (qN + 1)) < ⟨j + 2, by omega⟩ by simp)).ne
    rw [hid]
    exact lt_of_le_of_ne hsup hne.symm
  have hcrH : 0 < cross (r1 (L (⟨0, by omega⟩ : Fin qN).succ) - r1 (L (⟨0, by omega⟩ : Fin qN).castSucc))
      (r1 (U (⟨0, by omega⟩ : Fin pN).succ) - r1 (U (⟨0, by omega⟩ : Fin pN).castSucc)) := by
    have h1 : r1 (L (⟨0, by omega⟩ : Fin qN).succ) - r1 (L (⟨0, by omega⟩ : Fin qN).castSucc) =
        r1 (V ⟨1, by omega⟩) - r1 (V ⟨0, by omega⟩) := rfl
    have h2 : r1 (U (⟨0, by omega⟩ : Fin pN).succ) - r1 (U (⟨0, by omega⟩ : Fin pN).castSucc) =
        r1 (V ⟨m - 1, by omega⟩) - r1 (V ⟨0, by omega⟩) := by dsimp [U]; simp [hV0]
    rw [h1, h2]
    exact htriple1 ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨m - 1, by omega⟩ (by simp) (by change 1 < m - 1; omega)
  have hcrT : 0 < cross (r1 (U (⟨pN - 1, by omega⟩ : Fin pN).succ) - r1 (U (⟨pN - 1, by omega⟩ : Fin pN).castSucc))
      (r1 (L (⟨qN - 1, by omega⟩ : Fin qN).succ) - r1 (L (⟨qN - 1, by omega⟩ : Fin qN).castSucc)) := by
    have h1 : r1 (L (⟨qN - 1, by omega⟩ : Fin qN).succ) - r1 (L (⟨qN - 1, by omega⟩ : Fin qN).castSucc) =
        r1 (V q) - r1 (V ⟨qN - 1, by omega⟩) := by
      dsimp [L]
      have hqeq : (⟨qN - 1 + 1, by omega⟩ : Fin m) = q := Fin.ext (by dsimp [qN]; omega)
      rw [hqeq]
    have h2 : r1 (U (⟨pN - 1, by omega⟩ : Fin pN).succ) - r1 (U (⟨pN - 1, by omega⟩ : Fin pN).castSucc) =
        r1 (V q) - r1 (V ⟨(qN + 1) % m, Nat.mod_lt _ (by omega)⟩) := by
      have hs : (⟨pN - 1, by omega⟩ : Fin pN).succ = ⟨pN, by omega⟩ := Fin.ext (by simp; omega)
      rw [hs, hUp, ← hVq]
      congr 1
      by_cases hp1 : pN = 1
      · have hc : (⟨pN - 1, by omega⟩ : Fin pN).castSucc = ⟨0, by omega⟩ := Fin.ext (by simp [hp1])
        have hmod : (qN + 1) % m = 0 := by
          have hm_eq : qN + 1 = m := by omega
          rw [hm_eq, Nat.mod_self]
        rw [hc, hU0, show (⟨(qN + 1) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = ⟨0, by omega⟩ from
          Fin.ext hmod, hV0]
      · have hc_ne : ((⟨pN - 1, by omega⟩ : Fin pN).castSucc : ℕ) ≠ 0 := by simp; omega
        simp only [U, hc_ne, ↓reduceDIte]
        congr 1; congr 1; apply Fin.ext
        show m - ((⟨pN - 1, by omega⟩ : Fin pN).castSucc : ℕ) = (qN + 1) % m
        rw [Fin.val_castSucc, Fin.val_mk, Nat.mod_eq_of_lt (by omega)]; omega
    rw [h1, h2]
    by_cases hp1 : pN = 1
    · have hmod : (⟨(qN + 1) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = ⟨0, by omega⟩ := by
        apply Fin.ext; show (qN + 1) % m = 0
        have hm_eq : qN + 1 = m := by omega
        rw [hm_eq, Nat.mod_self]
      rw [hmod]
      have htr := htriple1 ⟨0, by omega⟩ ⟨qN - 1, by omega⟩ q
        (by change 0 < qN - 1; omega) (by change qN - 1 < qN; omega)
      have hid : cross (r1 (V q) - r1 (V ⟨0, by omega⟩)) (r1 (V q) - r1 (V ⟨qN - 1, by omega⟩)) =
          cross (r1 (V ⟨qN - 1, by omega⟩) - r1 (V ⟨0, by omega⟩)) (r1 (V q) - r1 (V ⟨0, by omega⟩)) := by
        unfold cross; simp; ring
      linarith
    · have hmod : (⟨(qN + 1) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = ⟨qN + 1, by omega⟩ :=
        Fin.ext (by simp; exact Nat.mod_eq_of_lt (by omega))
      rw [hmod]
      have htr := htriple1 ⟨qN - 1, by omega⟩ q ⟨qN + 1, by omega⟩
        (by change qN - 1 < qN; omega) (by change qN < qN + 1; omega)
      have hid : cross (r1 (V q) - r1 (V ⟨qN + 1, by omega⟩)) (r1 (V q) - r1 (V ⟨qN - 1, by omega⟩)) =
          cross (r1 (V q) - r1 (V ⟨qN - 1, by omega⟩)) (r1 (V ⟨qN + 1, by omega⟩) - r1 (V ⟨qN - 1, by omega⟩)) := by
        unfold cross; simp; ring
      linarith
  exact ⟨r1, hgp1, hsimp1, hlen1, huncov1, ⟨{
    pN := pN, qN := qN, hpN1 := hpN1, hqN1 := hq1, hsum3 := by omega,
    kH := kH, kT := kT, hr1_H := hr1_H, hr1_T_re := hr1_T_re, hr1_T_im := hr1_T_im,
    U := U, L := L, hU0 := hU0, hUp := hUp, hL0 := hL0, hLq := hLq,
    hU_im_pos := hU_im_pos, hL_im_neg := hL_im_neg, hUL_ne := hUL_ne,
    hU_mono := hU_mono, hL_mono := hL_mono,
    heU_sup := heU_sup, heL_sup := heL_sup, heU_turn := heU_turn, heL_turn := heL_turn,
    hcrH := hcrH, hcrT := hcrT }⟩⟩

structure HullChainsData {N : ℕ} (r1 : Fin (N + 1) → ℂ) where
  pN : ℕ
  qN : ℕ
  hpN1 : 1 ≤ pN
  hqN1 : 1 ≤ qN
  hsum3 : 3 ≤ pN + qN
  U : Fin (pN + 1) → Fin (N + 1)
  L : Fin (qN + 1) → Fin (N + 1)
  hU0_L0 : U ⟨0, by omega⟩ = L ⟨0, by omega⟩
  hUp_Lq : U ⟨pN, by omega⟩ = L ⟨qN, by omega⟩
  hU_mono : StrictMono U
  hL_mono : StrictMono L
  hUL_ne : ∀ (i : Fin (pN + 1)) (j : Fin (qN + 1)),
    0 < (i : ℕ) → (i : ℕ) < pN → 0 < (j : ℕ) → (j : ℕ) < qN → U i ≠ L j
  α : Fin pN → ℝ
  β : Fin qN → ℝ
  hα_anti : StrictAnti α
  hβ_mono : StrictMono β
  hU_edge_sup : ∀ (i : Fin pN) (k : Fin (N + 1)), cross (dir (α i)) (r1 k - r1 (U i.castSucc)) ≤ 0
  hL_edge_sup : ∀ (j : Fin qN) (k : Fin (N + 1)), 0 ≤ cross (dir (β j)) (r1 k - r1 (L j.castSucc))
  hU_vtx_sup : ∀ (i : ℕ) (hi : i + 1 < pN) (θ : ℝ),
    α ⟨i + 1, hi⟩ ≤ θ → θ ≤ α ⟨i, by omega⟩ →
    ∀ k, cross (dir θ) (r1 k - r1 (U ⟨i + 1, by omega⟩)) ≤ 0
  hL_vtx_sup : ∀ (j : ℕ) (hj : j + 1 < qN) (θ : ℝ),
    β ⟨j, by omega⟩ ≤ θ → θ ≤ β ⟨j + 1, hj⟩ →
    ∀ k, 0 ≤ cross (dir θ) (r1 k - r1 (L ⟨j + 1, by omega⟩))
  hcr_eU : ∀ i : Fin pN, cross (dir (α i)) (r1 (U i.succ) - r1 (U i.castSucc)) = 0
  hdot_eU : ∀ i : Fin pN, 0 < dotC (dir (α i)) (r1 (U i.succ) - r1 (U i.castSucc))
  hcr_eL : ∀ j : Fin qN, cross (dir (β j)) (r1 (L j.succ) - r1 (L j.castSucc)) = 0
  hdot_eL : ∀ j : Fin qN, 0 < dotC (dir (β j)) (r1 (L j.succ) - r1 (L j.castSucc))
  hH_ang_gt : Real.pi / 6 < α ⟨0, by omega⟩ - β ⟨0, by omega⟩
  hT_ang_gt : Real.pi / 6 < β ⟨qN - 1, by omega⟩ - α ⟨pN - 1, by omega⟩

lemma extract_hull_chains {N : ℕ} {r1 : Fin (N + 1) → ℂ}
    (hgp1 : GenPos r1) (hlen1 : polyLen r1 ≤ 1) (huncov1 : ¬ CoveredUnit r1)
    (D : HullMonoData r1) : Nonempty (HullChainsData r1) := by
  rcases D with ⟨pN, qN, hpN1, hqN1, hsum3, kH, kT, hr1_H, hr1_T_re, hr1_T_im,
    U, L, hU0, hUp, hL0, hLq, hU_im_pos, hL_im_neg, hUL_ne, hU_mono, hL_mono,
    heU_sup, heL_sup, heU_turn, heL_turn, hcrH_D, hcrT_D⟩
  let eU (i : Fin pN) : ℂ := r1 (U i.succ) - r1 (U i.castSucc)
  let eL (j : Fin qN) : ℂ := r1 (L j.succ) - r1 (L j.castSucc)
  have heU_ne : ∀ i : Fin pN, eU i ≠ 0 := fun i =>
    sub_ne_zero.mpr (hgp1.1 _ _ (hU_mono (Fin.castSucc_lt_succ (i := i))).ne')
  have heL_ne : ∀ j : Fin qN, eL j ≠ 0 := fun j =>
    sub_ne_zero.mpr (hgp1.1 _ _ (hL_mono (Fin.castSucc_lt_succ (i := j))).ne')
  -- No edge points along the negative real axis (im = 0, re ≤ 0)!
  have heU_not_neg_real : ∀ i : Fin pN, ¬ ((eU i).im = 0 ∧ (eU i).re ≤ 0) := by
    intro i ⟨him, hre⟩
    by_cases h0 : (i : ℕ) = 0
    · by_cases hp1 : pN = 1
      · have heq : eU i = r1 kT := by
          dsimp [eU]
          have h1 : i.castSucc = ⟨0, by omega⟩ := Fin.ext (by simp [h0])
          have h2 : i.succ = ⟨pN, by omega⟩ := Fin.ext (by simp [h0, hp1])
          rw [h1, h2, hU0, hUp, hr1_H, sub_zero]
        rw [heq] at hre; linarith
      · have h1 : i.castSucc = ⟨0, by omega⟩ := Fin.ext (by simp [h0])
        have hpos : 0 < (r1 (U i.succ)).im := hU_im_pos i.succ (by simp) (by simp [h0]; omega)
        have : (eU i).im = (r1 (U i.succ)).im := by simp only [eU, h1, hU0, hr1_H, sub_zero]
        linarith
    · have hpos : 0 < (r1 (U i.castSucc)).im := hU_im_pos i.castSucc (by simp; omega) (by simp)
      have hsup := heU_sup i kH
      rw [hr1_H, zero_sub] at hsup
      unfold cross at hsup; simp at hsup
      have hlt : (eU i).re < 0 := by
        rcases eq_or_lt_of_le hre with hre0 | hlt
        · exact absurd (Complex.ext hre0 him) (heU_ne i)
        · exact hlt
      simp [eU] at him hlt
      rw [him, zero_mul] at hsup
      nlinarith
  have heL_not_neg_real : ∀ j : Fin qN, ¬ ((eL j).im = 0 ∧ (eL j).re ≤ 0) := by
    intro j ⟨him, hre⟩
    by_cases h0 : (j : ℕ) = 0
    · by_cases hq1' : qN = 1
      · have heq : eL j = r1 kT := by
          dsimp [eL]
          have h1 : j.castSucc = ⟨0, by omega⟩ := Fin.ext (by simp [h0])
          have h2 : j.succ = ⟨qN, by omega⟩ := Fin.ext (by simp [h0, hq1'])
          rw [h1, h2, hL0, hLq, hr1_H, sub_zero]
        rw [heq] at hre; linarith
      · have h1 : j.castSucc = ⟨0, by omega⟩ := Fin.ext (by simp [h0])
        have hneg : (r1 (L j.succ)).im < 0 := hL_im_neg j.succ (by simp) (by simp [h0]; omega)
        have : (eL j).im = (r1 (L j.succ)).im := by simp only [eL, h1, hL0, hr1_H, sub_zero]
        linarith
    · have hneg : (r1 (L j.castSucc)).im < 0 := hL_im_neg j.castSucc (by simp; omega) (by simp)
      have hsup := heL_sup j kH
      rw [hr1_H, zero_sub] at hsup
      unfold cross at hsup; simp at hsup
      have hlt : (eL j).re < 0 := by
        rcases eq_or_lt_of_le hre with hre0 | hlt
        · exact absurd (Complex.ext hre0 him) (heL_ne j)
        · exact hlt
      simp [eL] at him hlt
      rw [him, zero_mul] at hsup
      nlinarith
  let α : Fin pN → ℝ := fun i => Complex.arg (eU i)
  let β : Fin qN → ℝ := fun j => Complex.arg (eL j)
  have hα_lt_pi : ∀ i : Fin pN, α i < Real.pi := fun i => by
    have hm := Complex.arg_mem_Ioc (eU i)
    rcases eq_or_lt_of_le hm.2 with heq | hlt
    · exfalso
      have hneg := Complex.arg_eq_pi_iff.mp heq
      exact heU_not_neg_real i ⟨hneg.2, hneg.1.le⟩
    · exact hlt
  have hβ_lt_pi : ∀ j : Fin qN, β j < Real.pi := fun j => by
    have hm := Complex.arg_mem_Ioc (eL j)
    rcases eq_or_lt_of_le hm.2 with heq | hlt
    · exfalso
      have hneg := Complex.arg_eq_pi_iff.mp heq
      exact heL_not_neg_real j ⟨hneg.2, hneg.1.le⟩
    · exact hlt
  have hα_step : ∀ (i : ℕ) (hi : i + 1 < pN),
      α ⟨i + 1, hi⟩ < α ⟨i, by omega⟩ ∧ α ⟨i, by omega⟩ - α ⟨i + 1, hi⟩ < Real.pi := by
    intro i hi
    let i1 : Fin pN := ⟨i, by omega⟩
    let i2 : Fin pN := ⟨i + 1, hi⟩
    have hcr := heU_turn i hi
    have hP_pos : 0 < (r1 (U i2.castSucc)).im := hU_im_pos i2.castSucc (by simp [i2]) (by simp [i2]; omega)
    have hsup1 : cross (eU i1) (0 - r1 (U i2.castSucc)) ≤ 0 := by
      have h := heU_sup i1 kH
      rw [hr1_H] at h
      have hid : cross (eU i1) (0 - r1 (U i2.castSucc)) = cross (eU i1) (0 - r1 (U i1.castSucc)) := by
        have hs : i1.succ = i2.castSucc := Fin.ext (by simp [i1, i2])
        dsimp [eU]; rw [← hs]; unfold cross; simp; ring
      linarith
    have hsup2 : cross (eU i2) (0 - r1 (U i2.castSucc)) ≤ 0 := by
      simpa [hr1_H] using heU_sup i2 kH
    have hno_wrap : ¬ ((eU i1).im ≤ 0 ∧ 0 ≤ (eU i2).im) := by
      rintro ⟨h1, h2⟩
      unfold cross at hsup1 hsup2 hcr; simp at hsup1 hsup2
      have hcomb : (eU i2).im * ((eU i1).im * (r1 (U i2.castSucc)).re - (eU i1).re * (r1 (U i2.castSucc)).im) +
          (-(eU i1).im) * ((eU i2).im * (r1 (U i2.castSucc)).re - (eU i2).re * (r1 (U i2.castSucc)).im) =
          -((eU i1).re * (eU i2).im - (eU i1).im * (eU i2).re) * (r1 (U i2.castSucc)).im := by ring
      nlinarith
    have hsin_pos : 0 < Real.sin (α i1 - α i2) := by
      have h1 : cross (dir (α i2)) (dir (α i1)) = Real.sin (α i1 - α i2) := cross_dir_dir _ _
      have h2 : cross (dir (α i1)) (dir (α i2)) = cross (eU i1) (eU i2) / (‖eU i1‖ * ‖eU i2‖) := by
        rw [cross_dir_arg_eq (heU_ne i1)]
        have h3 := cross_dir_arg_eq (z := eU i2) (w := eU i1) (heU_ne i2)
        rw [cross_antisymm (eU i1) (dir (α i2)), h3, cross_antisymm (eU i2) (eU i1)]
        have hn1 : ‖eU i1‖ ≠ 0 := norm_ne_zero_iff.mpr (heU_ne i1)
        have hn2 : ‖eU i2‖ ≠ 0 := norm_ne_zero_iff.mpr (heU_ne i2)
        field_simp [hn1, hn2]
      rw [← h1, cross_antisymm, h2]
      have hden : 0 < ‖eU i1‖ * ‖eU i2‖ := mul_pos (norm_pos_iff.mpr (heU_ne i1)) (norm_pos_iff.mpr (heU_ne i2))
      rw [neg_pos]; exact div_neg_of_neg_of_pos hcr hden
    have hm1 := Complex.arg_mem_Ioc (eU i1)
    have hm2 := Complex.arg_mem_Ioc (eU i2)
    have hlt1 := hα_lt_pi i1
    have hlt2 := hα_lt_pi i2
    have hlt : α i2 < α i1 := by
      by_cases h1 : 0 ≤ (eU i1).im
      · have ha1 : 0 ≤ α i1 := Complex.arg_nonneg_iff.mpr h1
        by_cases h2 : 0 ≤ (eU i2).im
        · have ha2 : 0 ≤ α i2 := Complex.arg_nonneg_iff.mpr h2
          by_contra hge; push Not at hge
          have hneg : Real.sin (α i1 - α i2) ≤ 0 := by
            have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ α i2 - α i1 by linarith) (by linarith)
            rw [show α i1 - α i2 = -(α i2 - α i1) by ring, Real.sin_neg]; linarith
          linarith
        · have ha2 : α i2 < 0 := Complex.arg_neg_iff.mpr (not_le.mp h2)
          linarith
      · have h1' : (eU i1).im < 0 := not_le.mp h1
        have h2' : (eU i2).im < 0 := by by_contra h2; exact hno_wrap ⟨h1'.le, not_lt.mp h2⟩
        have ha1 : α i1 < 0 := Complex.arg_neg_iff.mpr h1'
        have ha2 : α i2 < 0 := Complex.arg_neg_iff.mpr h2'
        by_contra hge; push Not at hge
        have hneg : Real.sin (α i1 - α i2) ≤ 0 := by
          have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ α i2 - α i1 by linarith) (by linarith [hm1.1, hm2.1])
          rw [show α i1 - α i2 = -(α i2 - α i1) by ring, Real.sin_neg]; linarith
        linarith
    refine ⟨hlt, ?_⟩
    by_contra hge; push Not at hge
    have hle : Real.sin (α i1 - α i2) ≤ 0 := by
      have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ (α i1 - α i2) - Real.pi by linarith)
        (by linarith [hm2.1])
      rw [Real.sin_sub_pi] at this; linarith
    linarith
  have hβ_step : ∀ (j : ℕ) (hj : j + 1 < qN),
      β ⟨j, by omega⟩ < β ⟨j + 1, hj⟩ ∧ β ⟨j + 1, hj⟩ - β ⟨j, by omega⟩ < Real.pi := by
    intro j hj
    let j1 : Fin qN := ⟨j, by omega⟩
    let j2 : Fin qN := ⟨j + 1, hj⟩
    have hcr := heL_turn j hj
    have hP_neg : (r1 (L j2.castSucc)).im < 0 := hL_im_neg j2.castSucc (by simp [j2]) (by simp [j2]; omega)
    have hsup1 : 0 ≤ cross (eL j1) (0 - r1 (L j2.castSucc)) := by
      have h := heL_sup j1 kH
      rw [hr1_H] at h
      have hid : cross (eL j1) (0 - r1 (L j2.castSucc)) = cross (eL j1) (0 - r1 (L j1.castSucc)) := by
        have hs : j1.succ = j2.castSucc := Fin.ext (by simp [j1, j2])
        dsimp [eL]; rw [← hs]; unfold cross; simp; ring
      linarith
    have hsup2 : 0 ≤ cross (eL j2) (0 - r1 (L j2.castSucc)) := by
      simpa [hr1_H] using heL_sup j2 kH
    have hno_wrap : ¬ (0 ≤ (eL j1).im ∧ (eL j2).im ≤ 0) := by
      rintro ⟨h1, h2⟩
      unfold cross at hsup1 hsup2 hcr; simp at hsup1 hsup2
      have hcomb : (-(eL j2).im) * ((eL j1).im * (r1 (L j2.castSucc)).re - (eL j1).re * (r1 (L j2.castSucc)).im) +
          (eL j1).im * ((eL j2).im * (r1 (L j2.castSucc)).re - (eL j2).re * (r1 (L j2.castSucc)).im) =
          ((eL j1).re * (eL j2).im - (eL j1).im * (eL j2).re) * (r1 (L j2.castSucc)).im := by ring
      nlinarith
    have hsin_pos : 0 < Real.sin (β j2 - β j1) := by
      have h1 : cross (dir (β j1)) (dir (β j2)) = Real.sin (β j2 - β j1) := cross_dir_dir _ _
      have h2 : cross (dir (β j1)) (dir (β j2)) = cross (eL j1) (eL j2) / (‖eL j1‖ * ‖eL j2‖) := by
        rw [cross_dir_arg_eq (heL_ne j1)]
        have h3 := cross_dir_arg_eq (z := eL j2) (w := eL j1) (heL_ne j2)
        rw [cross_antisymm (eL j1) (dir (β j2)), h3, cross_antisymm (eL j2) (eL j1)]
        have hn1 : ‖eL j1‖ ≠ 0 := norm_ne_zero_iff.mpr (heL_ne j1)
        have hn2 : ‖eL j2‖ ≠ 0 := norm_ne_zero_iff.mpr (heL_ne j2)
        field_simp [hn1, hn2]
      rw [← h1, h2]
      exact div_pos hcr (mul_pos (norm_pos_iff.mpr (heL_ne j1)) (norm_pos_iff.mpr (heL_ne j2)))
    have hm1 := Complex.arg_mem_Ioc (eL j1)
    have hm2 := Complex.arg_mem_Ioc (eL j2)
    have hlt1 := hβ_lt_pi j1
    have hlt2 := hβ_lt_pi j2
    have hlt : β j1 < β j2 := by
      by_cases h1 : (eL j1).im < 0
      · have hb1 : β j1 < 0 := Complex.arg_neg_iff.mpr h1
        by_cases h2 : (eL j2).im < 0
        · have hb2 : β j2 < 0 := Complex.arg_neg_iff.mpr h2
          by_contra hge; push Not at hge
          have hneg : Real.sin (β j2 - β j1) ≤ 0 := by
            have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ β j1 - β j2 by linarith) (by linarith [hm1.1, hm2.1])
            rw [show β j2 - β j1 = -(β j1 - β j2) by ring, Real.sin_neg]; linarith
          linarith
        · have hb2 : 0 ≤ β j2 := Complex.arg_nonneg_iff.mpr (not_lt.mp h2)
          linarith
      · have h1' : 0 ≤ (eL j1).im := not_lt.mp h1
        have h2' : 0 < (eL j2).im := by by_contra h2; exact hno_wrap ⟨h1', not_lt.mp h2⟩
        have hb1 : 0 ≤ β j1 := Complex.arg_nonneg_iff.mpr h1'
        have hb2 : 0 ≤ β j2 := Complex.arg_nonneg_iff.mpr h2'.le
        by_contra hge; push Not at hge
        have hneg : Real.sin (β j2 - β j1) ≤ 0 := by
          have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ β j1 - β j2 by linarith) (by linarith)
          rw [show β j2 - β j1 = -(β j1 - β j2) by ring, Real.sin_neg]; linarith
        linarith
    refine ⟨hlt, ?_⟩
    by_contra hge; push Not at hge
    have hle : Real.sin (β j2 - β j1) ≤ 0 := by
      have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ (β j2 - β j1) - Real.pi by linarith)
        (by linarith [hm1.1])
      rw [Real.sin_sub_pi] at this; linarith
    linarith
  have hα_anti : StrictAnti α := by
    have haux : ∀ d (i : ℕ) (hi : i + d + 1 < pN), α ⟨i + d + 1, hi⟩ < α ⟨i, by omega⟩ := by
      intro d
      induction d with
      | zero => intro i hi; exact (hα_step i hi).1
      | succ d ih =>
        intro i hi
        exact lt_trans (hα_step (i + d + 1) hi).1 (ih i (by omega))
    intro i1 i2 h12
    have hd : (i1 : ℕ) + ((i2 : ℕ) - (i1 : ℕ) - 1) + 1 = (i2 : ℕ) := by omega
    have h := haux ((i2 : ℕ) - (i1 : ℕ) - 1) (i1 : ℕ) (by omega)
    have h2 : (⟨(i1 : ℕ) + ((i2 : ℕ) - (i1 : ℕ) - 1) + 1, by omega⟩ : Fin pN) = i2 := Fin.ext hd
    rw [h2] at h; exact h
  have hβ_mono : StrictMono β := by
    have haux : ∀ d (j : ℕ) (hj : j + d + 1 < qN), β ⟨j, by omega⟩ < β ⟨j + d + 1, hj⟩ := by
      intro d
      induction d with
      | zero => intro j hj; exact (hβ_step j hj).1
      | succ d ih =>
        intro j hj
        exact lt_trans (ih j (by omega)) (hβ_step (j + d + 1) hj).1
    intro j1 j2 h12
    have hd : (j1 : ℕ) + ((j2 : ℕ) - (j1 : ℕ) - 1) + 1 = (j2 : ℕ) := by omega
    have h := haux ((j2 : ℕ) - (j1 : ℕ) - 1) (j1 : ℕ) (by omega)
    have h2 : (⟨(j1 : ℕ) + ((j2 : ℕ) - (j1 : ℕ) - 1) + 1, by omega⟩ : Fin qN) = j2 := Fin.ext hd
    rw [h2] at h; exact h
  -- Support lemmas for edges and intermediate angles at vertices
  have hU_edge_sup : ∀ (i : Fin pN) (k : Fin (N + 1)),
      cross (dir (α i)) (r1 k - r1 (U i.castSucc)) ≤ 0 := fun i k => by
    rw [cross_dir_arg_eq (heU_ne i)]
    exact div_nonpos_of_nonpos_of_nonneg (heU_sup i k) (norm_nonneg _)
  have hU_edge_sup_succ : ∀ (i : Fin pN) (k : Fin (N + 1)),
      cross (dir (α i)) (r1 k - r1 (U i.succ)) ≤ 0 := fun i k => by
    have hid : cross (dir (α i)) (r1 k - r1 (U i.succ)) = cross (dir (α i)) (r1 k - r1 (U i.castSucc)) := by
      have h1 : r1 k - r1 (U i.succ) = (r1 k - r1 (U i.castSucc)) - eU i := by dsimp [eU]; ring
      rw [h1, cross_sub_right, cross_dir_arg_eq (heU_ne i) (w := eU i), cross_self, zero_div, sub_zero]
    rw [hid]; exact hU_edge_sup i k
  have hL_edge_sup : ∀ (j : Fin qN) (k : Fin (N + 1)),
      0 ≤ cross (dir (β j)) (r1 k - r1 (L j.castSucc)) := fun j k => by
    rw [cross_dir_arg_eq (heL_ne j)]
    exact div_nonneg (heL_sup j k) (norm_nonneg _)
  have hL_edge_sup_succ : ∀ (j : Fin qN) (k : Fin (N + 1)),
      0 ≤ cross (dir (β j)) (r1 k - r1 (L j.succ)) := fun j k => by
    have hid : cross (dir (β j)) (r1 k - r1 (L j.succ)) = cross (dir (β j)) (r1 k - r1 (L j.castSucc)) := by
      have h1 : r1 k - r1 (L j.succ) = (r1 k - r1 (L j.castSucc)) - eL j := by dsimp [eL]; ring
      rw [h1, cross_sub_right, cross_dir_arg_eq (heL_ne j) (w := eL j), cross_self, zero_div, sub_zero]
    rw [hid]; exact hL_edge_sup j k
  have hU_vtx_sup : ∀ (i : ℕ) (hi : i + 1 < pN) (θ : ℝ),
      α ⟨i + 1, hi⟩ ≤ θ → θ ≤ α ⟨i, by omega⟩ →
      ∀ k, cross (dir θ) (r1 k - r1 (U ⟨i + 1, by omega⟩)) ≤ 0 := by
    intro i hi θ hlo hhi k
    have hst := hα_step i hi
    exact cross_dir_le_of_between_both hst.1 hst.2 hlo hhi
      (hU_edge_sup ⟨i + 1, hi⟩ k) (hU_edge_sup_succ ⟨i, by omega⟩ k)
  have hL_vtx_sup : ∀ (j : ℕ) (hj : j + 1 < qN) (θ : ℝ),
      β ⟨j, by omega⟩ ≤ θ → θ ≤ β ⟨j + 1, hj⟩ →
      ∀ k, 0 ≤ cross (dir θ) (r1 k - r1 (L ⟨j + 1, by omega⟩)) := by
    intro j hj θ hlo hhi k
    have hst := hβ_step j hj
    exact cross_dir_ge_of_between_both hst.1 hst.2 hlo hhi
      (hL_edge_sup_succ ⟨j, by omega⟩ k) (hL_edge_sup ⟨j + 1, hj⟩ k)
  have hH_ang_gt : Real.pi / 6 < α ⟨0, by omega⟩ - β ⟨0, by omega⟩ := by
    have hcrH : 0 < cross (eL ⟨0, by omega⟩) (eU ⟨0, by omega⟩) := hcrH_D
    have hsinH : 0 < Real.sin (α ⟨0, by omega⟩ - β ⟨0, by omega⟩) := by
      have h1 : cross (dir (β ⟨0, by omega⟩)) (dir (α ⟨0, by omega⟩)) =
          Real.sin (α ⟨0, by omega⟩ - β ⟨0, by omega⟩) := cross_dir_dir _ _
      have h2 : cross (dir (β ⟨0, by omega⟩)) (dir (α ⟨0, by omega⟩)) =
          cross (eL ⟨0, by omega⟩) (eU ⟨0, by omega⟩) / (‖eL ⟨0, by omega⟩‖ * ‖eU ⟨0, by omega⟩‖) := by
        rw [cross_dir_arg_eq (heL_ne _)]
        have h3 := cross_dir_arg_eq (z := eU ⟨0, by omega⟩) (w := eL ⟨0, by omega⟩) (heU_ne _)
        rw [cross_antisymm (eL _) (dir (α _)), h3, cross_antisymm (eU _) (eL _)]
        have hn1 : ‖eL ⟨0, by omega⟩‖ ≠ 0 := norm_ne_zero_iff.mpr (heL_ne _)
        have hn2 : ‖eU ⟨0, by omega⟩‖ ≠ 0 := norm_ne_zero_iff.mpr (heU_ne _)
        field_simp [hn1, hn2]
      rw [← h1, h2]
      exact div_pos hcrH (mul_pos (norm_pos_iff.mpr (heL_ne _)) (norm_pos_iff.mpr (heU_ne _)))
    have hα0_nn : 0 ≤ α ⟨0, by omega⟩ := by
      apply Complex.arg_nonneg_iff.mpr
      by_cases hp1 : pN = 1
      · have : eU ⟨0, by omega⟩ = r1 kT := by
          change r1 (U ⟨1, by omega⟩) - r1 (U ⟨0, by omega⟩) = r1 kT
          rw [show (⟨1, by omega⟩ : Fin (pN + 1)) = ⟨pN, by omega⟩ from Fin.ext (by simp [hp1]), hU0, hUp, hr1_H, sub_zero]
        rw [this, hr1_T_im]
      · have h1 := hU_im_pos ⟨1, by omega⟩ (by simp) (by simp; omega)
        have : eU ⟨0, by omega⟩ = r1 (U ⟨1, by omega⟩) := by
          change r1 (U ⟨1, by omega⟩) - r1 (U ⟨0, by omega⟩) = _
          rw [hU0, hr1_H, sub_zero]
        rw [this]; exact h1.le
    have hβ0_np : β ⟨0, by omega⟩ ≤ 0 := by
      by_cases hq1' : qN = 1
      · have heq : eL ⟨0, by omega⟩ = r1 kT := by
          change r1 (L ⟨1, by omega⟩) - r1 (L ⟨0, by omega⟩) = r1 kT
          rw [show (⟨1, by omega⟩ : Fin (qN + 1)) = ⟨qN, by omega⟩ from Fin.ext (by simp [hq1']), hL0, hLq, hr1_H, sub_zero]
        dsimp [β]; rw [heq, Complex.arg_eq_zero_iff.mpr ⟨hr1_T_re.le, hr1_T_im⟩]
      · have h1 := hL_im_neg ⟨1, by omega⟩ (by simp) (by simp; omega)
        have heq : eL ⟨0, by omega⟩ = r1 (L ⟨1, by omega⟩) := by
          change r1 (L ⟨1, by omega⟩) - r1 (L ⟨0, by omega⟩) = _
          rw [hL0, hr1_H, sub_zero]
        dsimp [β]; rw [heq]; exact (Complex.arg_neg_iff.mpr h1).le
    have hpos : 0 < α ⟨0, by omega⟩ - β ⟨0, by omega⟩ := by
      by_contra hle; push Not at hle
      have heq : α ⟨0, by omega⟩ - β ⟨0, by omega⟩ = 0 := by linarith
      rw [heq, Real.sin_zero] at hsinH; linarith
    by_contra hle; push Not at hle
    apply huncov1
    apply coveredUnit_of_wedge_and_ball (U := r1 kH) (β := β ⟨0, by omega⟩)
    · intro k; exact (norm_sub_le_polyLen r1 kH k).trans hlen1
    · intro k
      have h0 := hL_edge_sup ⟨0, by omega⟩ k
      rw [Fin.castSucc_mk, hL0] at h0; exact h0
    · intro k
      have hU0' : cross (dir (α ⟨0, by omega⟩)) (r1 k - r1 kH) ≤ 0 := by
        have h0 := hU_edge_sup ⟨0, by omega⟩ k; rw [Fin.castSucc_mk, hU0] at h0; exact h0
      have hL0' : 0 ≤ cross (dir (β ⟨0, by omega⟩)) (r1 k - r1 kH) := by
        have h0 := hL_edge_sup ⟨0, by omega⟩ k; rw [Fin.castSucc_mk, hL0] at h0; exact h0
      exact cross_dir_le_of_between (by linarith) (by linarith) (by linarith [Real.pi_pos]) hL0' hU0'
  have hT_ang_gt : Real.pi / 6 < β ⟨qN - 1, by omega⟩ - α ⟨pN - 1, by omega⟩ := by
    have hcrT : 0 < cross (eU ⟨pN - 1, by omega⟩) (eL ⟨qN - 1, by omega⟩) := hcrT_D
    have hsinT : 0 < Real.sin (β ⟨qN - 1, by omega⟩ - α ⟨pN - 1, by omega⟩) := by
      have h1 : cross (dir (α ⟨pN - 1, by omega⟩)) (dir (β ⟨qN - 1, by omega⟩)) =
          Real.sin (β ⟨qN - 1, by omega⟩ - α ⟨pN - 1, by omega⟩) := cross_dir_dir _ _
      have h2 : cross (dir (α ⟨pN - 1, by omega⟩)) (dir (β ⟨qN - 1, by omega⟩)) =
          cross (eU ⟨pN - 1, by omega⟩) (eL ⟨qN - 1, by omega⟩) /
            (‖eU ⟨pN - 1, by omega⟩‖ * ‖eL ⟨qN - 1, by omega⟩‖) := by
        rw [cross_dir_arg_eq (heU_ne _)]
        have h3 := cross_dir_arg_eq (z := eL ⟨qN - 1, by omega⟩) (w := eU ⟨pN - 1, by omega⟩) (heL_ne _)
        rw [cross_antisymm (eU _) (dir (β _)), h3, cross_antisymm (eL _) (eU _)]
        have hn1 : ‖eU ⟨pN - 1, by omega⟩‖ ≠ 0 := norm_ne_zero_iff.mpr (heU_ne _)
        have hn2 : ‖eL ⟨qN - 1, by omega⟩‖ ≠ 0 := norm_ne_zero_iff.mpr (heL_ne _)
        field_simp [hn1, hn2]
      rw [← h1, h2]
      exact div_pos hcrT (mul_pos (norm_pos_iff.mpr (heU_ne _)) (norm_pos_iff.mpr (heL_ne _)))
    have hαL_np : α ⟨pN - 1, by omega⟩ ≤ 0 := by
      by_cases hp1 : pN = 1
      · have heq : eU ⟨pN - 1, by omega⟩ = r1 kT := by
          change r1 (U ⟨pN - 1 + 1, by omega⟩) - r1 (U ⟨pN - 1, by omega⟩) = r1 kT
          rw [show (⟨pN - 1, by omega⟩ : Fin (pN + 1)) = ⟨0, by omega⟩ from Fin.ext (by simp [hp1]),
            show (⟨pN - 1 + 1, by omega⟩ : Fin (pN + 1)) = ⟨pN, by omega⟩ from Fin.ext (by simp [hp1]),
            hU0, hUp, hr1_H, sub_zero]
        dsimp [α]; rw [heq, Complex.arg_eq_zero_iff.mpr ⟨hr1_T_re.le, hr1_T_im⟩]
      · have h1 := hU_im_pos ⟨pN - 1, by omega⟩ (by simp; omega) (by simp; omega)
        have heq : eU ⟨pN - 1, by omega⟩ = r1 kT - r1 (U ⟨pN - 1, by omega⟩) := by
          change r1 (U ⟨pN - 1 + 1, by omega⟩) - r1 (U ⟨pN - 1, by omega⟩) = _
          rw [show (⟨pN - 1 + 1, by omega⟩ : Fin (pN + 1)) = ⟨pN, by omega⟩ from Fin.ext (by simp; omega), hUp]
        dsimp [α]; rw [heq]
        exact (Complex.arg_neg_iff.mpr (by simp [hr1_T_im]; linarith)).le
    have hβL_nn : 0 ≤ β ⟨qN - 1, by omega⟩ := by
      apply Complex.arg_nonneg_iff.mpr
      by_cases hq1' : qN = 1
      · have : eL ⟨qN - 1, by omega⟩ = r1 kT := by
          change r1 (L ⟨qN - 1 + 1, by omega⟩) - r1 (L ⟨qN - 1, by omega⟩) = r1 kT
          rw [show (⟨qN - 1, by omega⟩ : Fin (qN + 1)) = ⟨0, by omega⟩ from Fin.ext (by simp [hq1']),
            show (⟨qN - 1 + 1, by omega⟩ : Fin (qN + 1)) = ⟨qN, by omega⟩ from Fin.ext (by simp [hq1']),
            hL0, hLq, hr1_H, sub_zero]
        rw [this, hr1_T_im]
      · have h1 := hL_im_neg ⟨qN - 1, by omega⟩ (by simp; omega) (by simp; omega)
        have : eL ⟨qN - 1, by omega⟩ = r1 kT - r1 (L ⟨qN - 1, by omega⟩) := by
          change r1 (L ⟨qN - 1 + 1, by omega⟩) - r1 (L ⟨qN - 1, by omega⟩) = _
          rw [show (⟨qN - 1 + 1, by omega⟩ : Fin (qN + 1)) = ⟨qN, by omega⟩ from Fin.ext (by simp; omega), hLq]
        rw [this]; simp [hr1_T_im]; linarith
    have hpos : 0 < β ⟨qN - 1, by omega⟩ - α ⟨pN - 1, by omega⟩ := by
      by_contra hle; push Not at hle
      have heq : β ⟨qN - 1, by omega⟩ - α ⟨pN - 1, by omega⟩ = 0 := by linarith
      rw [heq, Real.sin_zero] at hsinT; linarith
    by_contra hle; push Not at hle
    apply huncov1
    apply coveredUnit_of_wedge_and_ball (U := r1 kT) (β := α ⟨pN - 1, by omega⟩ + Real.pi)
    · intro k; exact (norm_sub_le_polyLen r1 kT k).trans hlen1
    · intro k
      have hU_last : cross (dir (α ⟨pN - 1, by omega⟩)) (r1 k - r1 kT) ≤ 0 := by
        have hs : (⟨pN - 1, by omega⟩ : Fin pN).succ = ⟨pN, by omega⟩ := Fin.ext (by simp; omega)
        simpa [hs, hUp] using hU_edge_sup_succ ⟨pN - 1, by omega⟩ k
      rw [dir_add, dir_pi, mul_neg, mul_one, cross_neg_left]; linarith
    · intro k
      have hU_last : cross (dir (α ⟨pN - 1, by omega⟩)) (r1 k - r1 kT) ≤ 0 := by
        have hs : (⟨pN - 1, by omega⟩ : Fin pN).succ = ⟨pN, by omega⟩ := Fin.ext (by simp; omega)
        simpa [hs, hUp] using hU_edge_sup_succ ⟨pN - 1, by omega⟩ k
      have hL_last : 0 ≤ cross (dir (β ⟨qN - 1, by omega⟩)) (r1 k - r1 kT) := by
        have hs : (⟨qN - 1, by omega⟩ : Fin qN).succ = ⟨qN, by omega⟩ := Fin.ext (by simp; omega)
        simpa [hs, hLq] using hL_edge_sup_succ ⟨qN - 1, by omega⟩ k
      have h1 : cross (dir (α ⟨pN - 1, by omega⟩ + Real.pi + Real.pi / 6)) (r1 k - r1 kT) =
          -cross (dir (α ⟨pN - 1, by omega⟩ + Real.pi / 6)) (r1 k - r1 kT) := by
        rw [show α ⟨pN - 1, by omega⟩ + Real.pi + Real.pi / 6 = (α ⟨pN - 1, by omega⟩ + Real.pi / 6) + Real.pi by ring,
          dir_add, dir_pi, mul_neg, mul_one, cross_neg_left]
      rw [h1]
      have hU' : 0 ≤ cross (dir (α ⟨pN - 1, by omega⟩)) (-(r1 k - r1 kT)) := by rw [cross_neg_right]; linarith
      have hL' : cross (dir (β ⟨qN - 1, by omega⟩)) (-(r1 k - r1 kT)) ≤ 0 := by rw [cross_neg_right]; linarith
      have hres := cross_dir_le_of_between (θ₃ := α ⟨pN - 1, by omega⟩ + Real.pi / 6)
        (by linarith) (by linarith) (by linarith [Real.pi_pos]) hU' hL'
      rw [cross_neg_right] at hres; linarith
  have hdot_eL : ∀ j : Fin qN, 0 < dotC (dir (β j)) (r1 (L j.succ) - r1 (L j.castSucc)) := fun j => by
    change 0 < dotC (dir (β j)) (eL j)
    have h1 := dir_arg_eq_smul (eL j)
    conv_rhs => rw [h1]
    rw [dotC_smul_right, dotC_dir_dir, sub_self, Real.cos_zero, mul_one]
    exact norm_pos_iff.mpr (heL_ne j)
  have hdot_eU : ∀ i : Fin pN, 0 < dotC (dir (α i)) (r1 (U i.succ) - r1 (U i.castSucc)) := fun i => by
    change 0 < dotC (dir (α i)) (eU i)
    have h1 := dir_arg_eq_smul (eU i)
    conv_rhs => rw [h1]
    rw [dotC_smul_right, dotC_dir_dir, sub_self, Real.cos_zero, mul_one]
    exact norm_pos_iff.mpr (heU_ne i)
  have hcr_eL : ∀ j : Fin qN, cross (dir (β j)) (r1 (L j.succ) - r1 (L j.castSucc)) = 0 := fun j => by
    change cross (dir (β j)) (eL j) = 0
    rw [cross_dir_arg_eq (heL_ne j), cross_self, zero_div]
  have hcr_eU : ∀ i : Fin pN, cross (dir (α i)) (r1 (U i.succ) - r1 (U i.castSucc)) = 0 := fun i => by
    change cross (dir (α i)) (eU i) = 0
    rw [cross_dir_arg_eq (heU_ne i), cross_self, zero_div]
  exact ⟨{
    pN := pN, qN := qN, hpN1 := hpN1, hqN1 := hqN1, hsum3 := hsum3,
    U := U, L := L, hU0_L0 := hU0.trans hL0.symm, hUp_Lq := hUp.trans hLq.symm,
    hU_mono := hU_mono, hL_mono := hL_mono, hUL_ne := hUL_ne,
    α := α, β := β, hα_anti := hα_anti, hβ_mono := hβ_mono,
    hU_edge_sup := hU_edge_sup, hL_edge_sup := hL_edge_sup,
    hU_vtx_sup := hU_vtx_sup, hL_vtx_sup := hL_vtx_sup,
    hcr_eU := hcr_eU, hdot_eU := hdot_eU, hcr_eL := hcr_eL, hdot_eL := hdot_eL,
    hH_ang_gt := hH_ang_gt, hT_ang_gt := hT_ang_gt }⟩

theorem extract_two_wedge_case {N : ℕ} {r : Fin (N + 1) → ℂ} (hN : 2 ≤ N)
    (hgp : GenPos r) (hsimp : IsSimplePoly r) (hlen : polyLen r ≤ 1) (huncov : ¬ CoveredUnit r) :
    ∃ (r' : Fin (N + 1) → ℂ) (W : TwoWedgeBase r'),
      GenPos r' ∧ IsSimplePoly r' ∧ polyLen r' ≤ 1 ∧ ¬ CoveredUnit r' ∧
      (IsCase1 W ∨ IsCase3 W ∨ IsCase24 W) := by
  obtain ⟨r1, hgp1, hsimp1, hlen1, huncov1, ⟨D⟩⟩ := extract_hull_mono hN hgp hsimp hlen huncov
  obtain ⟨C⟩ := extract_hull_chains hgp1 hlen1 huncov1 D
  rcases C with ⟨pN, qN, hpN1, hqN1, hsum3, U, L, hU0_L0, hUp_Lq, hU_mono, hL_mono, hUL_ne,
    α, β, hα_anti, hβ_mono, hU_edge_sup, hL_edge_sup, hU_vtx_sup, hL_vtx_sup,
    hcr_eU, hdot_eU, hcr_eL, hdot_eL, hH_ang_gt, hT_ang_gt⟩
  let M : ℕ := pN + qN - 2
  have hM_pos : 1 ≤ M := by omega
  let stepFn : ℕ × ℕ → ℕ × ℕ := fun ⟨i, j⟩ =>
    if hi : i + 1 < pN then
      if hj : j + 1 < qN then
        if U ⟨i + 1, by omega⟩ < L ⟨j + 1, by omega⟩ then (i + 1, j) else (i, j + 1)
      else (i + 1, j)
    else (i, j + 1)
  let steps : ℕ → ℕ × ℕ := fun k => stepFn^[k] (0, 0)
  have hsteps_succ : ∀ k, steps (k + 1) = stepFn (steps k) := fun k =>
    Function.iterate_succ_apply' stepFn k (0, 0)
  have hsteps_bounds : ∀ k, k ≤ M →
      (steps k).1 + (steps k).2 = k ∧ (steps k).1 < pN ∧ (steps k).2 < qN := by
    intro k
    induction k with
    | zero => intro _; change 0 + 0 = 0 ∧ 0 < pN ∧ 0 < qN; omega
    | succ k ih =>
      intro hk
      obtain ⟨hsum, hi_lt, hj_lt⟩ := ih (by omega)
      rw [hsteps_succ]
      set i := (steps k).1; set j := (steps k).2
      change (stepFn (i, j)).1 + (stepFn (i, j)).2 = k + 1 ∧ (stepFn (i, j)).1 < pN ∧ (stepFn (i, j)).2 < qN
      dsimp only [stepFn]
      split_ifs <;> simp <;> omega
  have hsteps_order : ∀ k (hk : k ≤ M),
      U ⟨(steps k).1, Nat.lt_succ_of_lt (hsteps_bounds k hk).2.1⟩ <
        L ⟨(steps k).2 + 1, Nat.succ_lt_succ (hsteps_bounds k hk).2.2⟩ ∧
      L ⟨(steps k).2, Nat.lt_succ_of_lt (hsteps_bounds k hk).2.2⟩ <
        U ⟨(steps k).1 + 1, Nat.succ_lt_succ (hsteps_bounds k hk).2.1⟩ := by
    intro k
    induction k with
    | zero =>
      intro _
      constructor
      · change U ⟨0, by omega⟩ < L ⟨1, by omega⟩
        rw [hU0_L0]; exact hL_mono (show (⟨0, by omega⟩ : Fin (qN + 1)) < ⟨1, by omega⟩ by simp [Fin.lt_def])
      · change L ⟨0, by omega⟩ < U ⟨1, by omega⟩
        rw [← hU0_L0]; exact hU_mono (show (⟨0, by omega⟩ : Fin (pN + 1)) < ⟨1, by omega⟩ by simp [Fin.lt_def])
    | succ k ih =>
      intro hk
      obtain ⟨hsum, hi_lt, hj_lt⟩ := hsteps_bounds k (by omega)
      obtain ⟨hUL, hLU⟩ := ih (by omega)
      set i := (steps k).1; set j := (steps k).2
      have hst : steps (k + 1) = stepFn (i, j) := hsteps_succ k
      have hstep_sub : ∀ a b (ha : a < pN) (hb : b < qN),
          steps (k + 1) = (a, b) →
          U ⟨a, Nat.lt_succ_of_lt ha⟩ < L ⟨b + 1, Nat.succ_lt_succ hb⟩ →
          L ⟨b, Nat.lt_succ_of_lt hb⟩ < U ⟨a + 1, Nat.succ_lt_succ ha⟩ →
          U ⟨(steps (k + 1)).1, Nat.lt_succ_of_lt (hsteps_bounds (k + 1) hk).2.1⟩ <
            L ⟨(steps (k + 1)).2 + 1, Nat.succ_lt_succ (hsteps_bounds (k + 1) hk).2.2⟩ ∧
          L ⟨(steps (k + 1)).2, Nat.lt_succ_of_lt (hsteps_bounds (k + 1) hk).2.2⟩ <
            U ⟨(steps (k + 1)).1 + 1, Nat.succ_lt_succ (hsteps_bounds (k + 1) hk).2.1⟩ := by
        intro a b ha hb heq h1 h2
        have h1' : (steps (k + 1)).1 = a := congrArg Prod.fst heq
        have h2' : (steps (k + 1)).2 = b := congrArg Prod.snd heq
        constructor
        · convert h1 using 2 <;> exact Fin.ext (by simp [h1', h2'])
        · convert h2 using 2 <;> exact Fin.ext (by simp [h1', h2'])
      dsimp only [stepFn] at hst
      by_cases hi : i + 1 < pN
      · rw [dif_pos hi] at hst
        by_cases hj : j + 1 < qN
        · rw [dif_pos hj] at hst
          by_cases hcmp : U ⟨i + 1, by omega⟩ < L ⟨j + 1, by omega⟩
          · rw [if_pos hcmp] at hst
            exact hstep_sub (i + 1) j hi hj_lt hst hcmp
              (lt_trans hLU (hU_mono (show (⟨i + 1, by omega⟩ : Fin (pN + 1)) < ⟨i + 2, by omega⟩ by simp [Fin.lt_def])))
          · rw [if_neg hcmp] at hst
            have hlt : L ⟨j + 1, by omega⟩ < U ⟨i + 1, by omega⟩ :=
              lt_of_le_of_ne (not_lt.mp hcmp)
                (hUL_ne ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ (by simp) (by simp; omega) (by simp) (by simp; omega)).symm
            exact hstep_sub i (j + 1) hi_lt hj hst
              (lt_trans hUL (hL_mono (show (⟨j + 1, by omega⟩ : Fin (qN + 1)) < ⟨j + 2, by omega⟩ by simp [Fin.lt_def]))) hlt
        · rw [dif_neg hj] at hst
          have hj_eq : j + 1 = qN := by omega
          have hUq : U ⟨i + 1, by omega⟩ < L ⟨j + 1, by omega⟩ := by
            rw [show (⟨j + 1, by omega⟩ : Fin (qN + 1)) = ⟨qN, by omega⟩ from Fin.ext hj_eq, ← hUp_Lq]
            exact hU_mono (show (⟨i + 1, by omega⟩ : Fin (pN + 1)) < ⟨pN, by omega⟩ by simp [Fin.lt_def]; omega)
          exact hstep_sub (i + 1) j hi hj_lt hst hUq
            (lt_trans hLU (hU_mono (show (⟨i + 1, by omega⟩ : Fin (pN + 1)) < ⟨i + 2, by omega⟩ by simp [Fin.lt_def])))
      · rw [dif_neg hi] at hst
        have hi_eq : i + 1 = pN := by omega
        have hj : j + 1 < qN := by omega
        have hLp : L ⟨j + 1, by omega⟩ < U ⟨i + 1, by omega⟩ := by
          rw [show (⟨i + 1, by omega⟩ : Fin (pN + 1)) = ⟨pN, by omega⟩ from Fin.ext hi_eq, hUp_Lq]
          exact hL_mono (show (⟨j + 1, by omega⟩ : Fin (qN + 1)) < ⟨qN, by omega⟩ by simp [Fin.lt_def]; omega)
        exact hstep_sub i (j + 1) hi_lt hj hst
          (lt_trans hUL (hL_mono (show (⟨j + 1, by omega⟩ : Fin (qN + 1)) < ⟨j + 2, by omega⟩ by simp [Fin.lt_def]))) hLp
  let seqA (k : ℕ) : ℝ :=
    if hk : k ≤ M then
      α ⟨(steps k).1, (hsteps_bounds k hk).2.1⟩ - β ⟨(steps k).2, (hsteps_bounds k hk).2.2⟩
    else 0
  have hseqA_0 : Real.pi / 6 < seqA 0 := by
    simp only [seqA, Nat.zero_le, ↓reduceDIte, steps, Function.iterate_zero_apply]; exact hH_ang_gt
  have hseqA_M : seqA M < -(Real.pi / 6) := by
    simp only [seqA, le_rfl, ↓reduceDIte]
    have hinv := hsteps_bounds M le_rfl
    have h1 : (⟨(steps M).1, hinv.2.1⟩ : Fin pN) = ⟨pN - 1, by omega⟩ := Fin.ext (by simp; omega)
    have h2 : (⟨(steps M).2, hinv.2.2⟩ : Fin qN) = ⟨qN - 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [h1, h2]; linarith [hT_ang_gt]
  have hseqA_step : ∀ k, k < M → seqA (k + 1) < seqA k := by
    intro k hk
    simp only [seqA, show k ≤ M by omega, show k + 1 ≤ M by omega, ↓reduceDIte]
    have hst : steps (k + 1) = stepFn (steps k) := hsteps_succ k
    set i := (steps k).1
    set j := (steps k).2
    have hinv := hsteps_bounds k (by omega)
    dsimp only [stepFn] at hst
    have hdec_i : ∀ (hi : i + 1 < pN), steps (k + 1) = (i + 1, j) →
        α ⟨(steps (k + 1)).1, (hsteps_bounds (k + 1) (by omega)).2.1⟩ -
          β ⟨(steps (k + 1)).2, (hsteps_bounds (k + 1) (by omega)).2.2⟩ <
        α ⟨i, hinv.2.1⟩ - β ⟨j, hinv.2.2⟩ := by
      intro hi heq
      have h1 : (⟨(steps (k + 1)).1, (hsteps_bounds (k + 1) (by omega)).2.1⟩ : Fin pN) = ⟨i + 1, hi⟩ :=
        Fin.ext (by simpa [i] using congrArg Prod.fst heq)
      have h2 : (⟨(steps (k + 1)).2, (hsteps_bounds (k + 1) (by omega)).2.2⟩ : Fin qN) = ⟨j, hinv.2.2⟩ :=
        Fin.ext (by simpa [j] using congrArg Prod.snd heq)
      rw [h1, h2]; linarith [hα_anti (show (⟨i, hinv.2.1⟩ : Fin pN) < ⟨i + 1, hi⟩ by simp)]
    have hdec_j : ∀ (hj : j + 1 < qN), steps (k + 1) = (i, j + 1) →
        α ⟨(steps (k + 1)).1, (hsteps_bounds (k + 1) (by omega)).2.1⟩ -
          β ⟨(steps (k + 1)).2, (hsteps_bounds (k + 1) (by omega)).2.2⟩ <
        α ⟨i, hinv.2.1⟩ - β ⟨j, hinv.2.2⟩ := by
      intro hj heq
      have h1 : (⟨(steps (k + 1)).1, (hsteps_bounds (k + 1) (by omega)).2.1⟩ : Fin pN) = ⟨i, hinv.2.1⟩ :=
        Fin.ext (by simpa [i] using congrArg Prod.fst heq)
      have h2 : (⟨(steps (k + 1)).2, (hsteps_bounds (k + 1) (by omega)).2.2⟩ : Fin qN) = ⟨j + 1, hj⟩ :=
        Fin.ext (by simpa [j] using congrArg Prod.snd heq)
      rw [h1, h2]; linarith [hβ_mono (show (⟨j, hinv.2.2⟩ : Fin qN) < ⟨j + 1, hj⟩ by simp)]
    by_cases hi : i + 1 < pN
    · rw [dif_pos hi] at hst
      by_cases hj : j + 1 < qN
      · rw [dif_pos hj] at hst
        by_cases hcmp : U ⟨i + 1, by omega⟩ < L ⟨j + 1, by omega⟩
        · rw [if_pos hcmp] at hst; exact hdec_i hi hst
        · rw [if_neg hcmp] at hst; exact hdec_j hj hst
      · rw [dif_neg hj] at hst; exact hdec_i hi hst
    · rw [dif_neg hi] at hst; exact hdec_j (by omega) hst
  have hseqA_anti : ∀ k1 k2, k1 ≤ k2 → k2 ≤ M → seqA k2 ≤ seqA k1 := by
    intro k1 k2 h12 h2M
    induction h12 with
    | refl => exact le_rfl
    | @step m h1m ih => exact (hseqA_step m (by omega)).le.trans (ih (by omega))
  have hex_cross : ∀ (c : ℝ), seqA M < c → c < seqA 0 →
      ∃ k < M, seqA (k + 1) ≤ c ∧ c < seqA k := by
    intro c hM_lt h0_gt
    have hex : ∃ n, n ≤ M ∧ seqA n ≤ c := ⟨M, le_rfl, hM_lt.le⟩
    let n := Nat.find hex
    have hn : n ≤ M ∧ seqA n ≤ c := Nat.find_spec hex
    have hn_pos : 0 < n := by
      by_contra h0
      have hn0 : n = 0 := by omega
      rw [hn0] at hn; linarith
    refine ⟨n - 1, by omega, ?_, ?_⟩
    · have hm_eq : n - 1 + 1 = n := by omega
      rw [hm_eq]; exact hn.2
    · by_contra hle; push Not at hle
      exact Nat.find_min hex (show n - 1 < n by omega) ⟨by omega, hle⟩
  obtain ⟨k1, hk1_lt, hk1_hi, hk1_lo⟩ := hex_cross (Real.pi / 6) (by linarith [Real.pi_pos]) hseqA_0
  have hex_cross2 : ∃ k < M, seqA (k + 1) < -(Real.pi / 6) ∧ -(Real.pi / 6) ≤ seqA k := by
    have hex : ∃ n, n ≤ M ∧ seqA n < -(Real.pi / 6) := ⟨M, le_rfl, hseqA_M⟩
    let n := Nat.find hex
    have hn : n ≤ M ∧ seqA n < -(Real.pi / 6) := Nat.find_spec hex
    have hn_pos : 0 < n := by
      by_contra h0
      have hn0 : n = 0 := by omega
      rw [hn0] at hn; linarith [Real.pi_pos]
    refine ⟨n - 1, by omega, ?_, ?_⟩
    · have hm_eq : n - 1 + 1 = n := by omega
      rw [hm_eq]; exact hn.2
    · by_contra hlt; push Not at hlt
      exact Nat.find_min hex (show n - 1 < n by omega) ⟨by omega, hlt⟩
  obtain ⟨k2, hk2_lt, hk2_hi, hk2_lo⟩ := hex_cross2
  have hk12 : k1 ≤ k2 := by
    by_contra hgt; push Not at hgt
    have h1 := hseqA_anti (k2 + 1) k1 (by omega) (by omega)
    linarith [Real.pi_pos]
  have hsteps_mono : ∀ a b, a ≤ b → b ≤ M → (steps a).1 ≤ (steps b).1 ∧ (steps a).2 ≤ (steps b).2 := by
    intro a b hab hbM
    induction hab with
    | refl => exact ⟨le_rfl, le_rfl⟩
    | @step m ham ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [hsteps_succ]; dsimp only [stepFn]; split_ifs <;> omega
  have hstep_dich : ∀ k (hk : k < M),
      ((steps (k + 1) = ((steps k).1 + 1, (steps k).2) ∧ (steps k).1 + 1 < pN ∧
        L ⟨(steps k).2, Nat.lt_succ_of_lt (hsteps_bounds k hk.le).2.2⟩ <
          U ⟨(steps k).1 + 1, Nat.succ_lt_succ (hsteps_bounds k hk.le).2.1⟩ ∧
        U ⟨(steps k).1 + 1, Nat.succ_lt_succ (hsteps_bounds k hk.le).2.1⟩ <
          L ⟨(steps k).2 + 1, Nat.succ_lt_succ (hsteps_bounds k hk.le).2.2⟩) ∨
       (steps (k + 1) = ((steps k).1, (steps k).2 + 1) ∧ (steps k).2 + 1 < qN ∧
        U ⟨(steps k).1, Nat.lt_succ_of_lt (hsteps_bounds k hk.le).2.1⟩ <
          L ⟨(steps k).2 + 1, Nat.succ_lt_succ (hsteps_bounds k hk.le).2.2⟩ ∧
        L ⟨(steps k).2 + 1, Nat.succ_lt_succ (hsteps_bounds k hk.le).2.2⟩ <
          U ⟨(steps k).1 + 1, Nat.succ_lt_succ (hsteps_bounds k hk.le).2.1⟩)) := by
    intro k hk
    have hb := hsteps_bounds k hk.le
    have hord := hsteps_order k hk.le
    have hord1 := hsteps_order (k + 1) (by omega)
    have hst : steps (k + 1) = stepFn (steps k) := hsteps_succ k
    dsimp only [stepFn] at hst
    by_cases hi : (steps k).1 + 1 < pN
    · rw [dif_pos hi] at hst
      by_cases hj : (steps k).2 + 1 < qN
      · rw [dif_pos hj] at hst
        by_cases hcmp : U ⟨(steps k).1 + 1, by omega⟩ < L ⟨(steps k).2 + 1, by omega⟩
        · rw [if_pos hcmp] at hst; exact Or.inl ⟨hst, hi, hord.2, hcmp⟩
        · rw [if_neg hcmp] at hst
          have hlt : L ⟨(steps k).2 + 1, Nat.succ_lt_succ hb.2.2⟩ < U ⟨(steps k).1 + 1, Nat.succ_lt_succ hb.2.1⟩ := by
            have h1 := congrArg Prod.fst hst; have h2 := congrArg Prod.snd hst
            convert hord1.2 using 2 <;> exact Fin.ext (by simp [h1, h2])
          exact Or.inr ⟨hst, hj, hord.1, hlt⟩
      · rw [dif_neg hj] at hst
        have hlt : U ⟨(steps k).1 + 1, Nat.succ_lt_succ hb.2.1⟩ < L ⟨(steps k).2 + 1, Nat.succ_lt_succ hb.2.2⟩ := by
          have h1 := congrArg Prod.fst hst; have h2 := congrArg Prod.snd hst
          convert hord1.1 using 2 <;> exact Fin.ext (by simp [h1, h2])
        exact Or.inl ⟨hst, hi, hord.2, hlt⟩
    · rw [dif_neg hi] at hst
      have hlt : L ⟨(steps k).2 + 1, Nat.succ_lt_succ hb.2.2⟩ < U ⟨(steps k).1 + 1, Nat.succ_lt_succ hb.2.1⟩ := by
        have h1 := congrArg Prod.fst hst; have h2 := congrArg Prod.snd hst
        convert hord1.2 using 2 <;> exact Fin.ext (by simp [h1, h2])
      exact Or.inr ⟨hst, by omega, hord.1, hlt⟩
  let i1 := (steps k1).1; let j1 := (steps k1).2
  let i2 := (steps k2).1; let j2 := (steps k2).2
  have hi1_lt : i1 < pN := (hsteps_bounds k1 hk1_lt.le).2.1
  have hj1_lt : j1 < qN := (hsteps_bounds k1 hk1_lt.le).2.2
  have hi2_lt : i2 < pN := (hsteps_bounds k2 hk2_lt.le).2.1
  have hj2_lt : j2 < qN := (hsteps_bounds k2 hk2_lt.le).2.2
  have hi12 : i1 ≤ i2 := (hsteps_mono k1 k2 hk12 hk2_lt.le).1
  have hj12 : j1 ≤ j2 := (hsteps_mono k1 k2 hk12 hk2_lt.le).2
  have hseq1_lo : Real.pi / 6 < α ⟨i1, hi1_lt⟩ - β ⟨j1, hj1_lt⟩ := by
    simpa only [seqA, show k1 ≤ M by omega, ↓reduceDIte, i1, j1] using hk1_lo
  have hseq2_lo : -(Real.pi / 6) ≤ α ⟨i2, hi2_lt⟩ - β ⟨j2, hj2_lt⟩ := by
    simpa only [seqA, show k2 ≤ M by omega, ↓reduceDIte, i2, j2] using hk2_lo
  rcases hstep_dich k1 hk1_lt with ⟨h1_eq, hi1_succ, h1_LU, h1_UL⟩ | ⟨h1_eq, hj1_succ, h1_UL, h1_LU⟩
  · have hseq1_hi : α ⟨i1 + 1, hi1_succ⟩ - β ⟨j1, hj1_lt⟩ ≤ Real.pi / 6 := by
      have h := hk1_hi
      simp only [seqA, show k1 + 1 ≤ M by omega, ↓reduceDIte] at h
      have h1_p1 : (steps (k1 + 1)).1 = i1 + 1 := by simpa [i1] using congrArg Prod.fst h1_eq
      have h1_p2 : (steps (k1 + 1)).2 = j1 := by simpa [j1] using congrArg Prod.snd h1_eq
      have hf1 : (⟨(steps (k1 + 1)).1, (hsteps_bounds (k1 + 1) (by omega)).2.1⟩ : Fin pN) = ⟨i1 + 1, hi1_succ⟩ :=
        Fin.ext h1_p1
      have hf2 : (⟨(steps (k1 + 1)).2, (hsteps_bounds (k1 + 1) (by omega)).2.2⟩ : Fin qN) = ⟨j1, hj1_lt⟩ :=
        Fin.ext h1_p2
      rw [hf1, hf2] at h; exact h
    let βU := β ⟨j1, hj1_lt⟩
    let αU := βU + Real.pi / 6
    have hUtop_sup : ∀ k, cross (dir αU) (r1 k - r1 (U ⟨i1 + 1, by omega⟩)) ≤ 0 :=
      hU_vtx_sup i1 hi1_succ αU (by dsimp [αU, βU]; linarith) (by dsimp [αU, βU]; linarith)
    rcases hstep_dich k2 hk2_lt with ⟨h2_eq, hi2_succ, h2_LU, h2_UL⟩ | ⟨h2_eq, hj2_succ, h2_UL, h2_LU⟩
    · have hseq2_hi : α ⟨i2 + 1, hi2_succ⟩ - β ⟨j2, hj2_lt⟩ < -(Real.pi / 6) := by
        have h := hk2_hi
        simp only [seqA, show k2 + 1 ≤ M by omega, ↓reduceDIte] at h
        have h2_p1 : (steps (k2 + 1)).1 = i2 + 1 := by simpa [i2] using congrArg Prod.fst h2_eq
        have h2_p2 : (steps (k2 + 1)).2 = j2 := by simpa [j2] using congrArg Prod.snd h2_eq
        have hf1 : (⟨(steps (k2 + 1)).1, (hsteps_bounds (k2 + 1) (by omega)).2.1⟩ : Fin pN) = ⟨i2 + 1, hi2_succ⟩ :=
          Fin.ext h2_p1
        have hf2 : (⟨(steps (k2 + 1)).2, (hsteps_bounds (k2 + 1) (by omega)).2.2⟩ : Fin qN) = ⟨j2, hj2_lt⟩ :=
          Fin.ext h2_p2
        rw [hf1, hf2] at h; exact h
      let βV := β ⟨j2, hj2_lt⟩
      let αV := βV - Real.pi / 6
      have hVtop_sup : ∀ k, cross (dir αV) (r1 k - r1 (U ⟨i2 + 1, by omega⟩)) ≤ 0 :=
        hU_vtx_sup i2 hi2_succ αV (by dsimp [αV, βV]; linarith) (by dsimp [αV, βV]; linarith)
      have hδb : 0 ≤ βV - βU := by
        dsimp [βV, βU]
        rcases eq_or_lt_of_le hj12 with heq | hlt
        · have : (⟨j1, hj1_lt⟩ : Fin qN) = ⟨j2, hj2_lt⟩ := Fin.ext heq; rw [this, sub_self]
        · exact (sub_pos.mpr (hβ_mono (show (⟨j1, hj1_lt⟩ : Fin qN) < ⟨j2, hj2_lt⟩ from hlt))).le
      have hδt : 0 ≤ αU - αV := by
        rcases eq_or_lt_of_le hk12 with rfl | hlt12
        · dsimp [αU, αV, βU, βV]; linarith [Real.pi_pos]
        · have hi_le : i1 + 1 ≤ i2 := by
            have hm := (hsteps_mono (k1 + 1) k2 (by omega) (by omega)).1
            rw [congrArg Prod.fst h1_eq] at hm; exact hm
          have hα_cmp : α ⟨i2, hi2_lt⟩ ≤ α ⟨i1 + 1, hi1_succ⟩ := by
            rcases eq_or_lt_of_le hi_le with heq | hlt
            · have : (⟨i2, hi2_lt⟩ : Fin pN) = ⟨i1 + 1, hi1_succ⟩ := Fin.ext heq.symm; rw [this]
            · exact (hα_anti (show (⟨i1 + 1, hi1_succ⟩ : Fin pN) < ⟨i2, hi2_lt⟩ from hlt)).le
          dsimp [αU, αV, βU, βV]; linarith
      apply solve_raw_two_wedge r1 hgp1 hsimp1 hlen1 huncov1 βU αU βV αV rfl (by dsimp [αV]; ring) hδt hδb
        (L ⟨j1, by omega⟩) (U ⟨i1 + 1, by omega⟩) (L ⟨j1 + 1, by omega⟩) h1_LU h1_UL
        (hL_edge_sup ⟨j1, hj1_lt⟩) (hcr_eL ⟨j1, hj1_lt⟩) (hdot_eL ⟨j1, hj1_lt⟩) hUtop_sup
      left
      refine ⟨L ⟨j2, by omega⟩, U ⟨i2 + 1, by omega⟩, L ⟨j2 + 1, by omega⟩, h2_LU, h2_UL, ?_,
        hL_edge_sup ⟨j2, hj2_lt⟩, hcr_eL ⟨j2, hj2_lt⟩, hdot_eL ⟨j2, hj2_lt⟩, hVtop_sup, ?_⟩
      · exact hU_mono.monotone (show (⟨i1 + 1, by omega⟩ : Fin (pN + 1)) ≤ ⟨i2 + 1, by omega⟩ by simp; omega)
      · rcases eq_or_lt_of_le hj12 with heq | hlt
        · left
          have hjeq : (⟨j1, hj1_lt⟩ : Fin qN) = ⟨j2, hj2_lt⟩ := Fin.ext heq
          refine ⟨by dsimp [βU, βV]; rw [hjeq], congrArg L (Fin.ext heq.symm),
            congrArg L (Fin.ext (by simp [heq]))⟩
        · right
          exact hL_mono.monotone (show (⟨j1 + 1, by omega⟩ : Fin (qN + 1)) ≤ ⟨j2, by omega⟩ by simp; omega)
    · have hseq2_hi : α ⟨i2, hi2_lt⟩ - β ⟨j2 + 1, hj2_succ⟩ < -(Real.pi / 6) := by
        have h := hk2_hi
        simp only [seqA, show k2 + 1 ≤ M by omega, ↓reduceDIte] at h
        have h2_p1 : (steps (k2 + 1)).1 = i2 := by simpa [i2] using congrArg Prod.fst h2_eq
        have h2_p2 : (steps (k2 + 1)).2 = j2 + 1 := by simpa [j2] using congrArg Prod.snd h2_eq
        have hf1 : (⟨(steps (k2 + 1)).1, (hsteps_bounds (k2 + 1) (by omega)).2.1⟩ : Fin pN) = ⟨i2, hi2_lt⟩ :=
          Fin.ext h2_p1
        have hf2 : (⟨(steps (k2 + 1)).2, (hsteps_bounds (k2 + 1) (by omega)).2.2⟩ : Fin qN) = ⟨j2 + 1, hj2_succ⟩ :=
          Fin.ext h2_p2
        rw [hf1, hf2] at h; exact h
      have hk12_lt : k1 < k2 := by
        rcases eq_or_lt_of_le hk12 with rfl | hlt
        · exfalso; have h := congrArg Prod.fst (h1_eq.symm.trans h2_eq); simp at h
        · exact hlt
      have hi1_le : i1 + 1 ≤ i2 := by
        have hm := (hsteps_mono (k1 + 1) k2 (by omega) (by omega)).1
        rw [congrArg Prod.fst h1_eq] at hm; exact hm
      let αV := α ⟨i2, hi2_lt⟩
      let βV := αV + Real.pi / 6
      have hVbot_sup : ∀ k, 0 ≤ cross (dir βV) (r1 k - r1 (L ⟨j2 + 1, by omega⟩)) :=
        hL_vtx_sup j2 hj2_succ βV (by dsimp [αV, βV]; linarith) (by dsimp [αV, βV]; linarith)
      have hδt : 0 ≤ αU - αV := by
        have hα_cmp : α ⟨i2, hi2_lt⟩ ≤ α ⟨i1 + 1, hi1_succ⟩ := by
          rcases eq_or_lt_of_le hi1_le with heq | hlt
          · have : (⟨i2, hi2_lt⟩ : Fin pN) = ⟨i1 + 1, hi1_succ⟩ := Fin.ext heq.symm; rw [this]
          · exact (hα_anti (show (⟨i1 + 1, hi1_succ⟩ : Fin pN) < ⟨i2, hi2_lt⟩ from hlt)).le
        dsimp [αU, αV, βU]; linarith
      have hδb : 0 ≤ βV - βU := by
        have hβ_cmp : β ⟨j1, hj1_lt⟩ ≤ β ⟨j2, hj2_lt⟩ := by
          rcases eq_or_lt_of_le hj12 with heq | hlt
          · have : (⟨j1, hj1_lt⟩ : Fin qN) = ⟨j2, hj2_lt⟩ := Fin.ext heq; rw [this]
          · exact (hβ_mono (show (⟨j1, hj1_lt⟩ : Fin qN) < ⟨j2, hj2_lt⟩ from hlt)).le
        dsimp [βV, αV, βU]; linarith
      apply solve_raw_two_wedge r1 hgp1 hsimp1 hlen1 huncov1 βU αU βV αV rfl rfl hδt hδb
        (L ⟨j1, by omega⟩) (U ⟨i1 + 1, by omega⟩) (L ⟨j1 + 1, by omega⟩) h1_LU h1_UL
        (hL_edge_sup ⟨j1, hj1_lt⟩) (hcr_eL ⟨j1, hj1_lt⟩) (hdot_eL ⟨j1, hj1_lt⟩) hUtop_sup
      right
      refine ⟨U ⟨i2, by omega⟩, L ⟨j2 + 1, by omega⟩, U ⟨i2 + 1, by omega⟩, h2_UL, h2_LU,
        hU_mono.monotone (show (⟨i1 + 1, by omega⟩ : Fin (pN + 1)) ≤ ⟨i2, by omega⟩ by simp; omega),
        hL_mono.monotone (show (⟨j1 + 1, by omega⟩ : Fin (qN + 1)) ≤ ⟨j2 + 1, by omega⟩ by simp; omega),
        hU_edge_sup ⟨i2, hi2_lt⟩, hcr_eU ⟨i2, hi2_lt⟩, hdot_eU ⟨i2, hi2_lt⟩, hVbot_sup⟩
  · let r2 : Fin (N + 1) → ℂ := fun k => starRingEnd ℂ (r1 k)
    have hgp2 : GenPos r2 := genPos_of_conj hgp1
    have hsimp2 : IsSimplePoly r2 := isSimplePoly_of_conj hsimp1
    have hlen2 : polyLen r2 ≤ 1 := by rw [polyLen_of_conj]; exact hlen1
    have huncov2 : ¬ CoveredUnit r2 := fun h => huncov1 (coveredUnit_of_conj h)
    have hcr_conj : ∀ (φ : ℝ) (a b : Fin (N + 1)),
        cross (dir (-φ)) (r2 a - r2 b) = -cross (dir φ) (r1 a - r1 b) := fun φ a b => by
      dsimp [r2]; rw [dir_neg, ← map_sub, cross_conj]
    have hdot_conj : ∀ (φ : ℝ) (a b : Fin (N + 1)),
        dotC (dir (-φ)) (r2 a - r2 b) = dotC (dir φ) (r1 a - r1 b) := fun φ a b => by
      dsimp [r2]; rw [dir_neg, ← map_sub, dotC_conj]
    have hseq1_hi : α ⟨i1, hi1_lt⟩ - β ⟨j1 + 1, hj1_succ⟩ ≤ Real.pi / 6 := by
      have h := hk1_hi
      simp only [seqA, show k1 + 1 ≤ M by omega, ↓reduceDIte] at h
      have h1_p1 : (steps (k1 + 1)).1 = i1 := by simpa [i1] using congrArg Prod.fst h1_eq
      have h1_p2 : (steps (k1 + 1)).2 = j1 + 1 := by simpa [j1] using congrArg Prod.snd h1_eq
      have hf1 : (⟨(steps (k1 + 1)).1, (hsteps_bounds (k1 + 1) (by omega)).2.1⟩ : Fin pN) = ⟨i1, hi1_lt⟩ :=
        Fin.ext h1_p1
      have hf2 : (⟨(steps (k1 + 1)).2, (hsteps_bounds (k1 + 1) (by omega)).2.2⟩ : Fin qN) = ⟨j1 + 1, hj1_succ⟩ :=
        Fin.ext h1_p2
      rw [hf1, hf2] at h; exact h
    let βU := -(α ⟨i1, hi1_lt⟩)
    let αU := βU + Real.pi / 6
    have hUbot_sup : ∀ k, 0 ≤ cross (dir βU) (r2 k - r2 (U ⟨i1, by omega⟩)) := fun k => by
      dsimp [βU]; rw [hcr_conj]
      have h := hU_edge_sup ⟨i1, hi1_lt⟩ k; rw [Fin.castSucc_mk] at h; linarith
    have hUtop_sup : ∀ k, cross (dir αU) (r2 k - r2 (L ⟨j1 + 1, by omega⟩)) ≤ 0 := fun k => by
      have hneg : αU = -(α ⟨i1, hi1_lt⟩ - Real.pi / 6) := by dsimp [αU, βU]; ring
      rw [hneg, hcr_conj]
      linarith [hL_vtx_sup j1 hj1_succ (α ⟨i1, hi1_lt⟩ - Real.pi / 6) (by linarith) (by linarith) k]
    have hQ1_on : cross (dir βU) (r2 (U ⟨i1 + 1, by omega⟩) - r2 (U ⟨i1, by omega⟩)) = 0 := by
      dsimp [βU]; rw [hcr_conj]
      have h := hcr_eU ⟨i1, hi1_lt⟩; rw [Fin.succ_mk, Fin.castSucc_mk] at h; rw [h, neg_zero]
    have hQ1_dir : 0 < dotC (dir βU) (r2 (U ⟨i1 + 1, by omega⟩) - r2 (U ⟨i1, by omega⟩)) := by
      dsimp [βU]; rw [hdot_conj]; exact hdot_eU ⟨i1, hi1_lt⟩
    rcases hstep_dich k2 hk2_lt with ⟨h2_eq, hi2_succ, h2_LU, h2_UL⟩ | ⟨h2_eq, hj2_succ, h2_UL, h2_LU⟩
    · have hseq2_hi : α ⟨i2 + 1, hi2_succ⟩ - β ⟨j2, hj2_lt⟩ < -(Real.pi / 6) := by
        have h := hk2_hi
        simp only [seqA, show k2 + 1 ≤ M by omega, ↓reduceDIte] at h
        have h2_p1 : (steps (k2 + 1)).1 = i2 + 1 := by simpa [i2] using congrArg Prod.fst h2_eq
        have h2_p2 : (steps (k2 + 1)).2 = j2 := by simpa [j2] using congrArg Prod.snd h2_eq
        have hf1 : (⟨(steps (k2 + 1)).1, (hsteps_bounds (k2 + 1) (by omega)).2.1⟩ : Fin pN) = ⟨i2 + 1, hi2_succ⟩ :=
          Fin.ext h2_p1
        have hf2 : (⟨(steps (k2 + 1)).2, (hsteps_bounds (k2 + 1) (by omega)).2.2⟩ : Fin qN) = ⟨j2, hj2_lt⟩ :=
          Fin.ext h2_p2
        rw [hf1, hf2] at h; exact h
      have hk12_lt : k1 < k2 := by
        rcases eq_or_lt_of_le hk12 with rfl | hlt
        · exfalso; have h := congrArg Prod.fst (h1_eq.symm.trans h2_eq); simp at h
        · exact hlt
      have hj1_le : j1 + 1 ≤ j2 := by
        have hm := (hsteps_mono (k1 + 1) k2 (by omega) (by omega)).2
        rw [congrArg Prod.snd h1_eq] at hm; exact hm
      let αV := -(β ⟨j2, hj2_lt⟩)
      let βV := αV + Real.pi / 6
      have hVtop_sup : ∀ k, cross (dir αV) (r2 k - r2 (L ⟨j2, by omega⟩)) ≤ 0 := fun k => by
        dsimp [αV]; rw [hcr_conj]
        have h := hL_edge_sup ⟨j2, hj2_lt⟩ k; rw [Fin.castSucc_mk] at h; linarith
      have hVbot_sup : ∀ k, 0 ≤ cross (dir βV) (r2 k - r2 (U ⟨i2 + 1, by omega⟩)) := fun k => by
        have hneg : βV = -(β ⟨j2, hj2_lt⟩ - Real.pi / 6) := by dsimp [βV, αV]; ring
        rw [hneg, hcr_conj]
        linarith [hU_vtx_sup i2 hi2_succ (β ⟨j2, hj2_lt⟩ - Real.pi / 6) (by linarith) (by linarith) k]
      have hδt : 0 ≤ αU - αV := by
        have hβ_cmp : β ⟨j1 + 1, hj1_succ⟩ ≤ β ⟨j2, hj2_lt⟩ := by
          rcases eq_or_lt_of_le hj1_le with heq | hlt
          · have : (⟨j1 + 1, hj1_succ⟩ : Fin qN) = ⟨j2, hj2_lt⟩ := Fin.ext heq; rw [this]
          · exact (hβ_mono (show (⟨j1 + 1, hj1_succ⟩ : Fin qN) < ⟨j2, hj2_lt⟩ from hlt)).le
        dsimp [αU, βU, αV]; linarith
      have hδb : 0 ≤ βV - βU := by
        have hα_cmp : α ⟨i2, hi2_lt⟩ ≤ α ⟨i1, hi1_lt⟩ := by
          rcases eq_or_lt_of_le hi12 with heq | hlt
          · have : (⟨i2, hi2_lt⟩ : Fin pN) = ⟨i1, hi1_lt⟩ := Fin.ext heq.symm; rw [this]
          · exact (hα_anti (show (⟨i1, hi1_lt⟩ : Fin pN) < ⟨i2, hi2_lt⟩ from hlt)).le
        dsimp [βV, αV, βU]; linarith
      apply solve_raw_two_wedge r2 hgp2 hsimp2 hlen2 huncov2 βU αU βV αV rfl rfl hδt hδb
        (U ⟨i1, by omega⟩) (L ⟨j1 + 1, by omega⟩) (U ⟨i1 + 1, by omega⟩) h1_UL h1_LU
        hUbot_sup hQ1_on hQ1_dir hUtop_sup
      right
      refine ⟨L ⟨j2, by omega⟩, U ⟨i2 + 1, by omega⟩, L ⟨j2 + 1, by omega⟩, h2_LU, h2_UL,
        hL_mono.monotone (show (⟨j1 + 1, by omega⟩ : Fin (qN + 1)) ≤ ⟨j2, by omega⟩ by simp; omega),
        hU_mono.monotone (show (⟨i1 + 1, by omega⟩ : Fin (pN + 1)) ≤ ⟨i2 + 1, by omega⟩ by simp; omega),
        hVtop_sup,
        by dsimp [αV]; rw [hcr_conj]; have h := hcr_eL ⟨j2, hj2_lt⟩; rw [Fin.succ_mk, Fin.castSucc_mk] at h; rw [h, neg_zero],
        by dsimp [αV]; rw [hdot_conj]; exact hdot_eL ⟨j2, hj2_lt⟩,
        hVbot_sup⟩
    · have hseq2_hi : α ⟨i2, hi2_lt⟩ - β ⟨j2 + 1, hj2_succ⟩ < -(Real.pi / 6) := by
        have h := hk2_hi
        simp only [seqA, show k2 + 1 ≤ M by omega, ↓reduceDIte] at h
        have h2_p1 : (steps (k2 + 1)).1 = i2 := by simpa [i2] using congrArg Prod.fst h2_eq
        have h2_p2 : (steps (k2 + 1)).2 = j2 + 1 := by simpa [j2] using congrArg Prod.snd h2_eq
        have hf1 : (⟨(steps (k2 + 1)).1, (hsteps_bounds (k2 + 1) (by omega)).2.1⟩ : Fin pN) = ⟨i2, hi2_lt⟩ :=
          Fin.ext h2_p1
        have hf2 : (⟨(steps (k2 + 1)).2, (hsteps_bounds (k2 + 1) (by omega)).2.2⟩ : Fin qN) = ⟨j2 + 1, hj2_succ⟩ :=
          Fin.ext h2_p2
        rw [hf1, hf2] at h; exact h
      let βV := -(α ⟨i2, hi2_lt⟩)
      let αV := βV - Real.pi / 6
      have hVbot_sup : ∀ k, 0 ≤ cross (dir βV) (r2 k - r2 (U ⟨i2, by omega⟩)) := fun k => by
        dsimp [βV]; rw [hcr_conj]
        have h := hU_edge_sup ⟨i2, hi2_lt⟩ k; rw [Fin.castSucc_mk] at h; linarith
      have hVtop_sup : ∀ k, cross (dir αV) (r2 k - r2 (L ⟨j2 + 1, by omega⟩)) ≤ 0 := fun k => by
        have hneg : αV = -(α ⟨i2, hi2_lt⟩ + Real.pi / 6) := by dsimp [αV, βV]; ring
        rw [hneg, hcr_conj]
        linarith [hL_vtx_sup j2 hj2_succ (α ⟨i2, hi2_lt⟩ + Real.pi / 6) (by linarith) (by linarith) k]
      have hδb : 0 ≤ βV - βU := by
        dsimp [βV, βU]
        rcases eq_or_lt_of_le hi12 with heq | hlt
        · have : (⟨i1, hi1_lt⟩ : Fin pN) = ⟨i2, hi2_lt⟩ := Fin.ext heq; rw [this]; ring_nf; exact le_rfl
        · linarith [hα_anti (show (⟨i1, hi1_lt⟩ : Fin pN) < ⟨i2, hi2_lt⟩ from hlt)]
      have hδt : 0 ≤ αU - αV := by
        rcases eq_or_lt_of_le hk12 with rfl | hlt12
        · dsimp [αU, αV, βU, βV]; linarith [Real.pi_pos]
        · have hj_le : j1 + 1 ≤ j2 := by
            have hm := (hsteps_mono (k1 + 1) k2 (by omega) (by omega)).2
            rw [congrArg Prod.snd h1_eq] at hm; exact hm
          have hβ_cmp : β ⟨j1 + 1, hj1_succ⟩ ≤ β ⟨j2, hj2_lt⟩ := by
            rcases eq_or_lt_of_le hj_le with heq | hlt
            · have : (⟨j1 + 1, hj1_succ⟩ : Fin qN) = ⟨j2, hj2_lt⟩ := Fin.ext heq; rw [this]
            · exact (hβ_mono (show (⟨j1 + 1, hj1_succ⟩ : Fin qN) < ⟨j2, hj2_lt⟩ from hlt)).le
          dsimp [αU, αV, βU, βV]; linarith
      apply solve_raw_two_wedge r2 hgp2 hsimp2 hlen2 huncov2 βU αU βV αV rfl (by dsimp [αV]; ring) hδt hδb
        (U ⟨i1, by omega⟩) (L ⟨j1 + 1, by omega⟩) (U ⟨i1 + 1, by omega⟩) h1_UL h1_LU
        hUbot_sup hQ1_on hQ1_dir hUtop_sup
      left
      refine ⟨U ⟨i2, by omega⟩, L ⟨j2 + 1, by omega⟩, U ⟨i2 + 1, by omega⟩, h2_UL, h2_LU,
        hL_mono.monotone (show (⟨j1 + 1, by omega⟩ : Fin (qN + 1)) ≤ ⟨j2 + 1, by omega⟩ by simp; omega),
        hVbot_sup,
        by dsimp [βV]; rw [hcr_conj]; have h := hcr_eU ⟨i2, hi2_lt⟩; rw [Fin.succ_mk, Fin.castSucc_mk] at h; rw [h, neg_zero],
        by dsimp [βV]; rw [hdot_conj]; exact hdot_eU ⟨i2, hi2_lt⟩,
        hVtop_sup, ?_⟩
      rcases eq_or_lt_of_le hi12 with heq | hlt
      · left
        have hieq : (⟨i1, hi1_lt⟩ : Fin pN) = ⟨i2, hi2_lt⟩ := Fin.ext heq
        refine ⟨by dsimp [βU, βV]; rw [hieq], congrArg U (Fin.ext heq.symm),
          congrArg U (Fin.ext (by simp [heq]))⟩
      · right
        exact hU_mono.monotone (show (⟨i1 + 1, by omega⟩ : Fin (pN + 1)) ≤ ⟨i2, by omega⟩ by simp; omega)

/- Section 5A: Wedge region, symmetries, ray-distance monotonicity, and localization -/

def wedgeSet {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r) : Set ℂ :=
  {z : ℂ | 0 ≤ cross (dir (-W.u_lo)) z ∧
           cross (dir (Real.pi / 6 - W.u_lo)) z ≤ 0 ∧
           cross (dir (-(Real.pi / 6 - W.v_lo))) (z - (W.L : ℂ)) ≤ 0 ∧
           0 ≤ cross (dir W.v_lo) (z - (W.L : ℂ))}

lemma wedgeSet_convex {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r) :
    Convex ℝ (wedgeSet W) := by
  intro x hx y hy a b ha hb hab
  have hsub : ∀ p : ℂ, a • x + b • y - p = a • (x - p) + b • (y - p) := fun p => by
    simp only [Complex.real_smul]
    have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    linear_combination p * hab'
  have hcr : ∀ (u p q : ℂ), cross u (a • p + b • q) = a * cross u p + b * cross u q := fun u p q => by
    rw [cross_add_right, cross_smul_right, cross_smul_right]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcr]; exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  · rw [hcr]; exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx.2.1) (mul_nonpos_of_nonneg_of_nonpos hb hy.2.1)
  · rw [hsub, hcr]; exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx.2.2.1) (mul_nonpos_of_nonneg_of_nonpos hb hy.2.2.1)
  · rw [hsub, hcr]; exact add_nonneg (mul_nonneg ha hx.2.2.2) (mul_nonneg hb hy.2.2.2)

lemma polyAt_mem_wedgeSet {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (N : ℝ)) : polyAt r t ∈ wedgeSet W :=
  convexHull_min (by rintro _ ⟨k, rfl⟩; exact ⟨W.hU_bot k, W.hU_top k, W.hV_top k, W.hV_bot k⟩)
    (wedgeSet_convex W) (polyAt_mem_convexHull r ht)

lemma wedgeSet_sub_L_re_neg {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r)
    {z : ℂ} (hz : z ∈ wedgeSet W) (hne : z ≠ (W.L : ℂ)) : (z - (W.L : ℂ)).re < 0 := by
  have hdec := wedge_coord_decomp (-(Real.pi / 6 - W.v_lo)) (z - (W.L : ℂ))
  have hang : -(Real.pi / 6 - W.v_lo) + Real.pi / 6 = W.v_lo := by ring
  rw [hang] at hdec
  set c1 : ℝ := -2 * cross (dir W.v_lo) (z - (W.L : ℂ))
  set c2 : ℝ := 2 * cross (dir (-(Real.pi / 6 - W.v_lo))) (z - (W.L : ℂ))
  have hc1 : c1 ≤ 0 := by dsimp [c1]; linarith [hz.2.2.2]
  have hc2 : c2 ≤ 0 := by dsimp [c2]; linarith [hz.2.2.1]
  have hcos1 : 0 < Real.cos (-(Real.pi / 6 - W.v_lo)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [W.hv_lo0, Real.pi_pos], by linarith [W.hv_lo_le, Real.pi_pos]⟩
  have hcos2 : 0 < Real.cos W.v_lo :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [W.hv_lo0, Real.pi_pos], by linarith [W.hv_lo_le, Real.pi_pos]⟩
  have hre : (z - (W.L : ℂ)).re = c1 * Real.cos (-(Real.pi / 6 - W.v_lo)) + c2 * Real.cos W.v_lo := by
    conv_lhs => rw [hdec]
    simp only [add_re, smul_re, smul_eq_mul, dir_re]
  have hnot0 : ¬ (c1 = 0 ∧ c2 = 0) := by
    rintro ⟨h1, h2⟩
    rw [h1, h2, zero_smul, zero_smul, add_zero] at hdec
    exact sub_ne_zero.mpr hne hdec
  rw [hre]
  rcases eq_or_lt_of_le hc1 with h1 | h1
  · have h2 : c2 < 0 := lt_of_le_of_ne hc2 (fun h => hnot0 ⟨h1, h⟩)
    nlinarith
  · nlinarith

lemma wedgeSet_rot_bounds {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r)
    {z : ℂ} (hz : z ∈ wedgeSet W) :
    0 ≤ (rotC W.u_lo z).re ∧ (rotC W.u_lo z).re ≤ W.L ∧
    0 ≤ (rotC W.u_lo z).im ∧ cross (dir (Real.pi / 6)) (rotC W.u_lo z) ≤ 0 := by
  have hrot_dir : ∀ φ, rotC W.u_lo (dir φ) = dir (φ + W.u_lo) := fun φ => by
    simp only [rotC_apply, dir, ← Complex.exp_add]; congr 1; push_cast; ring
  have hbot' : 0 ≤ (rotC W.u_lo z).im := by
    have h1 := hz.1
    rw [← cross_rotC W.u_lo, hrot_dir, neg_add_cancel, dir_zero] at h1
    unfold cross at h1; simpa using h1
  have htop' : cross (dir (Real.pi / 6)) (rotC W.u_lo z) ≤ 0 := by
    have h1 := hz.2.1
    rw [← cross_rotC W.u_lo, hrot_dir, show Real.pi / 6 - W.u_lo + W.u_lo = Real.pi / 6 by ring] at h1
    exact h1
  have hre0 : 0 ≤ (rotC W.u_lo z).re := by
    have hdec := wedge_coord_decomp 0 (rotC W.u_lo z)
    rw [zero_add, dir_zero] at hdec
    have hre : (rotC W.u_lo z).re =
        (-2 * cross (dir (Real.pi / 6)) (rotC W.u_lo z)) * 1 +
        (2 * cross 1 (rotC W.u_lo z)) * Real.cos (Real.pi / 6) := by
      conv_lhs => rw [hdec]; simp only [add_re, smul_re, smul_eq_mul, one_re, dir_re]
    have hcr1 : cross 1 (rotC W.u_lo z) = (rotC W.u_lo z).im := by unfold cross; simp
    rw [hcr1, Real.cos_pi_div_six] at hre
    have hsq3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    nlinarith
  have hreL : (rotC W.u_lo z).re ≤ W.L := by
    have hdec := wedge_coord_decomp (-(Real.pi / 6 - W.v_lo)) (z - (W.L : ℂ))
    have hang : -(Real.pi / 6 - W.v_lo) + Real.pi / 6 = W.v_lo := by ring
    rw [hang] at hdec
    have hrot_sub : rotC W.u_lo (z - (W.L : ℂ)) =
        (-2 * cross (dir W.v_lo) (z - (W.L : ℂ))) • dir (W.u_lo - (Real.pi / 6 - W.v_lo)) +
        (2 * cross (dir (-(Real.pi / 6 - W.v_lo))) (z - (W.L : ℂ))) • dir (W.u_lo + W.v_lo) := by
      conv_lhs => rw [hdec]
      rw [map_add, map_smul, map_smul, hrot_dir, hrot_dir]
      congr 2 <;> congr 1 <;> ring
    have hcos1 : 0 ≤ Real.cos (W.u_lo - (Real.pi / 6 - W.v_lo)) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [W.hu_lo0, W.hv_lo0, Real.pi_pos],
        by linarith [W.hu_lo_le, W.hv_lo_le, Real.pi_pos]⟩
    have hcos2 : 0 ≤ Real.cos (W.u_lo + W.v_lo) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [W.hu_lo0, W.hv_lo0, Real.pi_pos],
        by linarith [W.hu_lo_le, W.hv_lo_le, Real.pi_pos]⟩
    have hsub_re : (rotC W.u_lo (z - (W.L : ℂ))).re ≤ 0 := by
      rw [hrot_sub]; simp only [add_re, smul_re, smul_eq_mul, dir_re]
      nlinarith [hz.2.2.1, hz.2.2.2]
    have hL_re : (rotC W.u_lo (W.L : ℂ)).re = W.L * Real.cos W.u_lo := by
      have : rotC W.u_lo (W.L : ℂ) = W.L • dir W.u_lo := by
        simp [rotC_apply, dir, Complex.real_smul, mul_comm]
      rw [this]; simp [dir_re]
    have hsplit : rotC W.u_lo z = rotC W.u_lo (z - (W.L : ℂ)) + rotC W.u_lo (W.L : ℂ) := by
      rw [← map_add, sub_add_cancel]
    have hcos_le : Real.cos W.u_lo ≤ 1 := Real.cos_le_one _
    rw [hsplit, add_re, hL_re]
    nlinarith [W.hL]
  exact ⟨hre0, hreL, hbot', htop'⟩

noncomputable def twoWedgeBase_conj {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r) :
    TwoWedgeBase (fun k => starRingEnd ℂ (r k)) where
  L := W.L
  u_lo := Real.pi / 6 - W.u_lo
  v_lo := Real.pi / 6 - W.v_lo
  hL := W.hL
  hu_lo0 := by linarith [W.hu_lo_le]
  hu_lo_le := by linarith [W.hu_lo0]
  hv_lo0 := by linarith [W.hv_lo_le]
  hv_lo_le := by linarith [W.hv_lo0]
  hU_bot := fun k => by
    rw [dir_neg, cross_conj]; linarith [W.hU_top k]
  hU_top := fun k => by
    rw [show Real.pi / 6 - (Real.pi / 6 - W.u_lo) = W.u_lo by ring,
      show dir W.u_lo = starRingEnd ℂ (dir (-W.u_lo)) by rw [← dir_neg, neg_neg], cross_conj]
    linarith [W.hU_bot k]
  hV_top := fun k => by
    rw [show -(Real.pi / 6 - (Real.pi / 6 - W.v_lo)) = -W.v_lo by ring, dir_neg,
      show starRingEnd ℂ (r k) - (W.L : ℂ) = starRingEnd ℂ (r k - (W.L : ℂ)) by simp, cross_conj]
    linarith [W.hV_bot k]
  hV_bot := fun k => by
    rw [show dir (Real.pi / 6 - W.v_lo) = starRingEnd ℂ (dir (-(Real.pi / 6 - W.v_lo))) by
        rw [← dir_neg, neg_neg],
      show starRingEnd ℂ (r k) - (W.L : ℂ) = starRingEnd ℂ (r k - (W.L : ℂ)) by simp, cross_conj]
    linarith [W.hV_top k]

def twoWedgeBase_flipX {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r) :
    TwoWedgeBase (fun k => (W.L : ℂ) - starRingEnd ℂ (r k.rev)) where
  L := W.L
  u_lo := W.v_lo
  v_lo := W.u_lo
  hL := W.hL
  hu_lo0 := W.hv_lo0
  hu_lo_le := W.hv_lo_le
  hv_lo0 := W.hu_lo0
  hv_lo_le := W.hu_lo_le
  hU_bot := fun k => by
    rw [dir_neg, show (W.L : ℂ) - starRingEnd ℂ (r k.rev) = -(starRingEnd ℂ (r k.rev - (W.L : ℂ))) by simp,
      cross_neg_right, cross_conj, neg_neg]
    exact W.hV_bot k.rev
  hU_top := fun k => by
    rw [show dir (Real.pi / 6 - W.v_lo) = starRingEnd ℂ (dir (-(Real.pi / 6 - W.v_lo))) by
        rw [← dir_neg, neg_neg],
      show (W.L : ℂ) - starRingEnd ℂ (r k.rev) = -(starRingEnd ℂ (r k.rev - (W.L : ℂ))) by simp,
      cross_neg_right, cross_conj, neg_neg]
    exact W.hV_top k.rev
  hV_top := fun k => by
    rw [dir_neg, show (W.L : ℂ) - starRingEnd ℂ (r k.rev) - (W.L : ℂ) = -(starRingEnd ℂ (r k.rev)) by ring,
      cross_neg_right, cross_conj, neg_neg]
    exact W.hU_top k.rev
  hV_bot := fun k => by
    rw [show dir W.u_lo = starRingEnd ℂ (dir (-W.u_lo)) by rw [← dir_neg, neg_neg],
      show (W.L : ℂ) - starRingEnd ℂ (r k.rev) - (W.L : ℂ) = -(starRingEnd ℂ (r k.rev)) by ring,
      cross_neg_right, cross_conj, neg_neg]
    exact W.hU_bot k.rev

noncomputable def twoWedgeBase_rot180 {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r) :
    TwoWedgeBase (fun k => (W.L : ℂ) - r k.rev) where
  L := W.L
  u_lo := Real.pi / 6 - W.v_lo
  v_lo := Real.pi / 6 - W.u_lo
  hL := W.hL
  hu_lo0 := by linarith [W.hv_lo_le]
  hu_lo_le := by linarith [W.hv_lo0]
  hv_lo0 := by linarith [W.hu_lo_le]
  hv_lo_le := by linarith [W.hu_lo0]
  hU_bot := fun k => by
    rw [show (W.L : ℂ) - r k.rev = -(r k.rev - (W.L : ℂ)) by ring, cross_neg_right]
    linarith [W.hV_top k.rev]
  hU_top := fun k => by
    rw [show Real.pi / 6 - (Real.pi / 6 - W.v_lo) = W.v_lo by ring,
      show (W.L : ℂ) - r k.rev = -(r k.rev - (W.L : ℂ)) by ring, cross_neg_right]
    linarith [W.hV_bot k.rev]
  hV_top := fun k => by
    rw [show -(Real.pi / 6 - (Real.pi / 6 - W.u_lo)) = -W.u_lo by ring,
      show (W.L : ℂ) - r k.rev - (W.L : ℂ) = -(r k.rev) by ring, cross_neg_right]
    linarith [W.hU_bot k.rev]
  hV_bot := fun k => by
    rw [show (W.L : ℂ) - r k.rev - (W.L : ℂ) = -(r k.rev) by ring, cross_neg_right]
    linarith [W.hU_top k.rev]

lemma onUbot_le_L_cos {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r)
    {t : ℝ} (ht0 : 0 ≤ t) (hmem : t • dir (-W.u_lo) ∈ wedgeSet W) :
    t ≤ W.L * Real.cos W.u_lo := by
  have hVb := hmem.2.2.2
  rw [cross_sub_right, cross_smul_right, cross_dir_dir] at hVb
  have hcrL_b : cross (dir W.v_lo) (W.L : ℂ) = -W.L * Real.sin W.v_lo := by
    unfold cross; rw [dir_re, dir_im]; simp; ring
  rw [hcrL_b, show -W.u_lo - W.v_lo = -(W.u_lo + W.v_lo) by ring, Real.sin_neg] at hVb
  by_cases hsum : W.u_lo + W.v_lo = 0
  · have hu0 : W.u_lo = 0 := by linarith [W.hu_lo0, W.hv_lo0]
    have hv0 : W.v_lo = 0 := by linarith [W.hu_lo0, W.hv_lo0]
    have hVt := hmem.2.2.1
    rw [hu0, hv0, neg_zero, sub_zero, dir_zero, Complex.real_smul, mul_one] at hVt
    unfold cross at hVt
    rw [dir_re, dir_im, Real.cos_neg, Real.sin_neg, Real.sin_pi_div_six] at hVt
    simp only [sub_im, ofReal_im, sub_self, mul_zero, sub_re, ofReal_re] at hVt
    rw [hu0, Real.cos_zero, mul_one]; linarith
  · have hsum_pos : 0 < W.u_lo + W.v_lo := lt_of_le_of_ne (by linarith [W.hu_lo0, W.hv_lo0]) (Ne.symm hsum)
    have hsin_pos : 0 < Real.sin (W.u_lo + W.v_lo) :=
      Real.sin_pos_of_pos_of_lt_pi hsum_pos (by linarith [W.hu_lo_le, W.hv_lo_le, Real.pi_pos])
    have hid : Real.cos W.u_lo * Real.sin (W.u_lo + W.v_lo) - Real.sin W.v_lo =
        Real.sin W.u_lo * Real.cos (W.u_lo + W.v_lo) := by
      rw [Real.sin_add, Real.cos_add]
      have hsq := Real.sin_sq_add_cos_sq W.u_lo
      linear_combination Real.sin W.v_lo * hsq
    have hsin_u : 0 ≤ Real.sin W.u_lo :=
      Real.sin_nonneg_of_nonneg_of_le_pi W.hu_lo0 (by linarith [W.hu_lo_le, Real.pi_pos])
    have hcos_sum : 0 ≤ Real.cos (W.u_lo + W.v_lo) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [W.hu_lo_le, W.hv_lo_le, Real.pi_pos]⟩
    have hle : Real.sin W.v_lo ≤ Real.cos W.u_lo * Real.sin (W.u_lo + W.v_lo) := by nlinarith
    have hmul : t * Real.sin (W.u_lo + W.v_lo) ≤ W.L * Real.cos W.u_lo * Real.sin (W.u_lo + W.v_lo) := by
      nlinarith [W.hL]
    exact le_of_mul_le_mul_right hmul hsin_pos

lemma onUtop_le_L_cos {N : ℕ} {r : Fin (N + 1) → ℂ} (W : TwoWedgeBase r)
    {t : ℝ} (ht0 : 0 ≤ t) (hmem : t • dir (Real.pi / 6 - W.u_lo) ∈ wedgeSet W) :
    t ≤ W.L * Real.cos (Real.pi / 6 - W.u_lo) := by
  let Wc := twoWedgeBase_conj W
  set z : ℂ := t • dir (Real.pi / 6 - W.u_lo)
  have hmem' : t • dir (-Wc.u_lo) ∈ wedgeSet Wc := by
    have hpt : t • dir (-Wc.u_lo) = starRingEnd ℂ z := by
      dsimp [Wc, twoWedgeBase_conj, z]; rw [dir_neg, map_mul, Complex.conj_ofReal]
    rw [hpt]
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [Wc, twoWedgeBase_conj]; rw [dir_neg, cross_conj]; linarith [hmem.2.1]
    · dsimp [Wc, twoWedgeBase_conj]
      rw [show Real.pi / 6 - (Real.pi / 6 - W.u_lo) = W.u_lo by ring,
        show dir W.u_lo = starRingEnd ℂ (dir (-W.u_lo)) by rw [← dir_neg, neg_neg], cross_conj]
      linarith [hmem.1]
    · dsimp [Wc, twoWedgeBase_conj]
      rw [show -(Real.pi / 6 - (Real.pi / 6 - W.v_lo)) = -W.v_lo by ring, dir_neg,
        show starRingEnd ℂ z - (W.L : ℂ) = starRingEnd ℂ (z - (W.L : ℂ)) by simp, cross_conj]
      linarith [hmem.2.2.2]
    · dsimp [Wc, twoWedgeBase_conj]
      rw [show dir (Real.pi / 6 - W.v_lo) = starRingEnd ℂ (dir (-(Real.pi / 6 - W.v_lo))) by
          rw [← dir_neg, neg_neg],
        show starRingEnd ℂ z - (W.L : ℂ) = starRingEnd ℂ (z - (W.L : ℂ)) by simp, cross_conj]
      linarith [hmem.2.2.1]
  exact onUbot_le_L_cos Wc ht0 hmem'

lemma norm_sq_ray_sub_L (t L φ : ℝ) :
    ‖t • dir φ - (L : ℂ)‖ ^ 2 = t ^ 2 - 2 * t * L * Real.cos φ + L ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, sub_im, smul_re, smul_im, smul_eq_mul, dir_re, dir_im, ofReal_re, ofReal_im, sub_zero]
  have hsc := Real.cos_sq_add_sin_sq φ
  linear_combination t ^ 2 * hsc

lemma ray_dist_le_of_le {t1 t2 L φ : ℝ} (ht1 : 0 ≤ t1) (h12 : t1 ≤ t2)
    (ht2 : t2 ≤ L * Real.cos φ) :
    ‖t2 • dir φ - (L : ℂ)‖ ≤ ‖t1 • dir φ - (L : ℂ)‖ := by
  have hsq : ‖t2 • dir φ - (L : ℂ)‖ ^ 2 ≤ ‖t1 • dir φ - (L : ℂ)‖ ^ 2 := by
    rw [norm_sq_ray_sub_L, norm_sq_ray_sub_L]
    nlinarith
  nlinarith [norm_nonneg (t2 • dir φ - (L : ℂ)), norm_nonneg (t1 • dir φ - (L : ℂ))]

lemma ray_lt_of_dist_lt {t1 t2 L φ : ℝ} (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2)
    (ht2_le : t2 ≤ L * Real.cos φ)
    (hdist : ‖t1 • dir φ - (L : ℂ)‖ < ‖t2 • dir φ - (L : ℂ)‖) : t2 < t1 := by
  by_contra hle; push Not at hle
  have := ray_dist_le_of_le ht1 hle ht2_le
  linarith

noncomputable def segPath (P Q : ℂ) (u : ℝ) : ℂ := (1 - u) • P + u • Q

lemma segPath_continuousOn (P Q : ℂ) : ContinuousOn (segPath P Q) (Icc 0 1) := by
  unfold segPath; fun_prop

noncomputable def pathConcat (p q : ℝ → ℂ) (u : ℝ) : ℂ :=
  if u ≤ 1 / 2 then p (2 * u) else q (2 * u - 1)

lemma pathConcat_continuousOn {p q : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1))
    (hq : ContinuousOn q (Icc 0 1)) (hjoin : p 1 = q 0) :
    ContinuousOn (pathConcat p q) (Icc 0 1) := by
  have hu : Set.Icc (0 : ℝ) 1 = Set.Icc 0 (1 / 2) ∪ Set.Icc (1 / 2) 1 := by
    ext x; simp only [Set.mem_Icc, Set.mem_union]; constructor <;> intro h
    · by_cases hx : x ≤ 1 / 2
      · left; exact ⟨h.1, hx⟩
      · right; exact ⟨by linarith, h.2⟩
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hu]
  have h1 : ContinuousOn (pathConcat p q) (Icc 0 (1 / 2)) := by
    refine (hp.comp (by fun_prop : ContinuousOn (fun u : ℝ => 2 * u) (Icc 0 (1 / 2)))
      (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)).congr fun u hu => ?_
    change pathConcat p q u = p (2 * u)
    unfold pathConcat; rw [if_pos hu.2]
  have h2 : ContinuousOn (pathConcat p q) (Icc (1 / 2) 1) := by
    refine (hq.comp (by fun_prop : ContinuousOn (fun u : ℝ => 2 * u - 1) (Icc (1 / 2) 1))
      (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)).congr fun u hu => ?_
    change pathConcat p q u = q (2 * u - 1)
    unfold pathConcat
    by_cases hx : u ≤ 1 / 2
    · have heq : u = 1 / 2 := le_antisymm hx hu.1
      rw [if_pos hx, heq]; norm_num; exact hjoin
    · rw [if_neg hx]
  exact h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc

lemma pathConcat_zero (p q : ℝ → ℂ) : pathConcat p q 0 = p 0 := by simp [pathConcat]

lemma pathConcat_one (p q : ℝ → ℂ) : pathConcat p q 1 = q 1 := by
  unfold pathConcat; rw [if_neg (by norm_num)]; norm_num

lemma pathConcat_mem {p q : ℝ → ℂ} {S : Set ℂ}
    (hp : ∀ u ∈ Icc (0 : ℝ) 1, p u ∈ S) (hq : ∀ u ∈ Icc (0 : ℝ) 1, q u ∈ S)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : pathConcat p q u ∈ S := by
  unfold pathConcat
  split_ifs with h
  · exact hp (2 * u) ⟨by linarith [hu.1], by linarith⟩
  · exact hq (2 * u - 1) ⟨by linarith, by linarith [hu.2]⟩

lemma crossing_two_on_bot_two_on_top {u_lo tA tQ1 tW tB : ℝ}
    (htA : 0 < tA) (hAQ : tA < tQ1) (htW : 0 < tW) (hWB : tW < tB)
    {α β : ℝ → ℂ} (hα_cont : ContinuousOn α (Icc 0 1)) (hβ_cont : ContinuousOn β (Icc 0 1))
    (hα_mem : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ cross (dir (-u_lo)) (α s) ∧ cross (dir (Real.pi / 6 - u_lo)) (α s) ≤ 0)
    (hβ_mem : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ cross (dir (-u_lo)) (β t) ∧ cross (dir (Real.pi / 6 - u_lo)) (β t) ≤ 0)
    (hα0 : α 0 = tA • dir (-u_lo)) (hα1 : α 1 = tB • dir (Real.pi / 6 - u_lo))
    (hβ0 : β 0 = tQ1 • dir (-u_lo)) (hβ1 : β 1 = tW • dir (Real.pi / 6 - u_lo))
    (hdisj : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, α s ≠ β t) : False := by
  let K : Set ℂ := {z | 0 ≤ cross (dir (-u_lo)) z ∧ cross (dir (Real.pi / 6 - u_lo)) z ≤ 0}
  let nBot : ℂ := -I * dir (-u_lo)
  let nTop : ℂ := I * dir (Real.pi / 6 - u_lo)
  have hnBot : nBot ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (dir_ne_zero _)
  have hnTop : nTop ≠ 0 := mul_ne_zero I_ne_zero (dir_ne_zero _)
  have hdot_bot : ∀ (t : ℝ) (z : ℂ), dotC nBot (z - t • dir (-u_lo)) = -cross (dir (-u_lo)) z := fun t z => by
    have h1 : dotC nBot (z - t • dir (-u_lo)) = -cross (dir (-u_lo)) (z - t • dir (-u_lo)) := by
      dsimp [nBot]; unfold dotC cross; simp; ring
    rw [h1, cross_sub_right, cross_smul_right, cross_self, mul_zero, sub_zero]
  have hdot_top : ∀ (t : ℝ) (z : ℂ), dotC nTop (z - t • dir (Real.pi / 6 - u_lo)) =
      cross (dir (Real.pi / 6 - u_lo)) z := fun t z => by
    have h1 : dotC nTop (z - t • dir (Real.pi / 6 - u_lo)) =
        cross (dir (Real.pi / 6 - u_lo)) (z - t • dir (Real.pi / 6 - u_lo)) := by
      dsimp [nTop]; unfold dotC cross; simp; ring
    rw [h1, cross_sub_right, cross_smul_right, cross_self, mul_zero, sub_zero]
  have hcr_dir : cross (dir (-u_lo)) (dir (Real.pi / 6 - u_lo)) = 1 / 2 := by
    rw [cross_dir_dir, show Real.pi / 6 - u_lo - -u_lo = Real.pi / 6 by ring, Real.sin_pi_div_six]
  have hcr_dir' : cross (dir (Real.pi / 6 - u_lo)) (dir (-u_lo)) = -(1 / 2) := by
    rw [cross_antisymm, hcr_dir]
  have hAB : cross (tA • dir (-u_lo) - tQ1 • dir (-u_lo))
      (tB • dir (Real.pi / 6 - u_lo) - tQ1 • dir (-u_lo)) < 0 := by
    rw [← sub_smul, cross_smul_left, cross_sub_right, cross_smul_right, cross_smul_right,
      hcr_dir, cross_self, mul_zero, sub_zero]
    nlinarith
  have hBC : cross (tB • dir (Real.pi / 6 - u_lo) - tQ1 • dir (-u_lo))
      (tB • dir (Real.pi / 6 - u_lo) - tW • dir (Real.pi / 6 - u_lo)) < 0 := by
    rw [← sub_smul, cross_smul_right, cross_sub_left, cross_smul_left, cross_smul_left,
      cross_self, mul_zero, zero_sub, hcr_dir]
    nlinarith
  have hCD : cross (tB • dir (Real.pi / 6 - u_lo) - tW • dir (Real.pi / 6 - u_lo))
      (tA • dir (-u_lo) - tW • dir (Real.pi / 6 - u_lo)) < 0 := by
    rw [← sub_smul, cross_smul_left, cross_sub_right, cross_smul_right, cross_smul_right,
      hcr_dir', cross_self, mul_zero, sub_zero]
    nlinarith
  have hDA : cross (tA • dir (-u_lo) - tW • dir (Real.pi / 6 - u_lo))
      (tA • dir (-u_lo) - tQ1 • dir (-u_lo)) < 0 := by
    rw [← sub_smul, cross_smul_right, cross_sub_left, cross_smul_left, cross_smul_left,
      cross_self, mul_zero, zero_sub, hcr_dir']
    nlinarith
  obtain ⟨s, hs, t, ht, heq⟩ := crossing_lemma (K := K) hnBot hnBot hnTop hnTop
    (fun z hz => by rw [hdot_bot]; linarith [hz.1])
    (fun z hz => by rw [hdot_bot]; linarith [hz.1])
    (fun z hz => by rw [hdot_top]; exact hz.2)
    (fun z hz => by rw [hdot_top]; exact hz.2)
    hAB hBC hCD hDA hα_cont hβ_cont hα_mem hβ_mem hα0 hα1 hβ0 hβ1
  exact hdisj s hs t ht heq

lemma crossing_three_on_bot {L tW tA tQ1 tB : ℝ}
    (htW0 : 0 ≤ tW) (hWA : tW < tA) (hAQ : tA < tQ1) (hQL : tQ1 ≤ L)
    (htB0 : 0 < tB) (hB_re : (tB • dir (Real.pi / 6)).re ≤ L)
    {α β : ℝ → ℂ} (hα_cont : ContinuousOn α (Icc 0 1)) (hβ_cont : ContinuousOn β (Icc 0 1))
    (hα_mem : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (α s).re ∧ (α s).re ≤ L ∧ 0 ≤ (α s).im ∧
      cross (dir (Real.pi / 6)) (α s) ≤ 0)
    (hβ_mem : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (β t).re ∧ (β t).re ≤ L ∧ 0 ≤ (β t).im ∧
      cross (dir (Real.pi / 6)) (β t) ≤ 0)
    (hα0 : α 0 = (tA : ℂ)) (hα1 : α 1 = tB • dir (Real.pi / 6))
    (hβ0 : β 0 = (tW : ℂ)) (hβ1 : β 1 = (tQ1 : ℂ))
    (hdisj : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, α s ≠ β t) : False := by
  let M : ℝ := L + 1
  let K : Set ℂ := {z | -1 ≤ z.re ∧ z.re ≤ M ∧ -2 ≤ z.im ∧ cross (dir (Real.pi / 6)) z ≤ 0}
  have hsq3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq3_gt1 : 1 < Real.sqrt 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hK_conv : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [add_re, smul_re, smul_eq_mul]; nlinarith [hx.1, hy.1]
    · simp only [add_re, smul_re, smul_eq_mul]; nlinarith [hx.2.1, hy.2.1]
    · simp only [add_im, smul_im, smul_eq_mul]; nlinarith [hx.2.2.1, hy.2.2.1]
    · rw [cross_add_right, cross_smul_right, cross_smul_right]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx.2.2.2) (mul_nonpos_of_nonneg_of_nonpos hb hy.2.2.2)
  have hcr6 : ∀ x y : ℝ, cross (dir (Real.pi / 6)) (x + y * I) = (Real.sqrt 3 / 2) * y - (1 / 2) * x := fun x y => by
    unfold cross; rw [dir_re, dir_im, Real.cos_pi_div_six, Real.sin_pi_div_six]; simp
  have hptK : ∀ x y : ℝ, -1 ≤ x → x ≤ M → -2 ≤ y → (Real.sqrt 3 / 2) * y - (1 / 2) * x ≤ 0 →
      ((x : ℂ) + (y : ℂ) * I) ∈ K := fun x y h1 h2 h3 h4 => by
    refine ⟨by simp [h1], by simp [h2], by simp [h3], ?_⟩
    rw [hcr6]; exact h4
  let Ac : ℂ := (tA : ℂ) + ((-2 : ℝ) : ℂ) * I
  let Bc : ℂ := (M : ℂ) + ((-1 : ℝ) : ℂ) * I
  let Cc : ℂ := tB • dir (Real.pi / 6)
  let Dc : ℂ := ((-1 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I
  let P_W : ℂ := (tW : ℂ) + ((-1 : ℝ) : ℂ) * I
  let P_Q : ℂ := (tQ1 : ℂ) + ((-1 : ℝ) : ℂ) * I
  have hsegK : ∀ P Q : ℂ, P ∈ K → Q ∈ K → ∀ u ∈ Icc (0 : ℝ) 1, segPath P Q u ∈ K := fun P Q hP hQ u hu =>
    hK_conv hP hQ (by linarith [hu.2]) hu.1 (by ring)
  have hAcK : Ac ∈ K := hptK tA (-2) (by linarith) (by dsimp [M]; linarith) (by linarith) (by nlinarith)
  have hBcK : Bc ∈ K := hptK M (-1) (by dsimp [M]; linarith) (by linarith) (by linarith) (by dsimp [M]; nlinarith)
  have hDcK : Dc ∈ K := hptK (-1) (-1) (by linarith) (by dsimp [M]; linarith) (by linarith) (by nlinarith)
  have hPWK : P_W ∈ K := hptK tW (-1) (by linarith) (by dsimp [M]; linarith) (by linarith) (by nlinarith)
  have hPQK : P_Q ∈ K := hptK tQ1 (-1) (by linarith) (by dsimp [M]; linarith) (by linarith) (by nlinarith)
  have hAK : (tA : ℂ) ∈ K := by
    have := hα_mem 0 ⟨le_rfl, zero_le_one⟩; rw [hα0] at this
    exact ⟨by linarith [this.1], by dsimp [M]; linarith [this.2.1], by linarith [this.2.2.1], this.2.2.2⟩
  have hWK : (tW : ℂ) ∈ K := by
    have := hβ_mem 0 ⟨le_rfl, zero_le_one⟩; rw [hβ0] at this
    exact ⟨by linarith [this.1], by dsimp [M]; linarith [this.2.1], by linarith [this.2.2.1], this.2.2.2⟩
  have hQK : (tQ1 : ℂ) ∈ K := by
    have := hβ_mem 1 ⟨zero_le_one, le_rfl⟩; rw [hβ1] at this
    exact ⟨by linarith [this.1], by dsimp [M]; linarith [this.2.1], by linarith [this.2.2.1], this.2.2.2⟩
  let αE := pathConcat (segPath Ac (tA : ℂ)) α
  let β1 := pathConcat (segPath Bc P_Q) (segPath P_Q (tQ1 : ℂ))
  let β2 := pathConcat (fun u => β (1 - u)) (segPath (tW : ℂ) P_W)
  let β3 := pathConcat β2 (segPath P_W Dc)
  let βE := pathConcat β1 β3
  have hαE_cont : ContinuousOn αE (Icc 0 1) :=
    pathConcat_continuousOn (segPath_continuousOn _ _) hα_cont (by simp [segPath, hα0])
  have hβ_rev_cont : ContinuousOn (fun u : ℝ => β (1 - u)) (Icc 0 1) :=
    hβ_cont.comp (by fun_prop) (fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩)
  have hβ1_cont : ContinuousOn β1 (Icc 0 1) :=
    pathConcat_continuousOn (segPath_continuousOn _ _) (segPath_continuousOn _ _) (by simp [segPath])
  have hβ2_cont : ContinuousOn β2 (Icc 0 1) :=
    pathConcat_continuousOn hβ_rev_cont (segPath_continuousOn _ _) (by simp [segPath, hβ0])
  have hβ3_cont : ContinuousOn β3 (Icc 0 1) :=
    pathConcat_continuousOn hβ2_cont (segPath_continuousOn _ _) (by simp [β2, pathConcat_one, segPath])
  have hβE_cont : ContinuousOn βE (Icc 0 1) :=
    pathConcat_continuousOn hβ1_cont hβ3_cont
      (by simp [β1, β3, β2, pathConcat_one, pathConcat_zero, segPath, hβ1])
  have hαE_mem : ∀ s ∈ Icc (0 : ℝ) 1, αE s ∈ K := fun s hs =>
    pathConcat_mem (hsegK _ _ hAcK hAK)
      (fun u hu => let h := hα_mem u hu; ⟨by linarith [h.1], by dsimp [M]; linarith [h.2.1], by linarith [h.2.2.1], h.2.2.2⟩) hs
  have hβE_mem : ∀ t ∈ Icc (0 : ℝ) 1, βE t ∈ K := fun t ht =>
    pathConcat_mem (S := K)
      (fun u hu => pathConcat_mem (S := K) (hsegK _ _ hBcK hPQK) (hsegK _ _ hPQK hQK) hu)
      (fun u hu => pathConcat_mem (S := K)
        (fun v hv => pathConcat_mem (S := K)
          (fun w hw => let h := hβ_mem (1 - w) ⟨by linarith [hw.2], by linarith [hw.1]⟩
            ⟨by linarith [h.1], by dsimp [M]; linarith [h.2.1], by linarith [h.2.2.1], h.2.2.2⟩)
          (hsegK _ _ hWK hPWK) hv)
        (hsegK _ _ hPWK hDcK) hu) ht
  have hCc_re : Cc.re = tB * (Real.sqrt 3 / 2) := by
    simp [Cc, dir_re, Real.cos_pi_div_six]
  have hCc_im : Cc.im = tB / 2 := by
    simp [Cc, dir_im, Real.sin_pi_div_six]; ring
  have hAB : cross (Ac - Bc) (Cc - Bc) < 0 := by
    unfold cross; simp [Ac, Bc, hCc_re, hCc_im] at *
    have hreM : tB * (Real.sqrt 3 / 2) ≤ L := by simpa [Cc, dir_re, Real.cos_pi_div_six] using hB_re
    dsimp [M]; nlinarith
  have hBC : cross (Cc - Bc) (Cc - Dc) < 0 := by
    unfold cross; simp [Bc, Dc, hCc_re, hCc_im]
    dsimp [M]; nlinarith
  have hCD : cross (Cc - Dc) (Ac - Dc) < 0 := by
    unfold cross; simp [Ac, Dc, hCc_re, hCc_im]
    nlinarith
  have hDA : cross (Ac - Dc) (Ac - Bc) < 0 := by
    unfold cross; simp [Ac, Bc, Dc]
    dsimp [M]; nlinarith
  obtain ⟨s, hs, t, ht, heq⟩ := crossing_lemma (K := K)
    (neg_ne_zero.mpr I_ne_zero) one_ne_zero (mul_ne_zero I_ne_zero (dir_ne_zero _)) (neg_ne_zero.mpr one_ne_zero)
    (fun z hz => by unfold dotC; simp [Ac]; linarith [hz.2.2.1])
    (fun z hz => by unfold dotC; simp [Bc]; linarith [hz.2.1])
    (fun z hz => by
      have hid : dotC (I * dir (Real.pi / 6)) (z - Cc) = cross (dir (Real.pi / 6)) (z - Cc) := by
        unfold dotC cross; simp; ring
      rw [hid, cross_sub_right, show cross (dir (Real.pi / 6)) Cc = 0 by
        change cross (dir (Real.pi / 6)) (tB • dir (Real.pi / 6)) = 0
        rw [cross_smul_right, cross_self, mul_zero], sub_zero]
      exact hz.2.2.2)
    (fun z hz => by unfold dotC; simp [Dc]; linarith [hz.1])
    hAB hBC hCD hDA hαE_cont hβE_cont hαE_mem hβE_mem
    (by simp [αE, pathConcat_zero, segPath]) (by simp [αE, pathConcat_one, hα1, Cc])
    (by simp [βE, β1, pathConcat_zero, segPath]) (by simp [βE, β3, pathConcat_one, segPath])
  -- Derive contradiction from αE s = βE t by splitting into im < 0 vs im ≥ 0!
  have hα_cases : (∃ u ∈ Icc (0 : ℝ) 1, αE s = segPath Ac (tA : ℂ) u) ∨ (∃ u ∈ Icc (0 : ℝ) 1, αE s = α u) := by
    unfold αE pathConcat
    split_ifs with h
    · left; exact ⟨2 * s, ⟨by linarith [hs.1], by linarith⟩, rfl⟩
    · right; exact ⟨2 * s - 1, ⟨by linarith, by linarith [hs.2]⟩, rfl⟩
  have hβ_cases : (∃ v ∈ Icc (0 : ℝ) 1, βE t = segPath Bc P_Q v) ∨
      (∃ v ∈ Icc (0 : ℝ) 1, βE t = segPath P_Q (tQ1 : ℂ) v) ∨
      (∃ v ∈ Icc (0 : ℝ) 1, βE t = β v) ∨
      (∃ v ∈ Icc (0 : ℝ) 1, βE t = segPath (tW : ℂ) P_W v) ∨
      (∃ v ∈ Icc (0 : ℝ) 1, βE t = segPath P_W Dc v) := by
    unfold βE pathConcat
    split_ifs with h1
    · unfold β1 pathConcat
      split_ifs with h2
      · left; exact ⟨2 * (2 * t), ⟨by linarith [ht.1], by linarith⟩, rfl⟩
      · right; left; exact ⟨2 * (2 * t) - 1, ⟨by linarith, by linarith⟩, rfl⟩
    · unfold β3 pathConcat
      split_ifs with h2
      · unfold β2 pathConcat
        split_ifs with h3
        · right; right; left; exact ⟨1 - 2 * (2 * (2 * t - 1)), ⟨by linarith, by linarith⟩, rfl⟩
        · right; right; right; left; exact ⟨2 * (2 * (2 * t - 1)) - 1, ⟨by linarith, by linarith⟩, rfl⟩
      · right; right; right; right; exact ⟨2 * (2 * t - 1) - 1, ⟨by linarith, by linarith [ht.2]⟩, rfl⟩
  rcases hα_cases with ⟨u, hu, hαu⟩ | ⟨u, hu, hαu⟩
  · have hreA : (αE s).re = tA := by rw [hαu]; simp [segPath, Ac]; ring
    have himA : (αE s).im ≤ 0 := by rw [hαu]; simp [segPath, Ac]; linarith [hu.2]
    rcases hβ_cases with ⟨v, hv, hβv⟩ | ⟨v, hv, hβv⟩ | ⟨v, hv, hβv⟩ | ⟨v, hv, hβv⟩ | ⟨v, hv, hβv⟩
    · have hreB : tQ1 ≤ (βE t).re := by rw [hβv]; simp [segPath, Bc, P_Q]; dsimp [M]; nlinarith [hv.1, hv.2]
      rw [← heq, hreA] at hreB; linarith
    · have hreB : (βE t).re = tQ1 := by rw [hβv]; simp [segPath, P_Q]; ring
      rw [← heq, hreA] at hreB; linarith
    · have himB : 0 ≤ (βE t).im := by rw [hβv]; exact (hβ_mem v hv).2.2.1
      have him0 : (αE s).im = 0 := le_antisymm himA (by rw [heq]; exact himB)
      have hu1 : u = 1 := by rw [hαu] at him0; simp [segPath, Ac] at him0; linarith
      have hαeq : αE s = α 0 := by rw [hαu, hu1, hα0]; simp [segPath]
      exact hdisj 0 ⟨le_rfl, zero_le_one⟩ v hv (by rw [← hαeq, heq, hβv])
    · have hreB : (βE t).re = tW := by rw [hβv]; simp [segPath, P_W]; ring
      rw [← heq, hreA] at hreB; linarith
    · have hreB : (βE t).re ≤ tW := by rw [hβv]; simp [segPath, P_W, Dc]; nlinarith [hv.1, hv.2]
      rw [← heq, hreA] at hreB; linarith
  · have himA : 0 ≤ (αE s).im := by rw [hαu]; exact (hα_mem u hu).2.2.1
    rcases hβ_cases with ⟨v, hv, hβv⟩ | ⟨v, hv, hβv⟩ | ⟨v, hv, hβv⟩ | ⟨v, hv, hβv⟩ | ⟨v, hv, hβv⟩
    · have himB : (βE t).im = -1 := by rw [hβv]; simp [segPath, Bc, P_Q]; ring
      rw [← heq] at himB; linarith
    · have himB : (βE t).im = -(1 - v) := by rw [hβv]; simp [segPath, P_Q]
      have hv1 : v = 1 := by rw [← heq] at himB; linarith [hv.2]
      have hβeq : βE t = β 1 := by rw [hβv, hv1, hβ1]; simp [segPath]
      exact hdisj u hu 1 ⟨zero_le_one, le_rfl⟩ (by rw [← hαu, heq, hβeq])
    · exact hdisj u hu v hv (by rw [← hαu, heq, hβv])
    · have himB : (βE t).im = -v := by rw [hβv]; simp [segPath, P_W]
      have hv0 : v = 0 := by rw [← heq] at himB; linarith [hv.1]
      have hβeq : βE t = β 0 := by rw [hβv, hv0, hβ0]; simp [segPath]
      exact hdisj u hu 0 ⟨le_rfl, zero_le_one⟩ (by rw [← hαu, heq, hβeq])
    · have himB : (βE t).im = -1 := by rw [hβv]; simp [segPath, P_W, Dc]; ring
      rw [← heq] at himB; linarith

lemma exists_far_before_B {N : ℕ} {r : Fin (N + 1) → ℂ}
    (hgp : GenPos r) (hsimp : IsSimplePoly r) (huncov : ¬ CoveredUnit r)
    (W : TwoWedgeBase r) {A B Q1 : Fin (N + 1)} {tA tB tQ1 : ℝ}
    (hAB : A < B) (hBQ1 : B < Q1) (hAQ : tA < tQ1)
    (hOnA : OnUbot W A tA) (hOnB : OnUtop W B tB) (hOnQ1 : OnUbot W Q1 tQ1) :
    ∃ x : Fin (N + 1), x ≤ B ∧ 1 < ‖r x - (W.L : ℂ)‖ := by
  by_contra hnone; push Not at hnone
  obtain ⟨x, hx_far⟩ : ∃ x : Fin (N + 1), 1 < ‖r x - (W.L : ℂ)‖ := by
    apply wedge_has_far_point huncov (U := (W.L : ℂ)) (β := Real.pi - (Real.pi / 6 - W.v_lo))
    · intro k
      have h1 : dir (Real.pi - (Real.pi / 6 - W.v_lo)) = -dir (-(Real.pi / 6 - W.v_lo)) := by
        rw [show Real.pi - (Real.pi / 6 - W.v_lo) = -(Real.pi / 6 - W.v_lo) + Real.pi by ring,
          dir_add, dir_pi, mul_neg, mul_one]
      rw [h1, cross_neg_left]; linarith [W.hV_top k]
    · intro k
      have h1 : dir (Real.pi - (Real.pi / 6 - W.v_lo) + Real.pi / 6) = -dir W.v_lo := by
        rw [show Real.pi - (Real.pi / 6 - W.v_lo) + Real.pi / 6 = W.v_lo + Real.pi by ring,
          dir_add, dir_pi, mul_neg, mul_one]
      rw [h1, cross_neg_left]; linarith [W.hV_bot k]
  have hBx : B < x := by
    by_contra hle; push Not at hle; linarith [hnone x hle]
  -- Shoot ray from r x outward along (r x - L) until hitting ∂W_U!
  have hrx_ne_L : r x ≠ (W.L : ℂ) := by
    intro heq; rw [heq, sub_self, norm_zero] at hx_far; linarith
  have hrx_mem : r x ∈ wedgeSet W := ⟨W.hU_bot x, W.hU_top x, W.hV_top x, W.hV_bot x⟩
  let fb0 : ℝ := cross (dir (-W.u_lo)) (r x)
  let ft0 : ℝ := -cross (dir (Real.pi / 6 - W.u_lo)) (r x)
  let fb' : ℝ := cross (dir (-W.u_lo)) (r x - (W.L : ℂ))
  let ft' : ℝ := -cross (dir (Real.pi / 6 - W.u_lo)) (r x - (W.L : ℂ))
  have hfb0 : 0 ≤ fb0 := W.hU_bot x
  have hft0 : 0 ≤ ft0 := by dsimp [ft0]; linarith [W.hU_top x]
  have hneg_slope : fb' < 0 ∨ ft' < 0 := by
    by_contra hnn; push Not at hnn
    have hdec := wedge_coord_decomp (-W.u_lo) (r x - (W.L : ℂ))
    rw [show -W.u_lo + Real.pi / 6 = Real.pi / 6 - W.u_lo by ring] at hdec
    have hre : (r x - (W.L : ℂ)).re =
        (2 * ft') * Real.cos (-W.u_lo) + (2 * fb') * Real.cos (Real.pi / 6 - W.u_lo) := by
      conv_lhs => rw [hdec]
      simp only [add_re, smul_re, smul_eq_mul, dir_re, ft', fb']; ring
    have hc1 : 0 < Real.cos (-W.u_lo) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [W.hu_lo_le, Real.pi_pos], by linarith [W.hu_lo0, Real.pi_pos]⟩
    have hc2 : 0 < Real.cos (Real.pi / 6 - W.u_lo) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [W.hu_lo_le, Real.pi_pos], by linarith [W.hu_lo0, Real.pi_pos]⟩
    have hre_neg := wedgeSet_sub_L_re_neg W hrx_mem hrx_ne_L
    nlinarith
  have hray_hit : ∃ s : ℝ, 0 ≤ s ∧
      0 ≤ fb0 + s * fb' ∧ 0 ≤ ft0 + s * ft' ∧ (fb0 + s * fb' = 0 ∨ ft0 + s * ft' = 0) := by
    by_cases hb : fb' < 0
    · by_cases ht : ft' < 0
      · by_cases hcmp : fb0 / (-fb') ≤ ft0 / (-ft')
        · refine ⟨fb0 / (-fb'), div_nonneg hfb0 (by linarith), ?_, ?_, Or.inl ?_⟩
          · have : fb0 + fb0 / (-fb') * fb' = 0 := by field_simp [hb.ne]; ring
            linarith
          · have h1 : fb0 / (-fb') * (-ft') ≤ ft0 := (le_div_iff₀ (show 0 < -ft' by linarith)).mp hcmp
            linarith
          · field_simp [hb.ne]; ring
        · push Not at hcmp
          refine ⟨ft0 / (-ft'), div_nonneg hft0 (by linarith), ?_, ?_, Or.inr ?_⟩
          · have h1 : ft0 / (-ft') * (-fb') ≤ fb0 := (le_div_iff₀ (show 0 < -fb' by linarith)).mp hcmp.le
            linarith
          · have : ft0 + ft0 / (-ft') * ft' = 0 := by field_simp [ht.ne]; ring
            linarith
          · field_simp [ht.ne]; ring
      · push Not at ht
        refine ⟨fb0 / (-fb'), div_nonneg hfb0 (by linarith), ?_, ?_, Or.inl ?_⟩
        · have : fb0 + fb0 / (-fb') * fb' = 0 := by field_simp [hb.ne]; ring
          linarith
        · exact add_nonneg hft0 (mul_nonneg (div_nonneg hfb0 (by linarith)) ht)
        · field_simp [hb.ne]; ring
    · push Not at hb
      have ht : ft' < 0 := hneg_slope.resolve_left (not_lt.mpr hb)
      refine ⟨ft0 / (-ft'), div_nonneg hft0 (by linarith), ?_, ?_, Or.inr ?_⟩
      · exact add_nonneg hfb0 (mul_nonneg (div_nonneg hft0 (by linarith)) hb)
      · have : ft0 + ft0 / (-ft') * ft' = 0 := by field_simp [ht.ne]; ring
        linarith
      · field_simp [ht.ne]; ring
  obtain ⟨sStar, hsStar0, hfb_s, hft_s, hhit⟩ := hray_hit
  let Wpt : ℂ := r x + sStar • (r x - (W.L : ℂ))
  have hWpt_eq : Wpt = r x + sStar • (r x - (W.L : ℂ)) := rfl
  have hWpt_subL : Wpt - (W.L : ℂ) = (1 + sStar) • (r x - (W.L : ℂ)) := by
    rw [hWpt_eq, Complex.real_smul, Complex.real_smul]; push_cast; ring
  have hWpt_mem : Wpt ∈ wedgeSet W := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hWpt_eq, cross_add_right, cross_smul_right]; exact hfb_s
    · rw [hWpt_eq, cross_add_right, cross_smul_right]; dsimp [ft0, ft'] at hft_s; linarith
    · rw [hWpt_subL, cross_smul_right]; exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (W.hV_top x)
    · rw [hWpt_subL, cross_smul_right]; exact mul_nonneg (by linarith) (W.hV_bot x)
  have hWpt_far : 1 < ‖Wpt - (W.L : ℂ)‖ := by
    rw [hWpt_subL, norm_smul, Real.norm_of_nonneg (by linarith)]
    nlinarith
  have hseg_far : ∀ u ∈ Icc (0 : ℝ) 1, 1 < ‖segPath Wpt (r x) u - (W.L : ℂ)‖ := fun u hu => by
    have h1 : segPath Wpt (r x) u - (W.L : ℂ) = (1 + (1 - u) * sStar) • (r x - (W.L : ℂ)) := by
      unfold segPath; rw [hWpt_eq]; simp only [Complex.real_smul]; push_cast; ring
    have hnn : 0 ≤ (1 - u) * sStar := mul_nonneg (by linarith [hu.2]) hsStar0
    rw [h1, norm_smul, Real.norm_of_nonneg (by linarith)]
    nlinarith
  have hseg_mem : ∀ u ∈ Icc (0 : ℝ) 1, segPath Wpt (r x) u ∈ wedgeSet W := fun u hu =>
    wedgeSet_convex W hWpt_mem hrx_mem (by linarith [hu.2]) hu.1 (by ring)
  -- Path α = polySubpath r A B stays in closedBall L 1!
  have hα_ball : ∀ u ∈ Icc (0 : ℝ) 1, ‖polySubpath r A B u - (W.L : ℂ)‖ ≤ 1 := by
    intro u hu
    let t : ℝ := (1 - u) * (A : ℝ) + u * (B : ℝ)
    have htA : (A : ℝ) ≤ t := by
      have hABr : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB.le
      dsimp [t]; nlinarith [hu.1, hu.2]
    have htB : t ≤ (B : ℝ) := by
      have hABr : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB.le
      dsimp [t]; nlinarith [hu.1, hu.2]
    have hN : N ≠ 0 := by rintro rfl; omega
    have ht_nn : 0 ≤ t := (Nat.cast_nonneg (A : ℕ)).trans htA
    by_cases htop : t = (B : ℝ)
    · change ‖polyAt r t - (W.L : ℂ)‖ ≤ 1
      rw [htop, polyAt_nat]; exact hnone B le_rfl
    · have ht_ltB : t < (B : ℝ) := lt_of_le_of_ne htB htop
      have hfl_ltB : ⌊t⌋₊ < (B : ℕ) := (Nat.floor_lt ht_nn).mpr ht_ltB
      have hfl_ltN : ⌊t⌋₊ < N := lt_of_lt_of_le hfl_ltB (Nat.le_of_lt_succ B.isLt)
      let k : Fin N := ⟨⌊t⌋₊, hfl_ltN⟩
      have htk : t ∈ Icc (k : ℝ) ((k : ℝ) + 1) :=
        ⟨Nat.floor_le ht_nn, (Nat.lt_floor_add_one t).le⟩
      have h1 : k.castSucc ≤ B := by change ⌊t⌋₊ ≤ (B : ℕ); omega
      have h2 : k.succ ≤ B := by change ⌊t⌋₊ + 1 ≤ (B : ℕ); omega
      have hpt := polyAt_eq_on_edge r k htk
      change ‖polyAt r t - (W.L : ℂ)‖ ≤ 1
      rw [hpt]
      have hsplit : ((1 - (t - (k : ℝ))) • r k.castSucc + (t - (k : ℝ)) • r k.succ) - (W.L : ℂ) =
          (1 - (t - (k : ℝ))) • (r k.castSucc - (W.L : ℂ)) + (t - (k : ℝ)) • (r k.succ - (W.L : ℂ)) := by
        simp only [Complex.real_smul]; push_cast; ring
      rw [hsplit]
      have hs0 : 0 ≤ t - (k : ℝ) := by linarith [htk.1]
      have hs1 : 0 ≤ 1 - (t - (k : ℝ)) := by linarith [htk.2]
      calc ‖(1 - (t - (k : ℝ))) • (r k.castSucc - (W.L : ℂ)) + (t - (k : ℝ)) • (r k.succ - (W.L : ℂ))‖
          ≤ ‖(1 - (t - (k : ℝ))) • (r k.castSucc - (W.L : ℂ))‖ + ‖(t - (k : ℝ)) • (r k.succ - (W.L : ℂ))‖ :=
            norm_add_le _ _
        _ = (1 - (t - (k : ℝ))) * ‖r k.castSucc - (W.L : ℂ)‖ + (t - (k : ℝ)) * ‖r k.succ - (W.L : ℂ)‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hs1, Real.norm_of_nonneg hs0]
        _ ≤ (1 - (t - (k : ℝ))) * 1 + (t - (k : ℝ)) * 1 := by
            nlinarith [hnone k.castSucc h1, hnone k.succ h2]
        _ = 1 := by ring
  -- Path β = pathConcat (segPath Wpt (r x)) (polySubpath r x Q1) is disjoint from α!
  let α := polySubpath r A B
  let β := pathConcat (segPath Wpt (r x)) (polySubpath r x Q1)
  have hα_cont : ContinuousOn α (Icc 0 1) := polySubpath_continuousOn r A B
  have hβ_cont : ContinuousOn β (Icc 0 1) :=
    pathConcat_continuousOn (segPath_continuousOn Wpt (r x)) (polySubpath_continuousOn r x Q1)
      (by simp [segPath, polySubpath_zero])
  have hα_mem : ∀ s ∈ Icc (0 : ℝ) 1, α s ∈ wedgeSet W := fun s hs =>
    polyAt_mem_wedgeSet W (by
      have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
      have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
      have hAN : (A : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ A.isLt
      have hBN : (B : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ B.isLt
      exact ⟨by nlinarith [hs.1, hs.2], by nlinarith [hs.1, hs.2]⟩)
  have hβ_mem : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ wedgeSet W := fun t ht =>
    pathConcat_mem hseg_mem (fun u hu => polyAt_mem_wedgeSet W (by
      have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg _
      have hQ0 : (0 : ℝ) ≤ (Q1 : ℝ) := Nat.cast_nonneg _
      have hxN : (x : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ x.isLt
      have hQN : (Q1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ Q1.isLt
      exact ⟨by nlinarith [hu.1, hu.2], by nlinarith [hu.1, hu.2]⟩)) ht
  have hdisj : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, α s ≠ β t := by
    intro s hs t ht heq
    unfold β pathConcat at heq
    split_ifs at heq with hhalf
    · have h1 : ‖α s - (W.L : ℂ)‖ ≤ 1 := hα_ball s hs
      have h2 := hseg_far (2 * t) ⟨by linarith [ht.1], by linarith⟩
      rw [heq] at h1; linarith
    · have hu : 2 * t - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
      have hinj := polyAt_injOn hgp hsimp
      have hmemI : ∀ (a b : Fin (N + 1)) (u : ℝ), u ∈ Icc (0 : ℝ) 1 →
          (1 - u) * (a : ℝ) + u * (b : ℝ) ∈ Icc (0 : ℝ) (N : ℝ) := fun a b u hu' => by
        have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
        have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
        have haN : (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ a.isLt
        have hbN : (b : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt_succ b.isLt
        exact ⟨by nlinarith [hu'.1, hu'.2], by nlinarith [hu'.1, hu'.2]⟩
      have ht_eq := hinj (hmemI A B s hs) (hmemI x Q1 (2 * t - 1) hu) heq
      have hle_B : (1 - s) * (A : ℝ) + s * (B : ℝ) ≤ (B : ℝ) := by
        have hABr : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB.le
        nlinarith [hs.1, hs.2]
      have hgt_B : (B : ℝ) < (1 - (2 * t - 1)) * (x : ℝ) + (2 * t - 1) * (Q1 : ℝ) := by
        have hBxr : (B : ℝ) < (x : ℝ) := by exact_mod_cast hBx
        have hBQr : (B : ℝ) < (Q1 : ℝ) := by exact_mod_cast hBQ1
        nlinarith [hu.1, hu.2]
      linarith
  -- Show 1 < L (so tA > 0 and tB > 0 automatically!)
  have h1_lt_L : 1 < W.L := by
    have hW_le_L : ‖Wpt - (W.L : ℂ)‖ ≤ W.L := by
      rcases hhit with hbot0 | htop0
      · have hcr0 : cross (dir (-W.u_lo)) Wpt = 0 := by
          rw [hWpt_eq, cross_add_right, cross_smul_right]; exact hbot0
        have hdec := wedge_coord_decomp (-W.u_lo) Wpt
        rw [show -W.u_lo + Real.pi / 6 = Real.pi / 6 - W.u_lo by ring, hcr0, mul_zero, zero_smul, add_zero] at hdec
        set tW : ℝ := -2 * cross (dir (Real.pi / 6 - W.u_lo)) Wpt
        have htW0 : 0 ≤ tW := by dsimp [tW]; linarith [hWpt_mem.2.1]
        have htW_le : tW ≤ W.L * Real.cos (-W.u_lo) := by
          rw [Real.cos_neg]; exact onUbot_le_L_cos W htW0 (hdec ▸ hWpt_mem)
        have hle := ray_dist_le_of_le (L := W.L) (φ := -W.u_lo) le_rfl htW0 htW_le
        rw [zero_smul, zero_sub, norm_neg, Complex.norm_of_nonneg W.hL.le, ← hdec] at hle
        exact hle
      · have hcr0 : cross (dir (Real.pi / 6 - W.u_lo)) Wpt = 0 := by
          rw [hWpt_eq, cross_add_right, cross_smul_right]; dsimp [ft0, ft'] at htop0; linarith
        have hdec := wedge_coord_decomp (-W.u_lo) Wpt
        rw [show -W.u_lo + Real.pi / 6 = Real.pi / 6 - W.u_lo by ring, hcr0, mul_zero, zero_smul, zero_add] at hdec
        set tW : ℝ := 2 * cross (dir (-W.u_lo)) Wpt
        have htW0 : 0 ≤ tW := by dsimp [tW]; linarith [hWpt_mem.1]
        have htW_le : tW ≤ W.L * Real.cos (Real.pi / 6 - W.u_lo) :=
          onUtop_le_L_cos W htW0 (hdec ▸ hWpt_mem)
        have hle := ray_dist_le_of_le (L := W.L) (φ := Real.pi / 6 - W.u_lo) le_rfl htW0 htW_le
        rw [zero_smul, zero_sub, norm_neg, Complex.norm_of_nonneg W.hL.le, ← hdec] at hle
        exact hle
    linarith
  have htA_pos : 0 < tA := by
    rcases eq_or_lt_of_le hOnA.1 with h0 | hpos
    · exfalso; have h1 := hnone A hAB.le
      rw [hOnA.2, ← h0, zero_smul, zero_sub, norm_neg, Complex.norm_of_nonneg W.hL.le] at h1
      linarith
    · exact hpos
  have htB_pos : 0 < tB := by
    rcases eq_or_lt_of_le hOnB.1 with h0 | hpos
    · exfalso; have h1 := hnone B le_rfl
      rw [hOnB.2, ← h0, zero_smul, zero_sub, norm_neg, Complex.norm_of_nonneg W.hL.le] at h1
      linarith
    · exact hpos
  -- Split on whether Wpt lies on U_bot or strictly on U_top!
  have hcase_bot : ∀ tW : ℝ, 0 ≤ tW → Wpt = tW • dir (-W.u_lo) → False := by
    intro tW htW0 hW_eq
    have htW_le : tW ≤ W.L * Real.cos (-W.u_lo) := by
      rw [Real.cos_neg]; exact onUbot_le_L_cos W htW0 (hW_eq ▸ hWpt_mem)
    have htW_lt_A : tW < tA := ray_lt_of_dist_lt hOnA.1 htW0 htW_le (by
      rw [← hOnA.2, ← hW_eq]; linarith [hnone A hAB.le])
    have htQ1_le : tQ1 ≤ W.L := by
      have h1 := onUbot_le_L_cos W hOnQ1.1 (hOnQ1.2 ▸ ⟨W.hU_bot Q1, W.hU_top Q1, W.hV_top Q1, W.hV_bot Q1⟩)
      have h2 : Real.cos W.u_lo ≤ 1 := Real.cos_le_one _
      nlinarith [W.hL]
    have hrot_dir : ∀ φ, rotC W.u_lo (dir φ) = dir (φ + W.u_lo) := fun φ => by
      simp only [rotC_apply, dir, ← Complex.exp_add]; congr 1; push_cast; ring
    have hrot_bot : ∀ t : ℝ, rotC W.u_lo (t • dir (-W.u_lo)) = (t : ℂ) := fun t => by
      rw [map_smul, hrot_dir, neg_add_cancel, dir_zero, Complex.real_smul, mul_one]
    have hrot_top : rotC W.u_lo (tB • dir (Real.pi / 6 - W.u_lo)) = tB • dir (Real.pi / 6) := by
      rw [map_smul, hrot_dir, show Real.pi / 6 - W.u_lo + W.u_lo = Real.pi / 6 by ring]
    have hB_re : (tB • dir (Real.pi / 6)).re ≤ W.L := by
      rw [← hrot_top, ← hOnB.2]
      exact (wedgeSet_rot_bounds W ⟨W.hU_bot B, W.hU_top B, W.hV_top B, W.hV_bot B⟩).2.1
    exact crossing_three_on_bot htW0 htW_lt_A hAQ htQ1_le htB_pos hB_re
      ((rotC W.u_lo).continuous.comp_continuousOn hα_cont)
      ((rotC W.u_lo).continuous.comp_continuousOn hβ_cont)
      (fun s hs => wedgeSet_rot_bounds W (hα_mem s hs))
      (fun t ht => wedgeSet_rot_bounds W (hβ_mem t ht))
      (by change rotC W.u_lo (α 0) = (tA : ℂ); rw [show α 0 = r A from polySubpath_zero r A B, hOnA.2, hrot_bot])
      (by change rotC W.u_lo (α 1) = tB • dir (Real.pi / 6); rw [show α 1 = r B from polySubpath_one r A B, hOnB.2, hrot_top])
      (by change rotC W.u_lo (β 0) = (tW : ℂ); rw [show β 0 = Wpt by simp [β, pathConcat_zero, segPath], hW_eq, hrot_bot])
      (by change rotC W.u_lo (β 1) = (tQ1 : ℂ); rw [show β 1 = r Q1 by simp [β, pathConcat_one, polySubpath_one], hOnQ1.2, hrot_bot])
      (fun s hs t ht heq => hdisj s hs t ht ((rotC W.u_lo).injective heq))
  rcases hhit with hbot0 | htop0
  · have hcr0 : cross (dir (-W.u_lo)) Wpt = 0 := by
      rw [hWpt_eq, cross_add_right, cross_smul_right]; exact hbot0
    have hdec := wedge_coord_decomp (-W.u_lo) Wpt
    rw [show -W.u_lo + Real.pi / 6 = Real.pi / 6 - W.u_lo by ring, hcr0, mul_zero, zero_smul, add_zero] at hdec
    exact hcase_bot (-2 * cross (dir (Real.pi / 6 - W.u_lo)) Wpt) (by linarith [hWpt_mem.2.1]) hdec
  · have hcr0 : cross (dir (Real.pi / 6 - W.u_lo)) Wpt = 0 := by
      rw [hWpt_eq, cross_add_right, cross_smul_right]; dsimp [ft0, ft'] at htop0; linarith
    have hdec := wedge_coord_decomp (-W.u_lo) Wpt
    rw [show -W.u_lo + Real.pi / 6 = Real.pi / 6 - W.u_lo by ring, hcr0, mul_zero, zero_smul, zero_add] at hdec
    set tW : ℝ := 2 * cross (dir (-W.u_lo)) Wpt
    have htW0 : 0 ≤ tW := by dsimp [tW]; linarith [hWpt_mem.1]
    rcases eq_or_lt_of_le htW0 with h0 | htW_pos
    · exact hcase_bot 0 le_rfl (by rw [hdec, ← h0, zero_smul, zero_smul])
    · have htW_le : tW ≤ W.L * Real.cos (Real.pi / 6 - W.u_lo) :=
        onUtop_le_L_cos W htW0 (hdec ▸ hWpt_mem)
      have htW_lt_B : tW < tB := ray_lt_of_dist_lt hOnB.1 htW0 htW_le (by
        rw [← hOnB.2, ← hdec]; linarith [hnone B le_rfl])
      exact crossing_two_on_bot_two_on_top htA_pos hAQ htW_pos htW_lt_B hα_cont
        (hβ_cont.comp (by fun_prop : ContinuousOn (fun t : ℝ => 1 - t) (Icc 0 1))
          (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩))
        (fun s hs => ⟨(hα_mem s hs).1, (hα_mem s hs).2.1⟩)
        (fun t ht => let h := hβ_mem (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩; ⟨h.1, h.2.1⟩)
        (by simp [α, polySubpath_zero, hOnA.2])
        (by simp [α, polySubpath_one, hOnB.2])
        (by simp [β, pathConcat_one, polySubpath_one, hOnQ1.2])
        (by simp [β, pathConcat_zero, segPath, hdec])
        (fun s hs t ht heq => hdisj s hs (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ heq)

lemma exists_far_after_Vtop {N : ℕ} {r : Fin (N + 1) → ℂ}
    (hgp : GenPos r) (hsimp : IsSimplePoly r) (huncov : ¬ CoveredUnit r)
    (W : TwoWedgeBase r) {D E F : Fin (N + 1)} {tD tE tF : ℝ}
    (hDE : D < E) (hEF : E < F) (hFD : tF < tD)
    (hOnD : OnVbot W D tD) (hOnE : OnVtop W E tE) (hOnF : OnVbot W F tF) :
    ∃ y : Fin (N + 1), E ≤ y ∧ 1 < ‖r y‖ := by
  let r' : Fin (N + 1) → ℂ := fun k => (W.L : ℂ) - starRingEnd ℂ (r k.rev)
  have hr'_eq : ∀ k, r' k = rotC Real.pi (starRingEnd ℂ (r k.rev)) + (W.L : ℂ) := fun k => by
    simp only [r', rotC_apply, show (Real.pi : ℂ) * I = Real.pi * I from rfl, Complex.exp_pi_mul_I]
    ring
  have hgp' : GenPos r' := by
    have h1 := genPos_of_rot_trans (genPos_of_conj (genPos_of_rev hgp)) Real.pi (W.L : ℂ)
    convert h1 using 1; funext k; exact hr'_eq k
  have hsimp' : IsSimplePoly r' := by
    have h1 := isSimplePoly_of_rot_trans (isSimplePoly_of_conj (isSimplePoly_of_rev hsimp)) Real.pi (W.L : ℂ)
    convert h1 using 1; funext k; exact hr'_eq k
  have huncov' : ¬ CoveredUnit r' := fun h => huncov (coveredUnit_of_rev (coveredUnit_of_conj
    (coveredUnit_of_rot_trans Real.pi (W.L : ℂ) (by convert h using 1; funext k; exact (hr'_eq k).symm))))
  let W' := twoWedgeBase_flipX W
  have hOnF' : OnUbot W' F.rev tF := ⟨hOnF.1, by
    show (W.L : ℂ) - starRingEnd ℂ (r F.rev.rev) = tF • dir (-W.v_lo)
    rw [Fin.rev_rev, hOnF.2, dir_neg]; simp [Complex.real_smul]⟩
  have hOnE' : OnUtop W' E.rev tE := ⟨hOnE.1, by
    show (W.L : ℂ) - starRingEnd ℂ (r E.rev.rev) = tE • dir (Real.pi / 6 - W.v_lo)
    rw [Fin.rev_rev, hOnE.2, show dir (Real.pi / 6 - W.v_lo) = starRingEnd ℂ (dir (-(Real.pi / 6 - W.v_lo))) by
      rw [← dir_neg, neg_neg]]; simp [Complex.real_smul]⟩
  have hOnD' : OnUbot W' D.rev tD := ⟨hOnD.1, by
    show (W.L : ℂ) - starRingEnd ℂ (r D.rev.rev) = tD • dir (-W.v_lo)
    rw [Fin.rev_rev, hOnD.2, dir_neg]; simp [Complex.real_smul]⟩
  obtain ⟨x', hx'E, hfar⟩ := exists_far_before_B hgp' hsimp' huncov' W'
    (Fin.rev_lt_rev.mpr hEF) (Fin.rev_lt_rev.mpr hDE) hFD hOnF' hOnE' hOnD'
  refine ⟨x'.rev, Fin.rev_le_rev.mp (by simpa using hx'E), ?_⟩
  have hnorm : ‖r' x' - (W'.L : ℂ)‖ = ‖r x'.rev‖ := by
    dsimp [r', W', twoWedgeBase_flipX]
    rw [show (W.L : ℂ) - starRingEnd ℂ (r x'.rev) - (W.L : ℂ) = -(starRingEnd ℂ (r x'.rev)) by ring,
      norm_neg, Complex.norm_conj]
  rwa [hnorm] at hfar

lemma exists_far_after_Vbot {N : ℕ} {r : Fin (N + 1) → ℂ}
    (hgp : GenPos r) (hsimp : IsSimplePoly r) (huncov : ¬ CoveredUnit r)
    (W : TwoWedgeBase r) {QV E F : Fin (N + 1)} {tQV tE tF : ℝ}
    (hQVE : QV < E) (hEF : E < F) (hFQV : tF < tQV)
    (hOnQV : OnVtop W QV tQV) (hOnE : OnVbot W E tE) (hOnF : OnVtop W F tF) :
    ∃ y : Fin (N + 1), E ≤ y ∧ 1 < ‖r y‖ := by
  let r' : Fin (N + 1) → ℂ := fun k => (W.L : ℂ) - r k.rev
  have hr'_eq : ∀ k, r' k = rotC Real.pi (r k.rev) + (W.L : ℂ) := fun k => by
    simp only [r', rotC_apply, Complex.exp_pi_mul_I]; ring
  have hgp' : GenPos r' := by
    have h1 := genPos_of_rot_trans (genPos_of_rev hgp) Real.pi (W.L : ℂ)
    convert h1 using 1; funext k; exact hr'_eq k
  have hsimp' : IsSimplePoly r' := by
    have h1 := isSimplePoly_of_rot_trans (isSimplePoly_of_rev hsimp) Real.pi (W.L : ℂ)
    convert h1 using 1; funext k; exact hr'_eq k
  have huncov' : ¬ CoveredUnit r' := fun h => huncov (coveredUnit_of_rev
    (coveredUnit_of_rot_trans Real.pi (W.L : ℂ) (by convert h using 1; funext k; exact (hr'_eq k).symm)))
  let W' := twoWedgeBase_rot180 W
  have hOnF' : OnUbot W' F.rev tF := ⟨hOnF.1, by
    show (W.L : ℂ) - r F.rev.rev = tF • dir (-(Real.pi / 6 - W.v_lo))
    rw [Fin.rev_rev, hOnF.2]; ring⟩
  have hOnE' : OnUtop W' E.rev tE := ⟨hOnE.1, by
    show (W.L : ℂ) - r E.rev.rev = tE • dir (Real.pi / 6 - (Real.pi / 6 - W.v_lo))
    rw [Fin.rev_rev, hOnE.2, show Real.pi / 6 - (Real.pi / 6 - W.v_lo) = W.v_lo by ring]; ring⟩
  have hOnQV' : OnUbot W' QV.rev tQV := ⟨hOnQV.1, by
    show (W.L : ℂ) - r QV.rev.rev = tQV • dir (-(Real.pi / 6 - W.v_lo))
    rw [Fin.rev_rev, hOnQV.2]; ring⟩
  obtain ⟨x', hx'E, hfar⟩ := exists_far_before_B hgp' hsimp' huncov' W'
    (Fin.rev_lt_rev.mpr hEF) (Fin.rev_lt_rev.mpr hQVE) hFQV hOnF' hOnE' hOnQV'
  refine ⟨x'.rev, Fin.rev_le_rev.mp (by simpa using hx'E), ?_⟩
  have hnorm : ‖r' x' - (W'.L : ℂ)‖ = ‖r x'.rev‖ := by
    dsimp [r', W', twoWedgeBase_rot180]
    rw [show (W.L : ℂ) - r x'.rev - (W.L : ℂ) = -(r x'.rev) by ring, norm_neg]
  rwa [hnorm] at hfar

/- Section 5B: Sector chord bounds, reflection algebra, and Fig. 7 obtuse-angle lemma -/

lemma sector60_left_bound {a x : ℂ}
    (ha : Real.sqrt 3 * a.re + a.im ≤ 0) (hx_re : x.re ≤ 0) (hx_im : 0 ≤ x.im) :
    ‖x‖ / 2 ≤ ‖a - x‖ - x.re := by
  have hsq3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq3_lt2 : Real.sqrt 3 < 2 := by nlinarith
  have hx_norm_sq : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  by_cases hcase : Real.sqrt 3 * x.re + x.im ≤ 0
  · have hsq : ‖x‖ ^ 2 ≤ (-2 * x.re) ^ 2 := by rw [hx_norm_sq]; nlinarith
    have hle : ‖x‖ ≤ -2 * x.re := by nlinarith [norm_nonneg x]
    linarith [norm_nonneg (a - x)]
  · push Not at hcase
    have hcs : (Real.sqrt 3 / 2) * x.re + (1 / 2) * x.im ≤ ‖a - x‖ := by
      have hdot : dotC ((Real.sqrt 3 / 2 : ℝ) + (1 / 2 : ℝ) * I) (x - a) ≤ ‖x - a‖ := by
        have h1 : (dotC ((Real.sqrt 3 / 2 : ℝ) + (1 / 2 : ℝ) * I) (x - a)) ^ 2 ≤ ‖x - a‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; unfold dotC
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, add_zero,
            add_im, mul_im, zero_add]
          have hrem : (x - a).re ^ 2 + (x - a).im ^ 2 -
              ((Real.sqrt 3 / 2) * (x - a).re + (1 / 2) * (x - a).im) ^ 2 =
              ((1 / 2) * (x - a).re - (Real.sqrt 3 / 2) * (x - a).im) ^ 2 := by
            linear_combination -((x - a).re ^ 2 + (x - a).im ^ 2) / 4 * (hsq3_sq - 3)
          nlinarith [sq_nonneg ((1 / 2) * (x - a).re - (Real.sqrt 3 / 2) * (x - a).im)]
        nlinarith [norm_nonneg (x - a)]
      rw [norm_sub_rev] at hdot
      unfold dotC at hdot
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, add_zero,
        add_im, mul_im, zero_add, sub_re, sub_im] at hdot
      linarith
    have hfac : ((Real.sqrt 3 - 2) * x.re + x.im) ^ 2 - ‖x‖ ^ 2 =
        2 * (2 - Real.sqrt 3) * (-x.re) * (Real.sqrt 3 * x.re + x.im) := by
      rw [hx_norm_sq]; linear_combination -x.re ^ 2 * hsq3_sq
    have hprod : 0 ≤ 2 * (2 - Real.sqrt 3) * (-x.re) * (Real.sqrt 3 * x.re + x.im) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have hsq : ‖x‖ ^ 2 ≤ ((Real.sqrt 3 - 2) * x.re + x.im) ^ 2 := by linarith
    have hnn : 0 ≤ (Real.sqrt 3 - 2) * x.re + x.im := by nlinarith
    have hle : ‖x‖ ≤ (Real.sqrt 3 - 2) * x.re + x.im := by nlinarith [norm_nonneg x]
    linarith

lemma sector60_right_bound {y f : ℂ}
    (hf : -Real.sqrt 3 * f.re + f.im ≤ 0) (hy_re : 0 ≤ y.re) (hy_im : 0 ≤ y.im) :
    ‖y‖ / 2 ≤ ‖y - f‖ + y.re := by
  let a' : ℂ := -starRingEnd ℂ f
  let x' : ℂ := -starRingEnd ℂ y
  have h := sector60_left_bound (a := a') (x := x')
    (by simp [a']; linarith) (by simp [x']; linarith) (by simp [x']; exact hy_im)
  have hnx : ‖x'‖ = ‖y‖ := by simp [x']
  have hnd : ‖a' - x'‖ = ‖y - f‖ := by
    have : a' - x' = starRingEnd ℂ (y - f) := by simp [a', x']; ring
    rw [this, Complex.norm_conj]
  have hre : x'.re = -y.re := by simp [x']
  rw [hnx, hnd, hre] at h; linarith

lemma sector60_chain_gt_one {a x y f : ℂ}
    (ha : Real.sqrt 3 * a.re + a.im ≤ 0) (hf : -Real.sqrt 3 * f.re + f.im ≤ 0)
    (hx_re : x.re ≤ 0) (hx_im : 0 ≤ x.im) (hy_re : 0 ≤ y.re) (hy_im : 0 ≤ y.im)
    (hx_gt : 1 < ‖x‖) (hy_gt : 1 < ‖y‖) :
    1 < ‖a - x‖ + ‖x - y‖ + ‖y - f‖ := by
  have hL := sector60_left_bound ha hx_re hx_im
  have hR := sector60_right_bound hf hy_re hy_im
  have hM : y.re - x.re ≤ ‖x - y‖ := by
    have h1 := Complex.abs_re_le_norm (y - x)
    rw [norm_sub_rev, sub_re] at h1
    exact (le_abs_self _).trans h1
  linarith

lemma case24_neg_xY_bound {a x y f yStar : ℂ} {c ψ θs : ℝ}
    (ha : Real.sqrt 3 * a.re + a.im ≤ 0) (hf : -Real.sqrt 3 * f.re + f.im ≤ 0)
    (hx_re : x.re ≤ 0) (hx_im : 0 ≤ x.im) (hx_gt : 1 < ‖x‖)
    (hy_re : y.re < 0) (hc : 0 ≤ c) (hy_eq : y = yStar + c • dir ψ)
    (hψ_lo : 2 * Real.pi / 3 ≤ ψ) (hψ_hi : ψ ≤ 5 * Real.pi / 6)
    (hyStar_eq : yStar = ‖yStar‖ • dir θs) (hyStar_gt : 1 < ‖yStar‖)
    (hθs_hi : θs ≤ Real.pi / 2) (hcoupled : 2 * ψ - θs ≤ 3 * Real.pi / 2) :
    1 < ‖a - x‖ + ‖x - y‖ + ‖y - f‖ := by
  have hsq3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hL := sector60_left_bound ha hx_re hx_im
  have hM : y.re - x.re ≤ ‖x - y‖ := by
    have h1 := Complex.abs_re_le_norm (y - x)
    rw [norm_sub_rev, sub_re] at h1
    exact (le_abs_self _).trans h1
  have hR : -(Real.sqrt 3 / 2) * y.re + (1 / 2) * y.im ≤ ‖y - f‖ := by
    have hdot : dotC (-(Real.sqrt 3 / 2 : ℝ) + (1 / 2 : ℝ) * I) (y - f) ≤ ‖y - f‖ := by
      have h1 : (dotC (-(Real.sqrt 3 / 2 : ℝ) + (1 / 2 : ℝ) * I) (y - f)) ^ 2 ≤ ‖y - f‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; unfold dotC
        simp only [add_re, neg_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, add_zero,
          add_im, neg_im, neg_zero, mul_im, zero_add]
        have hrem : (y - f).re ^ 2 + (y - f).im ^ 2 -
            (-(Real.sqrt 3 / 2) * (y - f).re + (1 / 2) * (y - f).im) ^ 2 =
            ((1 / 2) * (y - f).re + (Real.sqrt 3 / 2) * (y - f).im) ^ 2 := by
          linear_combination -((y - f).re ^ 2 + (y - f).im ^ 2) / 4 * (hsq3_sq - 3)
        nlinarith [sq_nonneg ((1 / 2) * (y - f).re + (Real.sqrt 3 / 2) * (y - f).im)]
      nlinarith [norm_nonneg (y - f)]
    unfold dotC at hdot
    simp only [add_re, neg_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, add_zero,
      add_im, neg_im, neg_zero, mul_im, zero_add, sub_re, sub_im] at hdot
    linarith
  -- Show (1 - √3 / 2) * y.re + (1 / 2) * y.im > 1 / 2!
  have hcos_neg : Real.cos ψ < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hsin_pos : 0 < Real.sin ψ :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hslope : 0 ≤ Real.sqrt 3 * Real.sin ψ + Real.cos ψ := by
    have h1 : Real.sqrt 3 * Real.sin ψ + Real.cos ψ = 2 * Real.sin (ψ + Real.pi / 6) := by
      rw [Real.sin_add, Real.cos_pi_div_six, Real.sin_pi_div_six]; ring
    rw [h1]
    have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ ψ + Real.pi / 6 by linarith [Real.pi_pos])
      (show ψ + Real.pi / 6 ≤ Real.pi by linarith)
    linarith
  have hsin_diff : -Real.cos ψ ≤ Real.sin (ψ - θs) := by
    have h1 : -Real.cos ψ = Real.sin (ψ - Real.pi / 2) := by
      rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
    rw [h1]
    have hmid : Real.sin (ψ - θs) - Real.sin (ψ - Real.pi / 2) =
        2 * Real.sin ((Real.pi / 2 - θs) / 2) * Real.cos ((2 * ψ - θs - Real.pi / 2) / 2) := by
      have := Real.sin_sub_sin (ψ - θs) (ψ - Real.pi / 2)
      rw [show (ψ - θs - (ψ - Real.pi / 2)) / 2 = (Real.pi / 2 - θs) / 2 by ring,
        show (ψ - θs + (ψ - Real.pi / 2)) / 2 = (2 * ψ - θs - Real.pi / 2) / 2 by ring] at this
      linarith
    have hs1 : 0 ≤ Real.sin ((Real.pi / 2 - θs) / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
    have hc1 : 0 ≤ Real.cos ((2 * ψ - θs - Real.pi / 2) / 2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
    nlinarith
  have hcross_yS : yStar.re * Real.sin ψ - yStar.im * Real.cos ψ = ‖yStar‖ * Real.sin (ψ - θs) := by
    have h1 : cross yStar (dir ψ) = ‖yStar‖ * Real.sin (ψ - θs) := by
      conv_lhs => rw [hyStar_eq]
      rw [cross_smul_left, cross_dir_dir]
    unfold cross at h1; rw [dir_re, dir_im] at h1; linarith
  have hy_re_eq : y.re = yStar.re + c * Real.cos ψ := by rw [hy_eq]; simp [dir_re]
  have hy_im_eq : y.im = yStar.im + c * Real.sin ψ := by rw [hy_eq]; simp [dir_im]
  have hlin_mul : 0 < (-Real.cos ψ) * ((1 - Real.sqrt 3 / 2) * y.re + (1 / 2) * y.im - 1 / 2) := by
    have hid : (-Real.cos ψ) * ((1 - Real.sqrt 3 / 2) * y.re + (1 / 2) * y.im - 1 / 2) =
        ((1 - Real.sqrt 3 / 2) * (-Real.cos ψ) - (1 / 2) * Real.sin ψ) * y.re +
        (1 / 2) * (yStar.re * Real.sin ψ - yStar.im * Real.cos ψ + Real.cos ψ) := by
      rw [hy_re_eq, hy_im_eq]; ring
    rw [hid, hcross_yS]
    have hcoef_neg : (1 - Real.sqrt 3 / 2) * (-Real.cos ψ) - (1 / 2) * Real.sin ψ < 0 := by
      have hsq3_lt2 : Real.sqrt 3 < 2 := by nlinarith
      nlinarith
    have hterm1 : 0 < ((1 - Real.sqrt 3 / 2) * (-Real.cos ψ) - (1 / 2) * Real.sin ψ) * y.re :=
      mul_pos_of_neg_of_neg hcoef_neg hy_re
    have hterm2 : 0 < ‖yStar‖ * Real.sin (ψ - θs) + Real.cos ψ := by nlinarith
    linarith
  have hlin : 1 / 2 < (1 - Real.sqrt 3 / 2) * y.re + (1 / 2) * y.im := by nlinarith
  linarith

noncomputable def reflectLine (P : ℂ) (φ : ℝ) (z : ℂ) : ℂ :=
  P + starRingEnd ℂ (z - P) * dir (2 * φ)

lemma reflectLine_dist (P : ℂ) (φ : ℝ) (z w : ℂ) :
    ‖reflectLine P φ z - reflectLine P φ w‖ = ‖z - w‖ := by
  have h1 : reflectLine P φ z - reflectLine P φ w = starRingEnd ℂ (z - w) * dir (2 * φ) := by
    unfold reflectLine; simp only [map_sub]; ring
  rw [h1, norm_mul, Complex.norm_conj, dir_norm, mul_one]

lemma reflectLine_fix_ray (P : ℂ) (φ t : ℝ) :
    reflectLine P φ (P + t • dir φ) = P + t • dir φ := by
  unfold reflectLine
  rw [add_sub_cancel_left, Complex.real_smul, map_mul, Complex.conj_ofReal, ← dir_neg,
    mul_assoc, ← dir_add, show -φ + 2 * φ = φ by ring]

lemma reflectLine_comp (P : ℂ) (φ1 φ2 : ℝ) (z : ℂ) :
    reflectLine P φ2 (reflectLine P φ1 z) = P + (z - P) * dir (2 * (φ2 - φ1)) := by
  unfold reflectLine
  rw [add_sub_cancel_left, map_mul, Complex.conj_conj, ← dir_neg, mul_assoc, ← dir_add]
  congr 2; congr 1; ring

lemma reflectLine_dir (P : ℂ) (φ ψ : ℝ) (t : ℝ) :
    reflectLine P φ (P + t • dir ψ) = P + t • dir (2 * φ - ψ) := by
  unfold reflectLine
  rw [add_sub_cancel_left, Complex.real_smul, map_mul, Complex.conj_ofReal, ← dir_neg,
    mul_assoc, ← dir_add, show -ψ + 2 * φ = 2 * φ - ψ by ring, Complex.real_smul]

lemma fig7_obtuse_dist {L u_lo tA : ℝ} {X : ℂ}
    (hL : 0 ≤ L) (hu0 : 0 ≤ u_lo) (hule : u_lo ≤ Real.pi / 6) (htA : tA ≤ L * Real.cos u_lo)
    (hX_bot : 0 ≤ cross (dir (-u_lo)) X) :
    ‖X - (L : ℂ)‖ ≤ ‖(tA • dir (-u_lo) - ‖X - tA • dir (-u_lo)‖ • dir (-u_lo)) - (L : ℂ)‖ := by
  set A : ℂ := tA • dir (-u_lo)
  set d : ℝ := ‖X - A‖
  set w : ℂ := A - (L : ℂ)
  have hsq_X : ‖X - (L : ℂ)‖ ^ 2 = ‖w‖ ^ 2 + d ^ 2 + 2 * dotC w (X - A) := by
    have hsplit : X - (L : ℂ) = w + (X - A) := by dsimp [w]; ring
    rw [hsplit, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
    unfold dotC; simp only [add_re, add_im]; ring
  have hsq_bar : ‖(A - d • dir (-u_lo)) - (L : ℂ)‖ ^ 2 =
      ‖w‖ ^ 2 + d ^ 2 + 2 * d * (-dotC w (dir (-u_lo))) := by
    have hsplit : (A - d • dir (-u_lo)) - (L : ℂ) = w + (-d) • dir (-u_lo) := by
      rw [show w = A - (L : ℂ) from rfl, Complex.real_smul, Complex.real_smul]; push_cast; ring
    rw [hsplit, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    unfold dotC
    simp only [add_re, add_im, smul_re, smul_im, smul_eq_mul, dir_re, dir_im]
    have hsc := Real.cos_sq_add_sin_sq (-u_lo)
    linear_combination d ^ 2 * hsc
  let u1 : ℂ := dir (-u_lo)
  let a1 : ℝ := dotC u1 (X - A)
  let a2 : ℝ := cross u1 (X - A)
  have ha2_nn : 0 ≤ a2 := by
    change 0 ≤ cross (dir (-u_lo)) (X - tA • dir (-u_lo))
    rw [cross_sub_right, cross_smul_right, cross_self, mul_zero, sub_zero]; exact hX_bot
  have ha1_ge : -d ≤ a1 := by
    have h1 : a1 ^ 2 ≤ d ^ 2 := by
      dsimp [a1, d, u1]
      rw [Complex.sq_norm, Complex.normSq_apply]; unfold dotC
      rw [dir_re, dir_im]
      have hsc := Real.cos_sq_add_sin_sq (-u_lo)
      have hrem : (X - A).re ^ 2 + (X - A).im ^ 2 -
          (Real.cos (-u_lo) * (X - A).re + Real.sin (-u_lo) * (X - A).im) ^ 2 =
          (Real.cos (-u_lo) * (X - A).im - Real.sin (-u_lo) * (X - A).re) ^ 2 := by
        linear_combination -((X - A).re ^ 2 + (X - A).im ^ 2) * hsc
      nlinarith [sq_nonneg (Real.cos (-u_lo) * (X - A).im - Real.sin (-u_lo) * (X - A).re)]
    nlinarith [norm_nonneg (X - A)]
  have hw_u1 : dotC w u1 ≤ 0 := by
    change dotC (tA • dir (-u_lo) - (L : ℂ)) (dir (-u_lo)) ≤ 0
    unfold dotC
    simp only [sub_re, sub_im, smul_re, smul_im, smul_eq_mul, dir_re, dir_im, ofReal_re, ofReal_im, sub_zero]
    have hsc := Real.cos_sq_add_sin_sq (-u_lo)
    have : (tA * Real.cos (-u_lo) - L) * Real.cos (-u_lo) + tA * Real.sin (-u_lo) * Real.sin (-u_lo) =
        tA * (Real.cos (-u_lo) ^ 2 + Real.sin (-u_lo) ^ 2) - L * Real.cos (-u_lo) := by ring
    rw [this, hsc, mul_one, Real.cos_neg]; linarith
  have hw_u2 : cross u1 w ≤ 0 := by
    change cross (dir (-u_lo)) (tA • dir (-u_lo) - (L : ℂ)) ≤ 0
    rw [cross_sub_right, cross_smul_right, cross_self, mul_zero, zero_sub]
    unfold cross; rw [dir_re, dir_im, Real.sin_neg]; simp
    have hsin : 0 ≤ Real.sin u_lo := Real.sin_nonneg_of_nonneg_of_le_pi hu0 (by linarith [Real.pi_pos])
    nlinarith
  have hdecomp : dotC w (X - A) = a1 * dotC w u1 + a2 * cross u1 w := by
    dsimp [a1, a2, u1]; unfold dotC cross; rw [dir_re, dir_im]
    have hsc := Real.cos_sq_add_sin_sq (-u_lo)
    linear_combination -(w.re * (X - A).re + w.im * (X - A).im) * (hsc - 1)
  have hle_sq : ‖X - (L : ℂ)‖ ^ 2 ≤ ‖(A - d • dir (-u_lo)) - (L : ℂ)‖ ^ 2 := by
    rw [hsq_X, hsq_bar, hdecomp]
    nlinarith [hw_u1, hw_u2, ha1_ge, ha2_nn]
  nlinarith [norm_nonneg (X - (L : ℂ)), norm_nonneg ((A - d • dir (-u_lo)) - (L : ℂ))]

/- Section 5C: Contradictions for Cases 1, 3, and 2/4 -/

lemma chain6_le_polyLen {N : ℕ} (r : Fin (N + 1) → ℂ) {a b c d e f : Fin (N + 1)}
    (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) (h5 : e ≤ f) :
    ‖r b - r a‖ + ‖r c - r b‖ + ‖r d - r c‖ + ‖r e - r d‖ + ‖r f - r e‖ ≤ polyLen r := by
  have hch : ([a, b, c, d, e, f] : List (Fin (N + 1))).IsChain (· ≤ ·) := by
    simp [h1, h2, h3, h4, h5]
  have h := chain_le_polyLen r [a, b, c, d, e, f] hch
  simp only [List.tail_cons, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
    List.sum_nil, add_zero] at h
  linarith

lemma chain7_le_polyLen {N : ℕ} (r : Fin (N + 1) → ℂ) {a b c d e f g : Fin (N + 1)}
    (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) (h5 : e ≤ f) (h6 : f ≤ g) :
    ‖r b - r a‖ + ‖r c - r b‖ + ‖r d - r c‖ + ‖r e - r d‖ + ‖r f - r e‖ + ‖r g - r f‖ ≤ polyLen r := by
  have hch : ([a, b, c, d, e, f, g] : List (Fin (N + 1))).IsChain (· ≤ ·) := by
    simp [h1, h2, h3, h4, h5, h6]
  have h := chain_le_polyLen r [a, b, c, d, e, f, g] hch
  simp only [List.tail_cons, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
    List.sum_nil, add_zero] at h
  linarith

lemma chain8_le_polyLen {N : ℕ} (r : Fin (N + 1) → ℂ) {a b c d e f g h : Fin (N + 1)}
    (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) (h5 : e ≤ f) (h6 : f ≤ g) (h7 : g ≤ h) :
    ‖r b - r a‖ + ‖r c - r b‖ + ‖r d - r c‖ + ‖r e - r d‖ + ‖r f - r e‖ + ‖r g - r f‖ + ‖r h - r g‖ ≤
      polyLen r := by
  have hch : ([a, b, c, d, e, f, g, h] : List (Fin (N + 1))).IsChain (· ≤ ·) := by
    simp [h1, h2, h3, h4, h5, h6, h7]
  have h' := chain_le_polyLen r [a, b, c, d, e, f, g, h] hch
  simp only [List.tail_cons, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
    List.sum_nil, add_zero] at h'
  linarith

lemma case1_contradiction {N : ℕ} {r : Fin (N + 1) → ℂ}
    (hgp : GenPos r) (hsimp : IsSimplePoly r) (hlen : polyLen r ≤ 1) (huncov : ¬ CoveredUnit r)
    (W : TwoWedgeBase r) (hcase : IsCase1 W) : False := by
  rcases hcase with ⟨hu0, hv0, A, B, C, D, tA, tB, tC, tD, hAB, hBC, hCD, htAD, hOnA, hOnB, hOnC, hOnD⟩
  have hD_mem : tD • dir (-W.u_lo) ∈ wedgeSet W :=
    hOnD.2 ▸ ⟨W.hU_bot D, W.hU_top D, W.hV_top D, W.hV_bot D⟩
  have htD_le : tD ≤ W.L := by
    have h1 := onUbot_le_L_cos W hOnD.1 hD_mem
    rw [hu0, Real.cos_zero, mul_one] at h1; exact h1
  have hrA_eq : r A = (tA : ℂ) := by
    rw [hOnA.2, hu0, neg_zero, dir_zero, Complex.real_smul, mul_one]
  have hrD_eq : r D = (tD : ℂ) := by
    rw [hOnD.2, hu0, neg_zero, dir_zero, Complex.real_smul, mul_one]
  have hOnA_Vb : OnVbot W A (W.L - tA) := ⟨by linarith, by
    rw [hrA_eq, hv0, dir_zero, Complex.real_smul, mul_one]; push_cast; ring⟩
  have hOnD_Vb : OnVbot W D (W.L - tD) := ⟨by linarith, by
    rw [hrD_eq, hv0, dir_zero, Complex.real_smul, mul_one]; push_cast; ring⟩
  obtain ⟨x, hxB, hx_far⟩ := exists_far_before_B hgp hsimp huncov W hAB (hBC.trans_lt hCD) htAD hOnA hOnB hOnD
  obtain ⟨y, hCy, hy_far⟩ := exists_far_after_Vtop hgp hsimp huncov W (hAB.trans_le hBC) hCD
    (by linarith) hOnA_Vb hOnC hOnD_Vb
  let leftLen : ℝ := if A ≤ x then ‖r x - r A‖ + ‖r B - r x‖ else ‖r A - r x‖ + ‖r B - r A‖
  let rightLen : ℝ := if y ≤ D then ‖r y - r C‖ + ‖r D - r y‖ else ‖r D - r C‖ + ‖r y - r D‖
  have htot_le : leftLen + ‖r C - r B‖ + rightLen ≤ 1 := by
    refine le_trans ?_ hlen
    dsimp [leftLen, rightLen]
    by_cases hAx : A ≤ x <;> by_cases hyD : y ≤ D
    · rw [if_pos hAx, if_pos hyD]
      linarith [chain6_le_polyLen r hAx hxB hBC hCy hyD]
    · push Not at hyD; rw [if_pos hAx, if_neg (not_le.mpr hyD)]
      linarith [chain6_le_polyLen r hAx hxB hBC hCD.le hyD.le]
    · push Not at hAx; rw [if_neg (not_le.mpr hAx), if_pos hyD]
      linarith [chain6_le_polyLen r hAx.le hAB.le hBC hCy hyD]
    · push Not at hAx hyD; rw [if_neg (not_le.mpr hAx), if_neg (not_le.mpr hyD)]
      linarith [chain6_le_polyLen r hAx.le hAB.le hBC hCD.le hyD.le]
  have hleft : ∃ (A_use X_use : ℂ) (sA : ℝ), sA ≤ W.L ∧ A_use = (sA : ℂ) ∧
      1 < ‖X_use - (W.L : ℂ)‖ ∧ 0 ≤ (X_use - (W.L : ℂ)).im ∧
      cross (dir (-(Real.pi / 6))) (X_use - (W.L : ℂ)) ≤ 0 ∧
      ‖A_use - X_use‖ + ‖X_use - r B‖ ≤ leftLen := by
    by_cases hAx : A ≤ x
    · refine ⟨r A, r x, tA, by linarith, hrA_eq, hx_far, ?_, ?_, ?_⟩
      · have h1 := W.hV_bot x; rw [hv0, dir_zero] at h1; unfold cross at h1; simpa using h1
      · have h1 := W.hV_top x; rw [hv0, sub_zero] at h1; exact h1
      · dsimp [leftLen]; rw [if_pos hAx, norm_sub_rev (r A) (r x), norm_sub_rev (r x) (r B)]
    · push Not at hAx
      let sA : ℝ := tA - ‖r x - r A‖
      refine ⟨(sA : ℂ), (sA : ℂ), sA, by linarith [norm_nonneg (r x - r A)], rfl, ?_, ?_, ?_, ?_⟩
      · have htri : ‖r x - (W.L : ℂ)‖ ≤ ‖r x - r A‖ + ‖r A - (W.L : ℂ)‖ := by
          have : r x - (W.L : ℂ) = (r x - r A) + (r A - (W.L : ℂ)) := by ring
          rw [this]; exact norm_add_le _ _
        have hAL : ‖r A - (W.L : ℂ)‖ = W.L - tA := by
          rw [hrA_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonpos (by linarith)]; ring
        have hSL : ‖(sA : ℂ) - (W.L : ℂ)‖ = W.L - sA := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonpos (by dsimp [sA]; linarith [norm_nonneg (r x - r A)])]; ring
        dsimp [sA] at hSL ⊢; linarith
      · simp
      · unfold cross; rw [dir_re, dir_im, Real.sin_neg, Real.sin_pi_div_six]
        simp only [sub_im, ofReal_im, sub_self, mul_zero, sub_re, ofReal_re]
        dsimp [sA]; linarith [norm_nonneg (r x - r A)]
      · dsimp [leftLen]; rw [if_neg (not_le.mpr hAx), sub_self, norm_zero, zero_add]
        have htri : ‖(sA : ℂ) - r B‖ ≤ ‖(sA : ℂ) - r A‖ + ‖r A - r B‖ := by
          have : (sA : ℂ) - r B = ((sA : ℂ) - r A) + (r A - r B) := by ring
          rw [this]; exact norm_add_le _ _
        have hsA_dist : ‖(sA : ℂ) - r A‖ = ‖r x - r A‖ := by
          rw [show (sA : ℂ) - r A = -((‖r x - r A‖ : ℝ) : ℂ) by dsimp [sA]; rw [hrA_eq]; push_cast; ring,
            norm_neg, Complex.norm_of_nonneg (norm_nonneg _)]
        rw [norm_sub_rev (r A) (r x), norm_sub_rev (r B) (r A)]; linarith
  have hright : ∃ (Y_use D_use : ℂ) (sD : ℝ), 0 ≤ sD ∧ D_use = (sD : ℂ) ∧
      1 < ‖Y_use‖ ∧ 0 ≤ Y_use.im ∧ cross (dir (Real.pi / 6)) Y_use ≤ 0 ∧
      ‖r C - Y_use‖ + ‖Y_use - D_use‖ ≤ rightLen := by
    by_cases hyD : y ≤ D
    · refine ⟨r y, r D, tD, hOnD.1, hrD_eq, hy_far, ?_, ?_, ?_⟩
      · have h1 := W.hU_bot y; rw [hu0, neg_zero, dir_zero] at h1; unfold cross at h1; simpa using h1
      · have h1 := W.hU_top y; rw [hu0, sub_zero] at h1; exact h1
      · dsimp [rightLen]; rw [if_pos hyD, norm_sub_rev (r C) (r y), norm_sub_rev (r y) (r D)]
    · push Not at hyD
      let sD : ℝ := tD + ‖r y - r D‖
      refine ⟨(sD : ℂ), (sD : ℂ), sD, by linarith [hOnD.1, norm_nonneg (r y - r D)], rfl, ?_, ?_, ?_, ?_⟩
      · have htri : ‖r y‖ ≤ ‖r D‖ + ‖r y - r D‖ := by
          have : r y = r D + (r y - r D) := by ring
          (conv_lhs => rw [this]); exact norm_add_le _ _
        have hD0 : ‖r D‖ = tD := by rw [hrD_eq, Complex.norm_of_nonneg hOnD.1]
        have hs0 : ‖(sD : ℂ)‖ = sD := Complex.norm_of_nonneg (by dsimp [sD]; linarith [hOnD.1, norm_nonneg (r y - r D)])
        dsimp [sD] at hs0 ⊢; linarith
      · simp
      · unfold cross; rw [dir_re, dir_im, Real.sin_pi_div_six]
        simp only [ofReal_im, mul_zero, ofReal_re]
        dsimp [sD]; linarith [hOnD.1, norm_nonneg (r y - r D)]
      · dsimp [rightLen]; rw [if_neg (not_le.mpr hyD), sub_self, norm_zero, add_zero]
        have htri : ‖r C - (sD : ℂ)‖ ≤ ‖r C - r D‖ + ‖r D - (sD : ℂ)‖ := by
          have : r C - (sD : ℂ) = (r C - r D) + (r D - (sD : ℂ)) := by ring
          rw [this]; exact norm_add_le _ _
        have hsD_dist : ‖r D - (sD : ℂ)‖ = ‖r y - r D‖ := by
          rw [show r D - (sD : ℂ) = -((‖r y - r D‖ : ℝ) : ℂ) by dsimp [sD]; rw [hrD_eq]; push_cast; ring,
            norm_neg, Complex.norm_of_nonneg (norm_nonneg _)]
        rw [norm_sub_rev (r D) (r C)]; linarith
  obtain ⟨A_use, X_use, sA, hsA_le, hA_eq, hX_far, hX_im, hX_top, hleft_len⟩ := hleft
  obtain ⟨Y_use, D_use, sD, hsD0, hD_eq, hY_far, hY_im, hY_top, hright_len⟩ := hright
  let V' : ℂ := W.L • dir (Real.pi / 3)
  let A' : ℂ := reflectLine 0 (Real.pi / 6) A_use
  let X' : ℂ := reflectLine 0 (Real.pi / 6) X_use
  let Y' : ℂ := reflectLine (W.L : ℂ) (-(Real.pi / 6)) Y_use
  let D' : ℂ := reflectLine (W.L : ℂ) (-(Real.pi / 6)) D_use
  have hB_fix : reflectLine 0 (Real.pi / 6) (r B) = r B := by
    have h1 : r B = 0 + tB • dir (Real.pi / 6) := by rw [zero_add, hOnB.2, hu0, sub_zero]
    (conv_lhs => rw [h1]); rw [reflectLine_fix_ray]; exact h1.symm
  have hC_fix : reflectLine (W.L : ℂ) (-(Real.pi / 6)) (r C) = r C := by
    have h1 : r C = (W.L : ℂ) + (-tC) • dir (-(Real.pi / 6)) := by
      rw [hOnC.2, hv0, sub_zero, neg_smul]; ring
    (conv_lhs => rw [h1]); rw [reflectLine_fix_ray]; exact h1.symm
  have hchain_le1 : ‖A' - X'‖ + ‖X' - Y'‖ + ‖Y' - D'‖ ≤ 1 := by
    have hAX : ‖A' - X'‖ = ‖A_use - X_use‖ := reflectLine_dist 0 (Real.pi / 6) A_use X_use
    have hXB : ‖X' - r B‖ = ‖X_use - r B‖ := by (conv_lhs => rw [← hB_fix]); exact reflectLine_dist 0 (Real.pi / 6) X_use (r B)
    have hCY : ‖r C - Y'‖ = ‖r C - Y_use‖ := by (conv_lhs => rw [← hC_fix]); exact reflectLine_dist (W.L : ℂ) (-(Real.pi / 6)) (r C) Y_use
    have hYD : ‖Y' - D'‖ = ‖Y_use - D_use‖ := reflectLine_dist (W.L : ℂ) (-(Real.pi / 6)) Y_use D_use
    have htri : ‖X' - Y'‖ ≤ ‖X' - r B‖ + ‖r B - r C‖ + ‖r C - Y'‖ := by
      have : X' - Y' = (X' - r B) + (r B - r C) + (r C - Y') := by ring
      rw [this]
      have h1 := norm_add_le ((X' - r B) + (r B - r C)) (r C - Y')
      have h2 := norm_add_le (X' - r B) (r B - r C)
      linarith
    rw [norm_sub_rev (r B) (r C)] at htri
    linarith
  have hV'_L : reflectLine 0 (Real.pi / 6) (W.L : ℂ) = V' := by
    unfold reflectLine V'
    rw [sub_zero, zero_add, Complex.conj_ofReal, show 2 * (Real.pi / 6) = Real.pi / 3 by ring, Complex.real_smul]
  have hV'_0 : reflectLine (W.L : ℂ) (-(Real.pi / 6)) 0 = V' := by
    unfold reflectLine V'
    rw [zero_sub, map_neg, Complex.conj_ofReal, show 2 * -(Real.pi / 6) = -(Real.pi / 3) by ring,
      Complex.real_smul]
    apply Complex.ext
    · simp [dir_re, dir_im, Real.cos_pi_div_three]; ring
    · simp [dir_re, dir_im, Real.sin_pi_div_three]
  let af : ℂ := starRingEnd ℂ (A' - V')
  let xf : ℂ := starRingEnd ℂ (X' - V')
  let yf : ℂ := starRingEnd ℂ (Y' - V')
  let df : ℂ := starRingEnd ℂ (D' - V')
  have hxf_eq : xf = (X_use - (W.L : ℂ)) * dir (-(Real.pi / 3)) := by
    dsimp [xf, X']; rw [← hV'_L]; unfold reflectLine
    simp only [zero_add, sub_zero, map_sub, map_mul, Complex.conj_conj, ← dir_neg]
    rw [show -(2 * (Real.pi / 6)) = -(Real.pi / 3) by ring]; ring
  have hyf_eq : yf = Y_use * dir (Real.pi / 3) := by
    dsimp [yf, Y']; rw [← hV'_0]; unfold reflectLine
    have h1 : ((W.L : ℂ) + starRingEnd ℂ (Y_use - (W.L : ℂ)) * dir (2 * -(Real.pi / 6))) -
        ((W.L : ℂ) + starRingEnd ℂ (0 - (W.L : ℂ)) * dir (2 * -(Real.pi / 6))) =
        starRingEnd ℂ Y_use * dir (-(Real.pi / 3)) := by
      simp only [map_sub, zero_sub, map_neg, show 2 * -(Real.pi / 6) = -(Real.pi / 3) by ring]; ring
    rw [h1, map_mul, Complex.conj_conj, ← dir_neg, neg_neg]
  have haf_eq : af = ((sA - W.L : ℝ) : ℂ) * dir (-(Real.pi / 3)) := by
    dsimp [af, A']; rw [← hV'_L, hA_eq]; unfold reflectLine
    simp only [zero_add, sub_zero, map_sub, map_mul, Complex.conj_conj, ← dir_neg, Complex.conj_ofReal]
    rw [show -(2 * (Real.pi / 6)) = -(Real.pi / 3) by ring]; push_cast; ring
  have hdf_eq : df = (sD : ℂ) * dir (Real.pi / 3) := by
    dsimp [df, D']; rw [← hV'_0, hD_eq]; unfold reflectLine
    have h1 : ((W.L : ℂ) + starRingEnd ℂ ((sD : ℂ) - (W.L : ℂ)) * dir (2 * -(Real.pi / 6))) -
        ((W.L : ℂ) + starRingEnd ℂ (0 - (W.L : ℂ)) * dir (2 * -(Real.pi / 6))) =
        (sD : ℂ) * dir (-(Real.pi / 3)) := by
      simp only [map_sub, zero_sub, map_neg, Complex.conj_ofReal,
        show 2 * -(Real.pi / 6) = -(Real.pi / 3) by ring]; ring
    rw [h1, map_mul, Complex.conj_ofReal, ← dir_neg, neg_neg]
  have haf_le : Real.sqrt 3 * af.re + af.im ≤ 0 := by
    rw [haf_eq]; simp [dir_re, dir_im, Real.cos_pi_div_three, Real.sin_pi_div_three]; ring_nf; exact le_rfl
  have hdf_le : -Real.sqrt 3 * df.re + df.im ≤ 0 := by
    rw [hdf_eq]; simp [dir_re, dir_im, Real.cos_pi_div_three, Real.sin_pi_div_three]; ring_nf; exact le_rfl
  have hxf_re : xf.re ≤ 0 := by
    rw [hxf_eq]; simp only [mul_re, dir_re, dir_im, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    unfold cross at hX_top; rw [dir_re, dir_im, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_six, Real.sin_pi_div_six] at hX_top
    linarith
  have hxf_im : 0 ≤ xf.im := by
    rw [hxf_eq]; simp only [mul_im, dir_re, dir_im, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    unfold cross at hX_top; rw [dir_re, dir_im, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_six, Real.sin_pi_div_six] at hX_top
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hsq3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith
  have hyf_re : 0 ≤ yf.re := by
    rw [hyf_eq]; simp only [mul_re, dir_re, dir_im, Real.cos_pi_div_three, Real.sin_pi_div_three]
    unfold cross at hY_top; rw [dir_re, dir_im, Real.cos_pi_div_six, Real.sin_pi_div_six] at hY_top
    linarith
  have hyf_im : 0 ≤ yf.im := by
    rw [hyf_eq]; simp only [mul_im, dir_re, dir_im, Real.cos_pi_div_three, Real.sin_pi_div_three]
    unfold cross at hY_top; rw [dir_re, dir_im, Real.cos_pi_div_six, Real.sin_pi_div_six] at hY_top
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hsq3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith
  have hxf_gt : 1 < ‖xf‖ := by rw [hxf_eq, norm_mul, dir_norm, mul_one]; exact hX_far
  have hyf_gt : 1 < ‖yf‖ := by rw [hyf_eq, norm_mul, dir_norm, mul_one]; exact hY_far
  have hgt := sector60_chain_gt_one haf_le hdf_le hxf_re hxf_im hyf_re hyf_im hxf_gt hyf_gt
  have h1 : ‖af - xf‖ = ‖A' - X'‖ := by
    rw [show af - xf = starRingEnd ℂ (A' - X') by dsimp [af, xf]; rw [← map_sub]; congr 1; ring, Complex.norm_conj]
  have h2 : ‖xf - yf‖ = ‖X' - Y'‖ := by
    rw [show xf - yf = starRingEnd ℂ (X' - Y') by dsimp [xf, yf]; rw [← map_sub]; congr 1; ring, Complex.norm_conj]
  have h3 : ‖yf - df‖ = ‖Y' - D'‖ := by
    rw [show yf - df = starRingEnd ℂ (Y' - D') by dsimp [yf, df]; rw [← map_sub]; congr 1; ring, Complex.norm_conj]
  linarith

set_option maxHeartbeats 800000 in
lemma case3_contradiction {N : ℕ} {r : Fin (N + 1) → ℂ}
    (hgp : GenPos r) (hsimp : IsSimplePoly r) (hlen : polyLen r ≤ 1) (huncov : ¬ CoveredUnit r)
    (W : TwoWedgeBase r) (hcase : IsCase3 W) : False := by
  rcases hcase with ⟨A, B, C, D, E, F, tA, tB, tC, tD, tE, tF,
    hAB, hBC, hCD, hDE, hEF, htAC, htFD, hOnA, hOnB, hOnC, hOnD, hOnE, hOnF⟩
  obtain ⟨x, hxB, hx_far⟩ := exists_far_before_B hgp hsimp huncov W hAB hBC htAC hOnA hOnB hOnC
  obtain ⟨y, hEy, hy_far⟩ := exists_far_after_Vtop hgp hsimp huncov W hDE hEF htFD hOnD hOnE hOnF
  let leftLen : ℝ := if A ≤ x then ‖r x - r A‖ + ‖r B - r x‖ else ‖r A - r x‖ + ‖r B - r A‖
  let rightLen : ℝ := if y ≤ F then ‖r y - r E‖ + ‖r F - r y‖ else ‖r F - r E‖ + ‖r y - r F‖
  have htot_le : leftLen + ‖r C - r B‖ + ‖r D - r C‖ + ‖r E - r D‖ + rightLen ≤ 1 := by
    refine le_trans ?_ hlen
    dsimp [leftLen, rightLen]
    by_cases hAx : A ≤ x <;> by_cases hyF : y ≤ F
    · rw [if_pos hAx, if_pos hyF]
      linarith [chain8_le_polyLen r hAx hxB hBC.le hCD hDE.le hEy hyF]
    · push Not at hyF; rw [if_pos hAx, if_neg (not_le.mpr hyF)]
      linarith [chain8_le_polyLen r hAx hxB hBC.le hCD hDE.le hEF.le hyF.le]
    · push Not at hAx; rw [if_neg (not_le.mpr hAx), if_pos hyF]
      linarith [chain8_le_polyLen r hAx.le hAB.le hBC.le hCD hDE.le hEy hyF]
    · push Not at hAx hyF; rw [if_neg (not_le.mpr hAx), if_neg (not_le.mpr hyF)]
      linarith [chain8_le_polyLen r hAx.le hAB.le hBC.le hCD hDE.le hEF.le hyF.le]
  let P3 : ℂ := W.L • dir (-(Real.pi / 3))
  let B' : ℂ := reflectLine 0 (-W.u_lo) (r B)
  let E' : ℂ := reflectLine (W.L : ℂ) W.v_lo (r E)
  have hrotL_eq : ∀ z : ℂ, rotC (-(Real.pi / 3)) z =
      reflectLine 0 (-W.u_lo - Real.pi / 6) (reflectLine 0 (-W.u_lo) z) := fun z => by
    rw [reflectLine_comp, sub_zero, zero_add, show 2 * (-W.u_lo - Real.pi / 6 - -W.u_lo) = -(Real.pi / 3) by ring]
    simp [rotC_apply, dir, mul_comm]
  have hB'_fix : reflectLine 0 (-W.u_lo - Real.pi / 6) B' = B' := by
    have h1 : B' = 0 + tB • dir (-W.u_lo - Real.pi / 6) := by
      dsimp [B']; rw [zero_add, hOnB.2, show tB • dir (Real.pi / 6 - W.u_lo) = 0 + tB • dir (Real.pi / 6 - W.u_lo) by ring,
        reflectLine_dir, zero_add]
      congr 2; ring
    conv_lhs => rw [h1]; rw [reflectLine_fix_ray]; exact h1.symm
  have hrotL_dist_B : ∀ z : ℂ, ‖rotC (-(Real.pi / 3)) z - B'‖ = ‖z - r B‖ := fun z => by
    rw [hrotL_eq, ← hB'_fix, reflectLine_dist, reflectLine_dist]
  have hrotR_eq : ∀ z : ℂ, (W.L : ℂ) + rotC (Real.pi / 3) (z - (W.L : ℂ)) =
      reflectLine (W.L : ℂ) (W.v_lo + Real.pi / 6) (reflectLine (W.L : ℂ) W.v_lo z) := fun z => by
    rw [reflectLine_comp, show 2 * (W.v_lo + Real.pi / 6 - W.v_lo) = Real.pi / 3 by ring]
    simp [rotC_apply, dir, mul_comm]
  have hE'_fix : reflectLine (W.L : ℂ) (W.v_lo + Real.pi / 6) E' = E' := by
    have h1 : E' = (W.L : ℂ) + (-tE) • dir (W.v_lo + Real.pi / 6) := by
      dsimp [E']; rw [hOnE.2, show (W.L : ℂ) - tE • dir (-(Real.pi / 6 - W.v_lo)) =
        (W.L : ℂ) + (-tE) • dir (-(Real.pi / 6 - W.v_lo)) by rw [neg_smul]; ring, reflectLine_dir]
      congr 3; ring
    conv_lhs => rw [h1]; rw [reflectLine_fix_ray]; exact h1.symm
  have hrotR_dist_E : ∀ z : ℂ, ‖E' - ((W.L : ℂ) + rotC (Real.pi / 3) (z - (W.L : ℂ)))‖ = ‖r E - z‖ := fun z => by
    rw [hrotR_eq, ← hE'_fix, reflectLine_dist, reflectLine_dist]
  have hBC_eq : ‖B' - r C‖ = ‖r B - r C‖ := by
    have hC_fix : reflectLine 0 (-W.u_lo) (r C) = r C := by
      have h1 : r C = 0 + tC • dir (-W.u_lo) := by rw [zero_add, hOnC.2]
      (conv_lhs => rw [h1]); rw [reflectLine_fix_ray]; exact h1.symm
    dsimp [B']; (conv_lhs => rw [← hC_fix]); exact reflectLine_dist 0 (-W.u_lo) (r B) (r C)
  have hDE_eq : ‖r D - E'‖ = ‖r D - r E‖ := by
    have hD_fix : reflectLine (W.L : ℂ) W.v_lo (r D) = r D := by
      have h1 : r D = (W.L : ℂ) + (-tD) • dir W.v_lo := by rw [hOnD.2, neg_smul]; ring
      (conv_lhs => rw [h1]); rw [reflectLine_fix_ray]; exact h1.symm
    dsimp [E']; (conv_lhs => rw [← hD_fix]); exact reflectLine_dist (W.L : ℂ) W.v_lo (r D) (r E)
  have hleft : ∃ (A_use X_use : ℂ), A_use.im ≤ 0 ∧ 1 < ‖X_use - (W.L : ℂ)‖ ∧
      cross (dir (-(Real.pi / 6 - W.v_lo))) (X_use - (W.L : ℂ)) ≤ 0 ∧
      0 ≤ cross (dir W.v_lo) (X_use - (W.L : ℂ)) ∧
      ‖rotC (-(Real.pi / 3)) A_use - rotC (-(Real.pi / 3)) X_use‖ +
        ‖rotC (-(Real.pi / 3)) X_use - B'‖ ≤ leftLen := by
    have htA_le : tA ≤ W.L * Real.cos W.u_lo :=
      onUbot_le_L_cos W hOnA.1 (hOnA.2 ▸ ⟨W.hU_bot A, W.hU_top A, W.hV_top A, W.hV_bot A⟩)
    by_cases hAx : A ≤ x
    · refine ⟨r A, r x, ?_, hx_far, W.hV_top x, W.hV_bot x, ?_⟩
      · rw [hOnA.2]; simp only [smul_im, smul_eq_mul, dir_im, Real.sin_neg]
        have := Real.sin_nonneg_of_nonneg_of_le_pi W.hu_lo0 (by linarith [W.hu_lo_le, Real.pi_pos])
        nlinarith [hOnA.1]
      · rw [← map_sub, (rotC _).norm_map, hrotL_dist_B]
        dsimp [leftLen]; rw [if_pos hAx, norm_sub_rev (r A) (r x), norm_sub_rev (r x) (r B)]
    · push Not at hAx
      have hfig7 := fig7_obtuse_dist W.hL.le W.hu_lo0 W.hu_lo_le htA_le (W.hU_bot x)
      rw [← hOnA.2] at hfig7
      by_cases hclamp : ‖r x - r A‖ ≤ tA
      · let s : ℝ := tA - ‖r x - r A‖
        let Z : ℂ := s • dir (-W.u_lo)
        have hZ_eq : Z = r A - ‖r x - r A‖ • dir (-W.u_lo) := by
          rw [show Z = s • dir (-W.u_lo) from rfl, show s = tA - ‖r x - r A‖ from rfl, hOnA.2, sub_smul]
        have hZ_mem : Z ∈ wedgeSet W := by
          have h0_mem : (0 : ℂ) ∈ wedgeSet W := by
            refine ⟨by simp [cross], by simp [cross], ?_, ?_⟩
            · rw [zero_sub, cross_neg_right]; unfold cross; rw [dir_re, dir_im, Real.sin_neg]; simp
              have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ Real.pi / 6 - W.v_lo by linarith [W.hv_lo_le])
                (by linarith [W.hv_lo0, Real.pi_pos])
              nlinarith [W.hL]
            · rw [zero_sub, cross_neg_right]; unfold cross; rw [dir_re, dir_im]; simp
              have := Real.sin_nonneg_of_nonneg_of_le_pi W.hv_lo0 (by linarith [W.hv_lo_le, Real.pi_pos])
              nlinarith [W.hL]
          have hA_mem : r A ∈ wedgeSet W := ⟨W.hU_bot A, W.hU_top A, W.hV_top A, W.hV_bot A⟩
          by_cases htA0 : tA = 0
          · have hs0 : s = 0 := by dsimp [s]; linarith [norm_nonneg (r x - r A)]
            simpa [Z, hs0] using h0_mem
          · have htA_pos : 0 < tA := lt_of_le_of_ne hOnA.1 (Ne.symm htA0)
            have hconv : Z = (1 - s / tA) • (0 : ℂ) + (s / tA) • r A := by
              rw [smul_zero, zero_add, hOnA.2, smul_smul, div_mul_cancel₀ _ htA_pos.ne']
            rw [hconv]
            exact wedgeSet_convex W h0_mem hA_mem
              (by rw [sub_nonneg, div_le_one htA_pos]; dsimp [s]; linarith [norm_nonneg (r x - r A)])
              (div_nonneg (by dsimp [s]; linarith) htA_pos.le) (by ring)
        refine ⟨Z, Z, ?_, by rw [hZ_eq]; linarith, hZ_mem.2.2.1, hZ_mem.2.2.2, ?_⟩
        · change (s • dir (-W.u_lo)).im ≤ 0
          simp only [smul_im, smul_eq_mul, dir_im, Real.sin_neg]
          have := Real.sin_nonneg_of_nonneg_of_le_pi W.hu_lo0 (by linarith [W.hu_lo_le, Real.pi_pos])
          dsimp [s]; nlinarith
        · rw [sub_self, norm_zero, zero_add, hrotL_dist_B]
          dsimp [leftLen]; rw [if_neg (not_le.mpr hAx)]
          have htri : ‖Z - r B‖ ≤ ‖Z - r A‖ + ‖r A - r B‖ := by
            have : Z - r B = (Z - r A) + (r A - r B) := by ring
            rw [this]; exact norm_add_le _ _
          have hZA : ‖Z - r A‖ = ‖r x - r A‖ := by
            rw [hZ_eq, show r A - ‖r x - r A‖ • dir (-W.u_lo) - r A = -(‖r x - r A‖ • dir (-W.u_lo)) by ring,
              norm_neg, norm_smul, Real.norm_of_nonneg (norm_nonneg _), dir_norm, mul_one]
          rw [norm_sub_rev (r A) (r x), norm_sub_rev (r B) (r A)]; linarith
      · push Not at hclamp
        let r_rem : ℝ := ‖r x - r A‖ - tA
        have hr_pos : 0 < r_rem := by dsimp [r_rem]; linarith
        let Z : ℂ := -(r_rem : ℂ)
        refine ⟨Z, Z, by simp [Z], ?_, ?_, ?_, ?_⟩
        · have hbar_le : ‖(r A - ‖r x - r A‖ • dir (-W.u_lo)) - (W.L : ℂ)‖ ≤ r_rem + W.L := by
            have h1 : (r A - ‖r x - r A‖ • dir (-W.u_lo)) - (W.L : ℂ) =
                (-r_rem) • dir (-W.u_lo) + (-(W.L : ℂ)) := by
              rw [show r_rem = ‖r x - r A‖ - tA from rfl, hOnA.2, Complex.real_smul, Complex.real_smul, Complex.real_smul]
              push_cast; ring
            rw [h1]
            calc ‖(-r_rem) • dir (-W.u_lo) + (-(W.L : ℂ))‖
                ≤ ‖(-r_rem) • dir (-W.u_lo)‖ + ‖-(W.L : ℂ)‖ := norm_add_le _ _
              _ = r_rem + W.L := by
                  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hr_pos, dir_norm, mul_one,
                    norm_neg, Complex.norm_of_nonneg W.hL.le]
          have hZL : ‖Z - (W.L : ℂ)‖ = r_rem + W.L := by
            dsimp [Z]; rw [show -(r_rem : ℂ) - (W.L : ℂ) = -((r_rem + W.L : ℝ) : ℂ) by push_cast; ring,
              norm_neg, Complex.norm_of_nonneg (by linarith [W.hL])]
          linarith
        · dsimp [Z]; unfold cross; rw [dir_re, dir_im, Real.sin_neg]
          simp only [sub_im, neg_im, ofReal_im, neg_zero, sub_self, mul_zero, sub_re, neg_re, ofReal_re]
          have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ Real.pi / 6 - W.v_lo by linarith [W.hv_lo_le])
            (by linarith [W.hv_lo0, Real.pi_pos])
          nlinarith [W.hL]
        · dsimp [Z]; unfold cross; rw [dir_re, dir_im]
          simp only [sub_im, neg_im, ofReal_im, neg_zero, sub_self, mul_zero, sub_re, neg_re, ofReal_re]
          have := Real.sin_nonneg_of_nonneg_of_le_pi W.hv_lo0 (by linarith [W.hv_lo_le, Real.pi_pos])
          nlinarith [W.hL]
        · rw [sub_self, norm_zero, zero_add]
          dsimp [leftLen]; rw [if_neg (not_le.mpr hAx)]
          have htri1 : ‖rotC (-(Real.pi / 3)) Z - B'‖ ≤ ‖rotC (-(Real.pi / 3)) Z‖ + ‖B'‖ := by
            have : rotC (-(Real.pi / 3)) Z - B' = rotC (-(Real.pi / 3)) Z + (-B') := by ring
            rw [this]; exact (norm_add_le _ _).trans (by rw [norm_neg])
          have hZnorm : ‖rotC (-(Real.pi / 3)) Z‖ = r_rem := by
            rw [(rotC _).norm_map]; dsimp [Z]; rw [norm_neg, Complex.norm_of_nonneg hr_pos.le]
          have hB'norm : ‖B'‖ = ‖r B‖ := by
            have h0 : reflectLine 0 (-W.u_lo) 0 = 0 := by unfold reflectLine; simp
            simpa [h0] using reflectLine_dist 0 (-W.u_lo) (r B) 0
          have hBtri : ‖r B‖ ≤ ‖r A‖ + ‖r B - r A‖ := by
            have : r B = r A + (r B - r A) := by ring
            (conv_lhs => rw [this]); exact norm_add_le _ _
          have hAnorm : ‖r A‖ = tA := by
            rw [hOnA.2, norm_smul, Real.norm_of_nonneg hOnA.1, dir_norm, mul_one]
          rw [norm_sub_rev (r A) (r x)]; dsimp [r_rem] at hZnorm; linarith
  have hright : ∃ (Y_use F_use : ℂ), F_use.im ≤ 0 ∧ 1 < ‖Y_use‖ ∧
      0 ≤ cross (dir (-W.u_lo)) Y_use ∧ cross (dir (Real.pi / 6 - W.u_lo)) Y_use ≤ 0 ∧
      ‖E' - ((W.L : ℂ) + rotC (Real.pi / 3) (Y_use - (W.L : ℂ)))‖ +
        ‖((W.L : ℂ) + rotC (Real.pi / 3) (Y_use - (W.L : ℂ))) -
          ((W.L : ℂ) + rotC (Real.pi / 3) (F_use - (W.L : ℂ)))‖ ≤ rightLen := by
    have htF_le : tF ≤ W.L * Real.cos W.v_lo := by
      let Wf := twoWedgeBase_flipX W
      have hF_mem : tF • dir (-Wf.u_lo) ∈ wedgeSet Wf := by
        have h1 : tF • dir (-Wf.u_lo) = (fun k => (W.L : ℂ) - starRingEnd ℂ (r k.rev)) F.rev := by
          dsimp [Wf, twoWedgeBase_flipX]; rw [Fin.rev_rev, hOnF.2, dir_neg]; simp [Complex.real_smul]
        rw [h1]
        exact ⟨Wf.hU_bot F.rev, Wf.hU_top F.rev, Wf.hV_top F.rev, Wf.hV_bot F.rev⟩
      exact onUbot_le_L_cos Wf hOnF.1 hF_mem
    by_cases hyF : y ≤ F
    · refine ⟨r y, r F, ?_, hy_far, W.hU_bot y, W.hU_top y, ?_⟩
      · rw [hOnF.2]; simp only [sub_im, ofReal_im, smul_im, smul_eq_mul, dir_im]
        have := Real.sin_nonneg_of_nonneg_of_le_pi W.hv_lo0 (by linarith [W.hv_lo_le, Real.pi_pos])
        nlinarith [hOnF.1]
      · rw [hrotR_dist_E, show ((W.L : ℂ) + rotC (Real.pi / 3) (r y - (W.L : ℂ))) -
            ((W.L : ℂ) + rotC (Real.pi / 3) (r F - (W.L : ℂ))) = rotC (Real.pi / 3) (r y - r F) by
          simp only [map_sub]; ring, (rotC _).norm_map]
        dsimp [rightLen]; rw [if_pos hyF, norm_sub_rev (r E) (r y), norm_sub_rev (r y) (r F)]
    · push Not at hyF
      let Xf : ℂ := (W.L : ℂ) - starRingEnd ℂ (r y)
      have hXf_bot : 0 ≤ cross (dir (-W.v_lo)) Xf := by
        dsimp [Xf]; rw [dir_neg, show (W.L : ℂ) - starRingEnd ℂ (r y) = -(starRingEnd ℂ (r y - (W.L : ℂ))) by simp,
          cross_neg_right, cross_conj, neg_neg]; exact W.hV_bot y
      have hfig7 := fig7_obtuse_dist W.hL.le W.hv_lo0 W.hv_lo_le htF_le hXf_bot
      have hXf_L : ‖Xf - (W.L : ℂ)‖ = ‖r y‖ := by
        dsimp [Xf]; rw [show (W.L : ℂ) - starRingEnd ℂ (r y) - (W.L : ℂ) = -(starRingEnd ℂ (r y)) by ring,
          norm_neg, Complex.norm_conj]
      have hXf_dist : ‖Xf - tF • dir (-W.v_lo)‖ = ‖r y - r F‖ := by
        have h1 : Xf - tF • dir (-W.v_lo) = -starRingEnd ℂ (r y - r F) := by
          dsimp [Xf]; rw [hOnF.2, dir_neg]; simp [Complex.real_smul]; ring
        rw [h1, norm_neg, Complex.norm_conj]
      rw [hXf_L, hXf_dist] at hfig7
      by_cases hclamp : ‖r y - r F‖ ≤ tF
      · let s : ℝ := tF - ‖r y - r F‖
        let Z : ℂ := (W.L : ℂ) - s • dir W.v_lo
        have hZ_norm : ‖Z‖ = ‖(tF • dir (-W.v_lo) - ‖r y - r F‖ • dir (-W.v_lo)) - (W.L : ℂ)‖ := by
          have h1 : (tF • dir (-W.v_lo) - ‖r y - r F‖ • dir (-W.v_lo)) - (W.L : ℂ) = -starRingEnd ℂ Z := by
            dsimp [Z, s]; rw [dir_neg]; simp [Complex.real_smul]; push_cast; ring
          rw [h1, norm_neg, Complex.norm_conj]
        have hZ_mem : Z ∈ wedgeSet W := by
          have hL_mem : (W.L : ℂ) ∈ wedgeSet W := by
            refine ⟨?_, ?_, by simp [cross], by simp [cross]⟩
            · unfold cross; rw [dir_re, dir_im, Real.sin_neg]; simp
              have := Real.sin_nonneg_of_nonneg_of_le_pi W.hu_lo0 (by linarith [W.hu_lo_le, Real.pi_pos])
              nlinarith [W.hL]
            · unfold cross; rw [dir_re, dir_im]; simp
              have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ Real.pi / 6 - W.u_lo by linarith [W.hu_lo_le])
                (by linarith [W.hu_lo0, Real.pi_pos])
              nlinarith [W.hL]
          have hF_mem : r F ∈ wedgeSet W := ⟨W.hU_bot F, W.hU_top F, W.hV_top F, W.hV_bot F⟩
          by_cases htF0 : tF = 0
          · have hs0 : s = 0 := by dsimp [s]; linarith [norm_nonneg (r y - r F)]
            simpa [Z, hs0] using hL_mem
          · have htF_pos : 0 < tF := lt_of_le_of_ne hOnF.1 (Ne.symm htF0)
            have hconv : Z = (1 - s / tF) • (W.L : ℂ) + (s / tF) • r F := by
              rw [show Z = (W.L : ℂ) - s • dir W.v_lo from rfl, hOnF.2]
              simp only [Complex.real_smul]; push_cast
              have hdiv : (s : ℂ) / (tF : ℂ) * (tF : ℂ) = (s : ℂ) := div_mul_cancel₀ _ (by exact_mod_cast htF_pos.ne')
              linear_combination dir W.v_lo * hdiv
            rw [hconv]
            exact wedgeSet_convex W hL_mem hF_mem
              (by rw [sub_nonneg, div_le_one htF_pos]; dsimp [s]; linarith [norm_nonneg (r y - r F)])
              (div_nonneg (by dsimp [s]; linarith) htF_pos.le) (by ring)
        refine ⟨Z, Z, ?_, by rw [hZ_norm]; linarith, hZ_mem.1, hZ_mem.2.1, ?_⟩
        · change ((W.L : ℂ) - s • dir W.v_lo).im ≤ 0
          simp only [sub_im, ofReal_im, smul_im, smul_eq_mul, dir_im]
          have := Real.sin_nonneg_of_nonneg_of_le_pi W.hv_lo0 (by linarith [W.hv_lo_le, Real.pi_pos])
          dsimp [s]; nlinarith
        · rw [sub_self, norm_zero, add_zero, hrotR_dist_E]
          dsimp [rightLen]; rw [if_neg (not_le.mpr hyF)]
          have htri : ‖r E - Z‖ ≤ ‖r E - r F‖ + ‖r F - Z‖ := by
            have : r E - Z = (r E - r F) + (r F - Z) := by ring
            rw [this]; exact norm_add_le _ _
          have hFZ : ‖r F - Z‖ = ‖r y - r F‖ := by
            have : r F - Z = -(‖r y - r F‖ • dir W.v_lo) := by
              rw [show Z = (W.L : ℂ) - s • dir W.v_lo from rfl, show s = tF - ‖r y - r F‖ from rfl, hOnF.2,
                Complex.real_smul, Complex.real_smul, Complex.real_smul]
              push_cast; ring
            rw [this, norm_neg, norm_smul, Real.norm_of_nonneg (norm_nonneg _), dir_norm, mul_one]
          rw [norm_sub_rev (r F) (r E)]; linarith
      · push Not at hclamp
        let s_rem : ℝ := ‖r y - r F‖ - tF
        have hs_pos : 0 < s_rem := by dsimp [s_rem]; linarith
        let Z : ℂ := ((W.L + s_rem : ℝ) : ℂ)
        refine ⟨Z, Z, by simp [Z], ?_, ?_, ?_, ?_⟩
        · have hbar_le : ‖(tF • dir (-W.v_lo) - ‖r y - r F‖ • dir (-W.v_lo)) - (W.L : ℂ)‖ ≤ s_rem + W.L := by
            have h1 : (tF • dir (-W.v_lo) - ‖r y - r F‖ • dir (-W.v_lo)) - (W.L : ℂ) =
                (-s_rem) • dir (-W.v_lo) + (-(W.L : ℂ)) := by
              rw [show s_rem = ‖r y - r F‖ - tF from rfl, Complex.real_smul, Complex.real_smul, Complex.real_smul]
              push_cast; ring
            rw [h1]
            calc ‖(-s_rem) • dir (-W.v_lo) + (-(W.L : ℂ))‖
                ≤ ‖(-s_rem) • dir (-W.v_lo)‖ + ‖-(W.L : ℂ)‖ := norm_add_le _ _
              _ = s_rem + W.L := by
                  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hs_pos, dir_norm, mul_one,
                    norm_neg, Complex.norm_of_nonneg W.hL.le]
          have hZn : ‖Z‖ = W.L + s_rem := Complex.norm_of_nonneg (by linarith [W.hL])
          linarith
        · dsimp [Z]; unfold cross; rw [dir_re, dir_im, Real.sin_neg]; simp
          have := Real.sin_nonneg_of_nonneg_of_le_pi W.hu_lo0 (by linarith [W.hu_lo_le, Real.pi_pos])
          nlinarith [W.hL]
        · dsimp [Z]; unfold cross; rw [dir_re, dir_im]; simp
          have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ Real.pi / 6 - W.u_lo by linarith [W.hu_lo_le])
            (by linarith [W.hu_lo0, Real.pi_pos])
          nlinarith [W.hL]
        · rw [sub_self, norm_zero, add_zero]
          dsimp [rightLen]; rw [if_neg (not_le.mpr hyF)]
          let Y'' := (W.L : ℂ) + rotC (Real.pi / 3) (Z - (W.L : ℂ))
          have htri1 : ‖E' - Y''‖ ≤ ‖E' - (W.L : ℂ)‖ + ‖(W.L : ℂ) - Y''‖ := by
            have : E' - Y'' = (E' - (W.L : ℂ)) + ((W.L : ℂ) - Y'') := by ring
            rw [this]; exact norm_add_le _ _
          have hEL : ‖E' - (W.L : ℂ)‖ = ‖r E - (W.L : ℂ)‖ := by
            have hL_fix : reflectLine (W.L : ℂ) W.v_lo (W.L : ℂ) = (W.L : ℂ) := by unfold reflectLine; simp
            simpa [hL_fix] using reflectLine_dist (W.L : ℂ) W.v_lo (r E) (W.L : ℂ)
          have hYL : ‖(W.L : ℂ) - Y''‖ = s_rem := by
            dsimp [Y'', Z]
            rw [show (W.L : ℂ) - ((W.L : ℂ) + rotC (Real.pi / 3) (((W.L + s_rem : ℝ) : ℂ) - (W.L : ℂ))) =
              -rotC (Real.pi / 3) (s_rem : ℂ) by push_cast; ring,
              norm_neg, (rotC _).norm_map, Complex.norm_of_nonneg hs_pos.le]
          have hEtri : ‖r E - (W.L : ℂ)‖ ≤ ‖r F - r E‖ + ‖r F - (W.L : ℂ)‖ := by
            have : r E - (W.L : ℂ) = (r E - r F) + (r F - (W.L : ℂ)) := by ring
            rw [this, norm_sub_rev (r F) (r E)]; exact norm_add_le _ _
          have hFL : ‖r F - (W.L : ℂ)‖ = tF := by
            rw [hOnF.2, show (W.L : ℂ) - tF • dir W.v_lo - (W.L : ℂ) = -(tF • dir W.v_lo) by ring,
              norm_neg, norm_smul, Real.norm_of_nonneg hOnF.1, dir_norm, mul_one]
          dsimp [s_rem] at hYL; linarith
  obtain ⟨A_use, X_use, hA_im, hX_far, hX_Vtop, hX_Vbot, hleft_len⟩ := hleft
  obtain ⟨Y_use, F_use, hF_im, hY_far, hY_Ubot, hY_Utop, hright_len⟩ := hright
  let A'' : ℂ := rotC (-(Real.pi / 3)) A_use
  let X'' : ℂ := rotC (-(Real.pi / 3)) X_use
  let Y'' : ℂ := (W.L : ℂ) + rotC (Real.pi / 3) (Y_use - (W.L : ℂ))
  let F'' : ℂ := (W.L : ℂ) + rotC (Real.pi / 3) (F_use - (W.L : ℂ))
  have hchain_le1 : ‖A'' - X''‖ + ‖X'' - Y''‖ + ‖Y'' - F''‖ ≤ 1 := by
    have htri : ‖X'' - Y''‖ ≤ ‖X'' - B'‖ + ‖B' - r C‖ + ‖r C - r D‖ + ‖r D - E'‖ + ‖E' - Y''‖ := by
      have : X'' - Y'' = (((X'' - B') + (B' - r C)) + (r C - r D)) + ((r D - E') + (E' - Y'')) := by ring
      rw [this]
      have h1 := norm_add_le (((X'' - B') + (B' - r C)) + (r C - r D)) ((r D - E') + (E' - Y''))
      have h2 := norm_add_le ((X'' - B') + (B' - r C)) (r C - r D)
      have h3 := norm_add_le (X'' - B') (B' - r C)
      have h4 := norm_add_le (r D - E') (E' - Y'')
      linarith
    rw [hBC_eq, hDE_eq, norm_sub_rev (r B) (r C), norm_sub_rev (r C) (r D), norm_sub_rev (r D) (r E)] at htri
    linarith
  have hP3_L : rotC (-(Real.pi / 3)) (W.L : ℂ) = P3 := by
    dsimp [P3]; simp [rotC_apply, dir, Complex.real_smul, mul_comm]
  have hP3_R : (W.L : ℂ) - rotC (Real.pi / 3) (W.L : ℂ) = P3 := by
    show (W.L : ℂ) - dir (Real.pi / 3) * (W.L : ℂ) = W.L • dir (-(Real.pi / 3))
    apply Complex.ext
    · simp [dir_re, dir_im, Real.cos_pi_div_three]; ring
    · simp [dir_re, dir_im, Real.sin_pi_div_three]; ring
  have hAf_eq : A'' - P3 = rotC (-(Real.pi / 3)) (A_use - (W.L : ℂ)) := by
    dsimp [A'']; rw [← hP3_L, map_sub]
  have hXf_eq : X'' - P3 = rotC (-(Real.pi / 3)) (X_use - (W.L : ℂ)) := by
    dsimp [X'']; rw [← hP3_L, map_sub]
  have hYf_eq : Y'' - P3 = rotC (Real.pi / 3) Y_use := by
    dsimp [Y'']; rw [← hP3_R, map_sub]; ring
  have hFf_eq : F'' - P3 = rotC (Real.pi / 3) F_use := by
    dsimp [F'']; rw [← hP3_R, map_sub]; ring
  have hAf_le : Real.sqrt 3 * (A'' - P3).re + (A'' - P3).im ≤ 0 := by
    rw [hAf_eq]; simp only [rotC_apply, mul_re, mul_im]
    have hre : (Complex.exp (((-(Real.pi / 3) : ℝ) : ℂ) * I)).re = 1 / 2 := by
      simpa [dir, Real.cos_neg, Real.cos_pi_div_three] using dir_re (-(Real.pi / 3))
    have him : (Complex.exp (((-(Real.pi / 3) : ℝ) : ℂ) * I)).im = -(Real.sqrt 3 / 2) := by
      simpa [dir, Real.sin_neg, Real.sin_pi_div_three] using dir_im (-(Real.pi / 3))
    rw [hre, him, sub_im, ofReal_im, sub_zero]
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hid : Real.sqrt 3 * (1 / 2 * (A_use - (W.L : ℂ)).re - -(Real.sqrt 3 / 2) * A_use.im) +
        (1 / 2 * A_use.im + -(Real.sqrt 3 / 2) * (A_use - (W.L : ℂ)).re) = 2 * A_use.im := by
      linear_combination (A_use.im / 2) * hsq3
    linarith
  have hFf_le : -Real.sqrt 3 * (F'' - P3).re + (F'' - P3).im ≤ 0 := by
    rw [hFf_eq]; simp only [rotC_apply, mul_re, mul_im]
    have hre : (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I)).re = 1 / 2 := by
      simpa [dir, Real.cos_pi_div_three] using dir_re (Real.pi / 3)
    have him : (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I)).im = Real.sqrt 3 / 2 := by
      simpa [dir, Real.sin_pi_div_three] using dir_im (Real.pi / 3)
    rw [hre, him]
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hid : -Real.sqrt 3 * (1 / 2 * F_use.re - Real.sqrt 3 / 2 * F_use.im) +
        (1 / 2 * F_use.im + Real.sqrt 3 / 2 * F_use.re) = 2 * F_use.im := by
      linear_combination (F_use.im / 2) * hsq3
    linarith
  have hrot_dir : ∀ θ φ, rotC θ (dir φ) = dir (φ + θ) := fun θ φ => by
    simp only [rotC_apply, dir, ← Complex.exp_add]; congr 1; push_cast; ring
  have hXf_Q2 : (X'' - P3).re ≤ 0 ∧ 0 ≤ (X'' - P3).im := by
    rw [hXf_eq]
    have hdec := wedge_coord_decomp (-(Real.pi / 6 - W.v_lo)) (X_use - (W.L : ℂ))
    rw [show -(Real.pi / 6 - W.v_lo) + Real.pi / 6 = W.v_lo by ring] at hdec
    have h1 : rotC (-(Real.pi / 3)) (X_use - (W.L : ℂ)) =
        (2 * cross (dir W.v_lo) (X_use - (W.L : ℂ))) • dir (W.v_lo + Real.pi / 2) +
        (-2 * cross (dir (-(Real.pi / 6 - W.v_lo))) (X_use - (W.L : ℂ))) • dir (W.v_lo + 2 * Real.pi / 3) := by
      conv_lhs => rw [hdec]
      rw [map_add, map_smul, map_smul, hrot_dir, hrot_dir]
      have hd1 : dir (-(Real.pi / 6 - W.v_lo) + -(Real.pi / 3)) = -dir (W.v_lo + Real.pi / 2) := by
        rw [show -(Real.pi / 6 - W.v_lo) + -(Real.pi / 3) = (W.v_lo + Real.pi / 2) - Real.pi by ring,
          dir_sub, dir_neg, dir_pi, map_neg, map_one, mul_neg_one]
      have hd2 : dir (W.v_lo + -(Real.pi / 3)) = -dir (W.v_lo + 2 * Real.pi / 3) := by
        rw [show W.v_lo + -(Real.pi / 3) = (W.v_lo + 2 * Real.pi / 3) - Real.pi by ring,
          dir_sub, dir_neg, dir_pi, map_neg, map_one, mul_neg_one]
      rw [hd1, hd2]; simp only [Complex.real_smul]; push_cast; ring
    rw [h1]; simp only [add_re, add_im, smul_re, smul_im, smul_eq_mul, dir_re, dir_im]
    have hc1 : Real.cos (W.v_lo + Real.pi / 2) ≤ 0 := by
      rw [Real.cos_add_pi_div_two]; linarith [Real.sin_nonneg_of_nonneg_of_le_pi W.hv_lo0 (by linarith [W.hv_lo_le, Real.pi_pos])]
    have hs1 : 0 ≤ Real.sin (W.v_lo + Real.pi / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [W.hv_lo0, Real.pi_pos]) (by linarith [W.hv_lo_le, Real.pi_pos])
    have hc2 : Real.cos (W.v_lo + 2 * Real.pi / 3) ≤ 0 :=
      (Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [W.hv_lo0, Real.pi_pos])
        (by linarith [W.hv_lo_le, Real.pi_pos])).le
    have hs2 : 0 ≤ Real.sin (W.v_lo + 2 * Real.pi / 3) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [W.hv_lo0, Real.pi_pos]) (by linarith [W.hv_lo_le, Real.pi_pos])
    exact ⟨by nlinarith, by nlinarith⟩
  have hYf_Q1 : 0 ≤ (Y'' - P3).re ∧ 0 ≤ (Y'' - P3).im := by
    rw [hYf_eq]
    have hdec := wedge_coord_decomp (-W.u_lo) Y_use
    rw [show -W.u_lo + Real.pi / 6 = Real.pi / 6 - W.u_lo by ring] at hdec
    have h1 : rotC (Real.pi / 3) Y_use =
        (-2 * cross (dir (Real.pi / 6 - W.u_lo)) Y_use) • dir (Real.pi / 3 - W.u_lo) +
        (2 * cross (dir (-W.u_lo)) Y_use) • dir (Real.pi / 2 - W.u_lo) := by
      conv_lhs => rw [hdec]
      rw [map_add, map_smul, map_smul, hrot_dir, hrot_dir]
      congr 2 <;> congr 1 <;> ring
    rw [h1]; simp only [add_re, add_im, smul_re, smul_im, smul_eq_mul, dir_re, dir_im]
    have hc1 : 0 ≤ Real.cos (Real.pi / 3 - W.u_lo) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [W.hu_lo_le, Real.pi_pos], by linarith [W.hu_lo0, Real.pi_pos]⟩
    have hs1 : 0 ≤ Real.sin (Real.pi / 3 - W.u_lo) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [W.hu_lo_le, Real.pi_pos]) (by linarith [W.hu_lo0, Real.pi_pos])
    have hc2 : 0 ≤ Real.cos (Real.pi / 2 - W.u_lo) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [W.hu_lo_le, Real.pi_pos], by linarith [W.hu_lo0, Real.pi_pos]⟩
    have hs2 : 0 ≤ Real.sin (Real.pi / 2 - W.u_lo) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [W.hu_lo_le, Real.pi_pos]) (by linarith [W.hu_lo0, Real.pi_pos])
    exact ⟨by nlinarith, by nlinarith⟩
  have hgt := sector60_chain_gt_one hAf_le hFf_le hXf_Q2.1 hXf_Q2.2 hYf_Q1.1 hYf_Q1.2
    (by rw [hXf_eq, (rotC _).norm_map]; exact hX_far)
    (by rw [hYf_eq, (rotC _).norm_map]; exact hY_far)
  have hs1 : (A'' - P3) - (X'' - P3) = A'' - X'' := by ring
  have hs2 : (X'' - P3) - (Y'' - P3) = X'' - Y'' := by ring
  have hs3 : (Y'' - P3) - (F'' - P3) = Y'' - F'' := by ring
  rw [hs1, hs2, hs3] at hgt; linarith

lemma case24_unclamped_finish {L u_lo v_lo α_eff β_eff tF_eff : ℝ}
    (hL : 0 < L) (hu0 : 0 ≤ u_lo) (hu_le : u_lo ≤ Real.pi / 6)
    (hv0 : 0 ≤ v_lo) (hv_le : v_lo ≤ Real.pi / 6)
    (hα_bounds : 0 ≤ α_eff ∧ α_eff ≤ v_lo)
    (hβ_bounds : 0 ≤ β_eff ∧ β_eff ≤ Real.pi / 6 - u_lo)
    (hβ_le_α : β_eff ≤ α_eff)
    {A_use X_use Y_use : ℂ}
    (hY_Ubot : 0 ≤ cross (dir (-u_lo)) Y_use)
    (hY_Utop : cross (dir (Real.pi / 6 - u_lo)) Y_use ≤ 0)
    (hY_Vtop : cross (dir (-(Real.pi / 6 - v_lo))) (Y_use - (L : ℂ)) ≤ 0)
    (hY_far : 1 < ‖Y_use‖)
    (hβ_eq : β_eff = Complex.arg ((L : ℂ) - tF_eff • dir (-(Real.pi / 6 - v_lo))))
    (hAf_le : Real.sqrt 3 * (rotC (-(Real.pi / 3) - (α_eff + β_eff) / 2) (A_use - (L : ℂ))).re +
      (rotC (-(Real.pi / 3) - (α_eff + β_eff) / 2) (A_use - (L : ℂ))).im ≤ 0)
    (hXf_Q2 : (rotC (-(Real.pi / 3) - (α_eff + β_eff) / 2) (X_use - (L : ℂ))).re ≤ 0 ∧
      0 ≤ (rotC (-(Real.pi / 3) - (α_eff + β_eff) / 2) (X_use - (L : ℂ))).im)
    (hXf_gt : 1 < ‖rotC (-(Real.pi / 3) - (α_eff + β_eff) / 2) (X_use - (L : ℂ))‖)
    (hchain_le1 :
      ‖rotC (-(Real.pi / 3) - (α_eff + β_eff) / 2) (A_use - (L : ℂ)) -
        rotC (-(Real.pi / 3) - (α_eff + β_eff) / 2) (X_use - (L : ℂ))‖ +
      ‖rotC (-(Real.pi / 3) - (α_eff + β_eff) / 2) (X_use - (L : ℂ)) -
        rotC (-(Real.pi / 3) - (α_eff + β_eff) / 2)
          (reflectLine (L • dir (Real.pi / 3)) (v_lo + Real.pi / 3) (rotC (Real.pi / 3) Y_use) - (L : ℂ))‖ +
      ‖rotC (-(Real.pi / 3) - (α_eff + β_eff) / 2)
          (reflectLine (L • dir (Real.pi / 3)) (v_lo + Real.pi / 3) (rotC (Real.pi / 3) Y_use) - (L : ℂ)) -
        rotC (-(Real.pi / 3) - (α_eff + β_eff) / 2)
          (reflectLine (L • dir (Real.pi / 3)) (v_lo + Real.pi / 3)
            (rotC (Real.pi / 3) ((L : ℂ) - tF_eff • dir (-(Real.pi / 6 - v_lo)))) - (L : ℂ))‖ ≤ 1) :
    False := by
  let Vp : ℂ := L • dir (Real.pi / 3)
  let M : ℂ → ℂ := fun z => reflectLine Vp (v_lo + Real.pi / 3) (rotC (Real.pi / 3) z)
  let θ_rot : ℝ := -(Real.pi / 3) - (α_eff + β_eff) / 2
  let frame : ℂ → ℂ := fun z => rotC θ_rot (z - (L : ℂ))
  let F_eff : ℂ := (L : ℂ) - tF_eff • dir (-(Real.pi / 6 - v_lo))
  have hrot_dir : ∀ θ φ, rotC θ (dir φ) = dir (φ + θ) := fun θ φ => by
    simp only [rotC_apply, dir, ← Complex.exp_add]; congr 1; push_cast; ring
  have hG_eq : ∀ z : ℂ, reflectLine Vp (v_lo + Real.pi / 2) (M z) =
      (L : ℂ) + z * dir (2 * Real.pi / 3) := fun z => by
    dsimp [M]; rw [reflectLine_comp, show 2 * (v_lo + Real.pi / 2 - (v_lo + Real.pi / 3)) = Real.pi / 3 by ring]
    have hVp_id : Vp - Vp * dir (Real.pi / 3) = (L : ℂ) := by
      show L • dir (Real.pi / 3) - (L • dir (Real.pi / 3)) * dir (Real.pi / 3) = (L : ℂ)
      apply Complex.ext
      · simp [dir_re, dir_im, Real.cos_pi_div_three, Real.sin_pi_div_three]
        have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        linear_combination (L / 4) * hsq3
      · simp [dir_re, dir_im, Real.cos_pi_div_three, Real.sin_pi_div_three]; ring
    have hz_rot : rotC (Real.pi / 3) z * dir (Real.pi / 3) = z * dir (2 * Real.pi / 3) := by
      rw [rotC_apply, show dir (Real.pi / 3) = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I) from rfl,
        show dir (2 * Real.pi / 3) = Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) from rfl]
      calc Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I) * z * Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I)
          = z * (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I) * Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I)) := by ring
        _ = z * Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) := by rw [← Complex.exp_add]; congr 2; push_cast; ring
    linear_combination hVp_id + hz_rot
  have hMF_eq : M F_eff - (L : ℂ) = F_eff * dir (2 * Real.pi / 3) := by
    have hfix : reflectLine Vp (v_lo + Real.pi / 2) (M F_eff) = M F_eff := by
      have h1 : M F_eff = Vp + (-tF_eff) • dir (v_lo + Real.pi / 2) := by
        change reflectLine Vp (v_lo + Real.pi / 3)
          (rotC (Real.pi / 3) ((L : ℂ) - tF_eff • dir (-(Real.pi / 6 - v_lo)))) = _
        have hr : rotC (Real.pi / 3) ((L : ℂ) - tF_eff • dir (-(Real.pi / 6 - v_lo))) =
            Vp + (-tF_eff) • dir (v_lo + Real.pi / 6) := by
          rw [map_sub, map_smul, hrot_dir,
            show rotC (Real.pi / 3) (L : ℂ) = Vp by dsimp [Vp]; simp [rotC_apply, dir, mul_comm],
            neg_smul]
          congr 2; congr 1; ring
        rw [hr, reflectLine_dir]; congr 3; ring
      (conv_lhs => rw [h1]); rw [reflectLine_fix_ray]; exact h1.symm
    rw [← hfix, hG_eq]; ring
  have hFf_le : -Real.sqrt 3 * (frame (M F_eff)).re + (frame (M F_eff)).im ≤ 0 := by
    have h1 : frame (M F_eff) = ‖F_eff‖ • dir (Real.pi / 3 - (α_eff - β_eff) / 2) := by
      change rotC θ_rot (M F_eff - (L : ℂ)) = _
      rw [hMF_eq]
      have hdir : F_eff = ‖F_eff‖ • dir β_eff := by
        rw [hβ_eq]; exact dir_arg_eq_smul F_eff
      (conv_lhs => rw [hdir])
      rw [show (‖F_eff‖ • dir β_eff) * dir (2 * Real.pi / 3) = ‖F_eff‖ • dir (β_eff + 2 * Real.pi / 3) by
        simp only [Complex.real_smul, dir_add]; ring, map_smul, hrot_dir]
      congr 2; dsimp [θ_rot]; ring
    rw [h1]; simp only [smul_re, smul_im, smul_eq_mul, dir_re, dir_im]
    have hid : -Real.sqrt 3 * Real.cos (Real.pi / 3 - (α_eff - β_eff) / 2) +
        Real.sin (Real.pi / 3 - (α_eff - β_eff) / 2) = -2 * Real.sin ((α_eff - β_eff) / 2) := by
      rw [Real.cos_sub, Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
      have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      linear_combination -(Real.sin ((α_eff - β_eff) / 2) / 2) * hsq3
    have hsn : 0 ≤ Real.sin ((α_eff - β_eff) / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hα_bounds.2, hv_le, hβ_bounds.1, Real.pi_pos])
    have hmul : -Real.sqrt 3 * (‖F_eff‖ * Real.cos (Real.pi / 3 - (α_eff - β_eff) / 2)) +
        ‖F_eff‖ * Real.sin (Real.pi / 3 - (α_eff - β_eff) / 2) =
        ‖F_eff‖ * (-2 * Real.sin ((α_eff - β_eff) / 2)) := by linear_combination ‖F_eff‖ * hid
    nlinarith [norm_nonneg F_eff]
  set c : ℝ := -2 * cross (dir (-(Real.pi / 6 - v_lo))) (Y_use - (L : ℂ))
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  let Ystar : ℂ := (L : ℂ) + Y_use * dir (2 * Real.pi / 3)
  have hMY_sub_Ystar : M Y_use = Ystar - c • dir v_lo := by
    have hdec := wedge_coord_decomp (-(Real.pi / 6 - v_lo)) (Y_use - (L : ℂ))
    rw [show -(Real.pi / 6 - v_lo) + Real.pi / 6 = v_lo by ring] at hdec
    set d : ℝ := 2 * cross (dir v_lo) (Y_use - (L : ℂ))
    have hY_dec : Y_use = (L : ℂ) + (-d) • dir (-(Real.pi / 6 - v_lo)) + (-c) • dir v_lo := by
      have hcd : (-d) • dir (-(Real.pi / 6 - v_lo)) + (-c) • dir v_lo = Y_use - (L : ℂ) := by
        rw [hdec]; congr 1
        · congr 1; dsimp [d]; ring
        · congr 1; dsimp [c]; ring
      linear_combination -hcd
    have hrotY : rotC (Real.pi / 3) Y_use =
        Vp + (-d) • dir (v_lo + Real.pi / 6) + (-c) • dir (v_lo + Real.pi / 3) := by
      (conv_lhs => rw [hY_dec])
      rw [map_add, map_add, map_smul, map_smul, hrot_dir, hrot_dir,
        show rotC (Real.pi / 3) (L : ℂ) = Vp by dsimp [Vp]; simp [rotC_apply, dir, mul_comm]]
      congr 2; congr 1; ring
    have hMY_dec : M Y_use = Vp + (-d) • dir (v_lo + Real.pi / 2) + (-c) • dir (v_lo + Real.pi / 3) := by
      dsimp [M]; rw [hrotY]; unfold reflectLine
      have hsub : (Vp + (-d) • dir (v_lo + Real.pi / 6) + (-c) • dir (v_lo + Real.pi / 3)) - Vp =
          (-d) • dir (v_lo + Real.pi / 6) + (-c) • dir (v_lo + Real.pi / 3) := by ring
      rw [hsub, map_add, Complex.real_smul, Complex.real_smul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        ← dir_neg, ← dir_neg, add_mul, mul_assoc, mul_assoc, ← dir_add, ← dir_add]
      have h1 : -(v_lo + Real.pi / 6) + 2 * (v_lo + Real.pi / 3) = v_lo + Real.pi / 2 := by ring
      have h2 : -(v_lo + Real.pi / 3) + 2 * (v_lo + Real.pi / 3) = v_lo + Real.pi / 3 := by ring
      rw [h1, h2]; ring
    have hGY_dec : Ystar = Vp + (-d) • dir (v_lo + Real.pi / 2) + (-c) • dir (v_lo + 2 * Real.pi / 3) := by
      dsimp [Ystar]; rw [← hG_eq, hMY_dec]; unfold reflectLine
      have hsub : (Vp + (-d) • dir (v_lo + Real.pi / 2) + (-c) • dir (v_lo + Real.pi / 3)) - Vp =
          (-d) • dir (v_lo + Real.pi / 2) + (-c) • dir (v_lo + Real.pi / 3) := by ring
      rw [hsub, map_add, Complex.real_smul, Complex.real_smul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        ← dir_neg, ← dir_neg, add_mul, mul_assoc, mul_assoc, ← dir_add, ← dir_add]
      have h1 : -(v_lo + Real.pi / 2) + 2 * (v_lo + Real.pi / 2) = v_lo + Real.pi / 2 := by ring
      have h2 : -(v_lo + Real.pi / 3) + 2 * (v_lo + Real.pi / 2) = v_lo + 2 * Real.pi / 3 := by ring
      rw [h1, h2]; ring
    have hdiff : dir (v_lo + 2 * Real.pi / 3) - dir (v_lo + Real.pi / 3) = -dir v_lo := by
      rw [dir_add, dir_add, ← mul_sub]
      have h1 : dir (2 * Real.pi / 3) - dir (Real.pi / 3) = -1 := by
        apply Complex.ext
        · simp [dir_re, Real.cos_pi_div_three,
            show Real.cos (2 * Real.pi / 3) = -(1 / 2) by
              rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]]; ring
        · simp [dir_im, Real.sin_pi_div_three,
            show Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 by
              rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]]
      rw [h1, mul_neg_one]
    rw [hMY_dec, hGY_dec]
    simp only [Complex.real_smul]; push_cast
    linear_combination (c : ℂ) * hdiff
  have hYf_gt : 1 < ‖frame (M Y_use)‖ := by
    dsimp [frame]; rw [(rotC _).norm_map]
    have hVp_dist : ‖M Y_use - Vp‖ = ‖Ystar - Vp‖ := by
      have hVp_fix : reflectLine Vp (v_lo + Real.pi / 2) Vp = Vp := by unfold reflectLine; simp
      have h := reflectLine_dist Vp (v_lo + Real.pi / 2) (M Y_use) Vp
      rw [hG_eq Y_use, hVp_fix] at h
      exact h.symm
    have hsq_diff : ‖M Y_use - (L : ℂ)‖ ^ 2 - ‖Ystar - (L : ℂ)‖ ^ 2 =
        2 * dotC ((L : ℂ) - Vp) (Ystar - M Y_use) := by
      have h1 : M Y_use - (L : ℂ) = (M Y_use - Vp) - ((L : ℂ) - Vp) := by ring
      have h2 : Ystar - (L : ℂ) = (Ystar - Vp) - ((L : ℂ) - Vp) := by ring
      have h3 : Ystar - M Y_use = (Ystar - Vp) - (M Y_use - Vp) := by ring
      rw [h1, h2, h3, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      have hsqV : (M Y_use - Vp).re * (M Y_use - Vp).re + (M Y_use - Vp).im * (M Y_use - Vp).im =
          (Ystar - Vp).re * (Ystar - Vp).re + (Ystar - Vp).im * (Ystar - Vp).im := by
        have := congrArg (fun t : ℝ => t ^ 2) hVp_dist
        simpa [Complex.sq_norm, Complex.normSq_apply] using this
      simp only [sub_re, sub_im] at hsqV
      unfold dotC; simp only [sub_re, sub_im]
      linear_combination hsqV
    have hLVp : (L : ℂ) - Vp = L • dir (-(Real.pi / 3)) := by
      show (L : ℂ) - L • dir (Real.pi / 3) = L • dir (-(Real.pi / 3))
      apply Complex.ext
      · simp [dir_re, Real.cos_pi_div_three]; ring
      · simp [dir_im, Real.sin_pi_div_three]
    have hYM : Ystar - M Y_use = c • dir v_lo := by rw [hMY_sub_Ystar]; ring
    have hdot_nn : 0 ≤ dotC ((L : ℂ) - Vp) (Ystar - M Y_use) := by
      rw [hLVp, hYM, dotC_smul_right,
        show dotC (L • dir (-(Real.pi / 3))) (dir v_lo) = L * dotC (dir (-(Real.pi / 3))) (dir v_lo) by
          unfold dotC; simp; ring, dotC_dir_dir]
      have hcos : 0 ≤ Real.cos (v_lo - -(Real.pi / 3)) :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hv0, Real.pi_pos], by linarith [hv_le, Real.pi_pos]⟩
      exact mul_nonneg hc0 (mul_nonneg hL.le hcos)
    have hYstar_n : ‖Ystar - (L : ℂ)‖ = ‖Y_use‖ := by
      dsimp [Ystar]; rw [add_sub_cancel_left, norm_mul, dir_norm, mul_one]
    have hge : ‖Y_use‖ ≤ ‖M Y_use - (L : ℂ)‖ := by
      rw [← hYstar_n]
      nlinarith [norm_nonneg (M Y_use - (L : ℂ)), norm_nonneg (Ystar - (L : ℂ))]
    linarith
  let ψ : ℝ := 2 * Real.pi / 3 + v_lo - (α_eff + β_eff) / 2
  have hψ_lo : 2 * Real.pi / 3 ≤ ψ := by dsimp [ψ]; linarith [hα_bounds.2, hβ_le_α]
  have hψ_hi : ψ ≤ 5 * Real.pi / 6 := by dsimp [ψ]; linarith [hv_le, hα_bounds.1, hβ_bounds.1]
  have hYf_shift : frame (M Y_use) = frame Ystar + c • dir ψ := by
    change rotC θ_rot (M Y_use - (L : ℂ)) = rotC θ_rot (Ystar - (L : ℂ)) + c • dir ψ
    rw [hMY_sub_Ystar, show Ystar - c • dir v_lo - (L : ℂ) =
      (Ystar - (L : ℂ)) + (-c) • dir v_lo by rw [neg_smul]; ring,
      map_add, map_smul, hrot_dir, neg_smul, ← smul_neg]
    have hd : -dir (v_lo + θ_rot) = dir ψ := by
      rw [show ψ = (v_lo + θ_rot) + Real.pi by dsimp [ψ, θ_rot]; ring,
        dir_add (v_lo + θ_rot) Real.pi, dir_pi, mul_neg_one]
    rw [hd]
  have hY_ne : Y_use ≠ 0 := fun h => by rw [h, norm_zero] at hY_far; linarith
  have hY_re_pos : 0 < Y_use.re := by
    have hdec := wedge_coord_decomp (-u_lo) Y_use
    rw [show -u_lo + Real.pi / 6 = Real.pi / 6 - u_lo by ring] at hdec
    set a : ℝ := -2 * cross (dir (Real.pi / 6 - u_lo)) Y_use
    set b : ℝ := 2 * cross (dir (-u_lo)) Y_use
    have ha0 : 0 ≤ a := by dsimp [a]; linarith
    have hb0 : 0 ≤ b := by dsimp [b]; linarith
    have hnot0 : ¬ (a = 0 ∧ b = 0) := by
      rintro ⟨h1, h2⟩; rw [h1, h2, zero_smul, zero_smul, add_zero] at hdec; exact hY_ne hdec
    have hc1 : 0 < Real.cos (-u_lo) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hu_le, Real.pi_pos], by linarith [hu0, Real.pi_pos]⟩
    have hc2 : 0 < Real.cos (Real.pi / 6 - u_lo) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hu_le, Real.pi_pos], by linarith [hu0, Real.pi_pos]⟩
    have hre : Y_use.re = a * Real.cos (-u_lo) + b * Real.cos (Real.pi / 6 - u_lo) := by
      (conv_lhs => rw [hdec]); simp only [add_re, smul_re, smul_eq_mul, dir_re]
    rw [hre]
    rcases eq_or_lt_of_le ha0 with h1 | h1
    · have h2 : 0 < b := lt_of_le_of_ne hb0 (fun h => hnot0 ⟨h1.symm, h.symm⟩)
      rw [← h1, zero_mul, zero_add]; exact mul_pos h2 hc2
    · linarith [mul_pos h1 hc1, mul_nonneg hb0 hc2.le]
  let φY : ℝ := Complex.arg Y_use
  have hφY_abs : |φY| < Real.pi / 2 := by
    have h := abs_arg_le_pi_div_two_of_re_nonneg hY_ne hY_re_pos.le
    rcases eq_or_lt_of_le h with heq | hlt
    · exfalso; have hc := Complex.cos_arg hY_ne
      have hcos0 : Real.cos (Complex.arg Y_use) = 0 := by
        rcases abs_eq (by linarith [Real.pi_pos]) |>.mp heq with h1 | h1
        · rw [h1, Real.cos_pi_div_two]
        · rw [h1, Real.cos_neg, Real.cos_pi_div_two]
      rw [hcos0] at hc
      have : Y_use.re = 0 := (div_eq_zero_iff.mp hc.symm).resolve_right (norm_ne_zero_iff.mpr hY_ne)
      linarith
    · exact hlt
  have hφY_lo : -u_lo ≤ φY := by
    have hcr := hY_Ubot
    rw [dir_arg_eq_smul Y_use, cross_smul_right, cross_dir_dir] at hcr
    have hsn : 0 ≤ Real.sin (φY + u_lo) := by
      rw [show φY + u_lo = Complex.arg Y_use - -u_lo by dsimp [φY]; ring]
      exact nonneg_of_mul_nonneg_right hcr (norm_pos_iff.mpr hY_ne)
    by_contra hlt; push Not at hlt
    have hneg : Real.sin (-(φY + u_lo)) > 0 :=
      Real.sin_pos_of_pos_of_lt_pi (x := -(φY + u_lo)) (by linarith)
        (by linarith [(abs_lt.mp hφY_abs).1, hu0, Real.pi_pos])
    rw [Real.sin_neg] at hneg; linarith
  have hφY_hi : φY ≤ Real.pi / 6 - u_lo := by
    have hcr := hY_Utop
    rw [dir_arg_eq_smul Y_use, cross_smul_right, cross_dir_dir] at hcr
    have hsn : Real.sin (φY - (Real.pi / 6 - u_lo)) ≤ 0 := by
      change Real.sin (Complex.arg Y_use - (Real.pi / 6 - u_lo)) ≤ 0
      exact nonpos_of_mul_nonpos_right hcr (norm_pos_iff.mpr hY_ne)
    by_contra hgt; push Not at hgt
    have hpos : 0 < Real.sin (φY - (Real.pi / 6 - u_lo)) :=
      Real.sin_pos_of_pos_of_lt_pi (x := φY - (Real.pi / 6 - u_lo)) (by linarith)
        (by linarith [(abs_lt.mp hφY_abs).2, hu_le, Real.pi_pos])
    linarith
  let θs : ℝ := φY + Real.pi / 3 - (α_eff + β_eff) / 2
  have hYsf_norm : ‖frame Ystar‖ = ‖Y_use‖ := by
    dsimp [frame, Ystar]; rw [add_sub_cancel_left, (rotC _).norm_map, norm_mul, dir_norm, mul_one]
  have hYsf_eq : frame Ystar = ‖frame Ystar‖ • dir θs := by
    rw [hYsf_norm]
    change rotC θ_rot (((L : ℂ) + Y_use * dir (2 * Real.pi / 3)) - (L : ℂ)) = ‖Y_use‖ • dir θs
    rw [add_sub_cancel_left]
    have hdir := dir_arg_eq_smul Y_use
    (conv_lhs => rw [hdir])
    rw [show (‖Y_use‖ • dir φY) * dir (2 * Real.pi / 3) = ‖Y_use‖ • dir (φY + 2 * Real.pi / 3) by
      simp only [Complex.real_smul, dir_add]; ring, map_smul, hrot_dir]
    congr 2; dsimp [θs, θ_rot]; ring
  have hθs_lo : 0 ≤ θs := by dsimp [θs]; linarith [hu_le, hα_bounds.2, hβ_le_α, hv_le]
  have hθs_hi : θs ≤ Real.pi / 2 := by dsimp [θs]; linarith [hu0, hα_bounds.1, hβ_bounds.1]
  have hYf_im : 0 ≤ (frame (M Y_use)).im := by
    rw [hYf_shift, hYsf_eq]; simp only [add_im, smul_im, smul_eq_mul, dir_im]
    have hs1 : 0 ≤ Real.sin θs := Real.sin_nonneg_of_nonneg_of_le_pi hθs_lo (by linarith [Real.pi_pos])
    have hs2 : 0 ≤ Real.sin ψ := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    nlinarith [norm_nonneg (frame Ystar)]
  by_cases hYf_re : 0 ≤ (frame (M Y_use)).re
  · have hgt := sector60_chain_gt_one hAf_le hFf_le hXf_Q2.1 hXf_Q2.2 hYf_re hYf_im hXf_gt hYf_gt
    linarith
  · push Not at hYf_re
    have hcoupled : 2 * ψ - θs ≤ 3 * Real.pi / 2 := by
      dsimp [ψ, θs]; linarith [hv_le, hu_le, hα_bounds.1, hβ_bounds.1]
    have hgt := case24_neg_xY_bound hAf_le hFf_le hXf_Q2.1 hXf_Q2.2 hXf_gt hYf_re hc0 hYf_shift
      hψ_lo hψ_hi hYsf_eq (by rw [hYsf_norm]; exact hY_far) hθs_hi hcoupled
    linarith

set_option maxHeartbeats 800000 in
lemma case24_wlog_contradiction {N : ℕ} {r : Fin (N + 1) → ℂ}
    (hlen : polyLen r ≤ 1) (W : TwoWedgeBase r)
    {A B QU QV E F x y : Fin (N + 1)} {tA tB tQU tQV tE tF : ℝ}
    (hAB : A < B) (hBQU : B < QU) (hQUE : QU ≤ E) (hEF : E < F)
    (htAQU : tA < tQU) (htFQV : tF < tQV)
    (hOnA : OnUbot W A tA) (hOnB : OnUtop W B tB) (hOnQU : OnUbot W QU tQU)
    (hOnQV : OnVtop W QV tQV) (hOnE : OnVbot W E tE) (hOnF : OnVtop W F tF)
    (hxB : x ≤ B) (hx_far : 1 < ‖r x - (W.L : ℂ)‖)
    (hEy : E ≤ y) (hy_far : 1 < ‖r y‖)
    (hαβ : Complex.arg ((W.L : ℂ) - (if y ≤ F then tF else max 0 (tF - ‖r y - r F‖)) • dir (-(Real.pi / 6 - W.v_lo))) ≤
           Complex.arg ((W.L : ℂ) - (if A ≤ x then tA else max 0 (tA - ‖r x - r A‖)) • dir (-W.u_lo))) :
    False := by
  let tA_eff : ℝ := if A ≤ x then tA else max 0 (tA - ‖r x - r A‖)
  let tF_eff : ℝ := if y ≤ F then tF else max 0 (tF - ‖r y - r F‖)
  let A_eff : ℂ := tA_eff • dir (-W.u_lo)
  let F_eff : ℂ := (W.L : ℂ) - tF_eff • dir (-(Real.pi / 6 - W.v_lo))
  let α_eff : ℝ := Complex.arg ((W.L : ℂ) - A_eff)
  let β_eff : ℝ := Complex.arg F_eff
  have hβ_le_α : β_eff ≤ α_eff := hαβ
  have htQU_le : tQU ≤ W.L * Real.cos W.u_lo :=
    onUbot_le_L_cos W hOnQU.1 (hOnQU.2 ▸ ⟨W.hU_bot QU, W.hU_top QU, W.hV_top QU, W.hV_bot QU⟩)
  have htQV_le : tQV ≤ W.L * Real.cos (Real.pi / 6 - W.v_lo) := by
    let Wr := twoWedgeBase_rot180 W
    have hQV_mem : tQV • dir (-Wr.u_lo) ∈ wedgeSet Wr := by
      have h1 : tQV • dir (-Wr.u_lo) = (fun k => (W.L : ℂ) - r k.rev) QV.rev := by
        show tQV • dir (-(Real.pi / 6 - W.v_lo)) = (W.L : ℂ) - r QV.rev.rev
        rw [Fin.rev_rev, hOnQV.2]; ring
      rw [h1]
      exact ⟨Wr.hU_bot QV.rev, Wr.hU_top QV.rev, Wr.hV_top QV.rev, Wr.hV_bot QV.rev⟩
    exact onUbot_le_L_cos Wr hOnQV.1 hQV_mem
  have htA_eff0 : 0 ≤ tA_eff := by
    dsimp [tA_eff]; split_ifs; exact hOnA.1; exact le_max_left _ _
  have htA_eff_le : tA_eff ≤ tA := by
    dsimp [tA_eff]; split_ifs; exact le_rfl; exact max_le hOnA.1 (by linarith [norm_nonneg (r x - r A)])
  have htF_eff0 : 0 ≤ tF_eff := by
    dsimp [tF_eff]; split_ifs; exact hOnF.1; exact le_max_left _ _
  have htF_eff_le : tF_eff ≤ tF := by
    dsimp [tF_eff]; split_ifs; exact le_rfl; exact max_le hOnF.1 (by linarith [norm_nonneg (r y - r F)])
  have hA_eff_mem : A_eff ∈ wedgeSet W := by
    have h0_mem : (0 : ℂ) ∈ wedgeSet W := by
      refine ⟨by simp [cross], by simp [cross], ?_, ?_⟩
      · rw [zero_sub, cross_neg_right]; unfold cross; rw [dir_re, dir_im, Real.sin_neg]; simp
        have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ Real.pi / 6 - W.v_lo by linarith [W.hv_lo_le])
          (by linarith [W.hv_lo0, Real.pi_pos])
        nlinarith [W.hL]
      · rw [zero_sub, cross_neg_right]; unfold cross; rw [dir_re, dir_im]; simp
        have := Real.sin_nonneg_of_nonneg_of_le_pi W.hv_lo0 (by linarith [W.hv_lo_le, Real.pi_pos])
        nlinarith [W.hL]
    have hA_mem : r A ∈ wedgeSet W := ⟨W.hU_bot A, W.hU_top A, W.hV_top A, W.hV_bot A⟩
    by_cases h0 : tA = 0
    · have : tA_eff = 0 := le_antisymm (by linarith) htA_eff0
      simpa [A_eff, this] using h0_mem
    · have htA_pos : 0 < tA := lt_of_le_of_ne hOnA.1 (Ne.symm h0)
      have hconv : A_eff = (1 - tA_eff / tA) • (0 : ℂ) + (tA_eff / tA) • r A := by
        rw [show A_eff = tA_eff • dir (-W.u_lo) from rfl, smul_zero, zero_add, hOnA.2, smul_smul,
          div_mul_cancel₀ _ htA_pos.ne']
      rw [hconv]
      exact wedgeSet_convex W h0_mem hA_mem
        (by rw [sub_nonneg, div_le_one htA_pos]; exact htA_eff_le) (div_nonneg htA_eff0 htA_pos.le) (by ring)
  have hF_eff_mem : F_eff ∈ wedgeSet W := by
    have hL_mem : (W.L : ℂ) ∈ wedgeSet W := by
      refine ⟨?_, ?_, by simp [cross], by simp [cross]⟩
      · unfold cross; rw [dir_re, dir_im, Real.sin_neg]; simp
        have := Real.sin_nonneg_of_nonneg_of_le_pi W.hu_lo0 (by linarith [W.hu_lo_le, Real.pi_pos])
        nlinarith [W.hL]
      · unfold cross; rw [dir_re, dir_im]; simp
        have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ Real.pi / 6 - W.u_lo by linarith [W.hu_lo_le])
          (by linarith [W.hu_lo0, Real.pi_pos])
        nlinarith [W.hL]
    have hF_mem : r F ∈ wedgeSet W := ⟨W.hU_bot F, W.hU_top F, W.hV_top F, W.hV_bot F⟩
    by_cases h0 : tF = 0
    · have : tF_eff = 0 := le_antisymm (by linarith) htF_eff0
      simpa [F_eff, this] using hL_mem
    · have htF_pos : 0 < tF := lt_of_le_of_ne hOnF.1 (Ne.symm h0)
      have hconv : F_eff = (1 - tF_eff / tF) • (W.L : ℂ) + (tF_eff / tF) • r F := by
        rw [show F_eff = (W.L : ℂ) - tF_eff • dir (-(Real.pi / 6 - W.v_lo)) from rfl, hOnF.2]
        simp only [Complex.real_smul]; push_cast
        have hdiv : (tF_eff : ℂ) / (tF : ℂ) * (tF : ℂ) = (tF_eff : ℂ) :=
          div_mul_cancel₀ _ (by exact_mod_cast htF_pos.ne')
        linear_combination dir (-(Real.pi / 6 - W.v_lo)) * hdiv
      rw [hconv]
      exact wedgeSet_convex W hL_mem hF_mem
        (by rw [sub_nonneg, div_le_one htF_pos]; exact htF_eff_le) (div_nonneg htF_eff0 htF_pos.le) (by ring)
  -- Bounds 0 ≤ α_eff ≤ W.v_lo and 0 ≤ β_eff ≤ π/6 - W.u_lo!
  have hLA_re_pos : 0 < ((W.L : ℂ) - A_eff).re := by
    change 0 < ((W.L : ℂ) - tA_eff • dir (-W.u_lo)).re
    simp only [sub_re, ofReal_re, smul_re, smul_eq_mul, dir_re, Real.cos_neg]
    have hcos_pos : 0 < Real.cos W.u_lo :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [W.hu_lo0, Real.pi_pos], by linarith [W.hu_lo_le, Real.pi_pos]⟩
    have hcos_le : Real.cos W.u_lo ≤ 1 := Real.cos_le_one _
    have hltL : tA_eff < W.L := by nlinarith [W.hL]
    nlinarith
  have hLA_ne : (W.L : ℂ) - A_eff ≠ 0 := fun h => by rw [h, zero_re] at hLA_re_pos; linarith
  have hα_bounds : 0 ≤ α_eff ∧ α_eff ≤ W.v_lo := by
    have h0 : 0 ≤ α_eff := by
      apply Complex.arg_nonneg_iff.mpr
      change 0 ≤ ((W.L : ℂ) - tA_eff • dir (-W.u_lo)).im
      simp only [sub_im, ofReal_im, smul_im, smul_eq_mul, dir_im, Real.sin_neg]
      have := Real.sin_nonneg_of_nonneg_of_le_pi W.hu_lo0 (by linarith [W.hu_lo_le, Real.pi_pos])
      nlinarith
    have hlt_pi2 : α_eff < Real.pi / 2 := by
      have h := abs_arg_le_pi_div_two_of_re_nonneg hLA_ne hLA_re_pos.le
      rcases eq_or_lt_of_le (abs_le.mp h).2 with heq | hlt
      · exfalso; have hc := Complex.cos_arg hLA_ne
        rw [show Complex.arg ((W.L : ℂ) - A_eff) = Real.pi / 2 from heq, Real.cos_pi_div_two] at hc
        have : ((W.L : ℂ) - A_eff).re = 0 := by
          have := (div_eq_zero_iff.mp hc.symm).resolve_right (norm_ne_zero_iff.mpr hLA_ne); exact this
        linarith
      · exact hlt
    have hcr : cross (dir W.v_lo) ((W.L : ℂ) - A_eff) ≤ 0 := by
      rw [show (W.L : ℂ) - A_eff = -(A_eff - (W.L : ℂ)) by ring, cross_neg_right]
      linarith [hA_eff_mem.2.2.2]
    have hsin : Real.sin (α_eff - W.v_lo) ≤ 0 := by
      rw [← cross_dir_dir]
      have h1 := dir_arg_eq_smul ((W.L : ℂ) - A_eff)
      rw [h1, cross_smul_right] at hcr
      exact nonpos_of_mul_nonpos_right hcr (norm_pos_iff.mpr hLA_ne)
    have hle : α_eff ≤ W.v_lo := by
      by_contra hgt; push Not at hgt
      have := Real.sin_pos_of_pos_of_lt_pi (x := α_eff - W.v_lo) (by linarith) (by linarith [W.hv_lo0, Real.pi_pos])
      linarith
    exact ⟨h0, hle⟩
  have hF_re_pos : 0 < F_eff.re := by
    change 0 < ((W.L : ℂ) - tF_eff • dir (-(Real.pi / 6 - W.v_lo))).re
    simp only [sub_re, ofReal_re, smul_re, smul_eq_mul, dir_re, Real.cos_neg]
    have hcos_pos : 0 < Real.cos (Real.pi / 6 - W.v_lo) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [W.hv_lo_le, Real.pi_pos], by linarith [W.hv_lo0, Real.pi_pos]⟩
    have hcos_le : Real.cos (Real.pi / 6 - W.v_lo) ≤ 1 := Real.cos_le_one _
    have hltL : tF_eff < W.L := by nlinarith [W.hL]
    nlinarith
  have hF_ne : F_eff ≠ 0 := fun h => by rw [h, zero_re] at hF_re_pos; linarith
  have hβ_bounds : 0 ≤ β_eff ∧ β_eff ≤ Real.pi / 6 - W.u_lo := by
    have h0 : 0 ≤ β_eff := by
      apply Complex.arg_nonneg_iff.mpr
      change 0 ≤ ((W.L : ℂ) - tF_eff • dir (-(Real.pi / 6 - W.v_lo))).im
      simp only [sub_im, ofReal_im, smul_im, smul_eq_mul, dir_im, Real.sin_neg]
      have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ Real.pi / 6 - W.v_lo by linarith [W.hv_lo_le])
        (by linarith [W.hv_lo0, Real.pi_pos])
      nlinarith
    have hlt_pi2 : β_eff < Real.pi / 2 := by
      have h := abs_arg_le_pi_div_two_of_re_nonneg hF_ne hF_re_pos.le
      rcases eq_or_lt_of_le (abs_le.mp h).2 with heq | hlt
      · exfalso; have hc := Complex.cos_arg hF_ne
        rw [show Complex.arg F_eff = Real.pi / 2 from heq, Real.cos_pi_div_two] at hc
        have : F_eff.re = 0 := (div_eq_zero_iff.mp hc.symm).resolve_right (norm_ne_zero_iff.mpr hF_ne)
        linarith
      · exact hlt
    have hcr := hF_eff_mem.2.1
    have hsin : Real.sin (β_eff - (Real.pi / 6 - W.u_lo)) ≤ 0 := by
      rw [← cross_dir_dir]
      have h1 := dir_arg_eq_smul F_eff
      rw [h1, cross_smul_right] at hcr
      exact nonpos_of_mul_nonpos_right hcr (norm_pos_iff.mpr hF_ne)
    have hle : β_eff ≤ Real.pi / 6 - W.u_lo := by
      by_contra hgt; push Not at hgt
      have := Real.sin_pos_of_pos_of_lt_pi (x := β_eff - (Real.pi / 6 - W.u_lo)) (by linarith)
        (by linarith [W.hu_lo_le, Real.pi_pos])
      linarith
    exact ⟨h0, hle⟩
  -- Chain budget!
  let leftLen : ℝ := if A ≤ x then ‖r x - r A‖ + ‖r B - r x‖ else ‖r A - r x‖ + ‖r B - r A‖
  let rightLen : ℝ := if y ≤ F then ‖r y - r E‖ + ‖r F - r y‖ else ‖r F - r E‖ + ‖r y - r F‖
  have htot_le : leftLen + ‖r QU - r B‖ + ‖r E - r QU‖ + rightLen ≤ 1 := by
    refine le_trans ?_ hlen
    dsimp [leftLen, rightLen]
    by_cases hAx : A ≤ x <;> by_cases hyF : y ≤ F
    · rw [if_pos hAx, if_pos hyF]
      linarith [chain7_le_polyLen r hAx hxB hBQU.le hQUE hEy hyF]
    · push Not at hyF; rw [if_pos hAx, if_neg (not_le.mpr hyF)]
      linarith [chain7_le_polyLen r hAx hxB hBQU.le hQUE hEF.le hyF.le]
    · push Not at hAx; rw [if_neg (not_le.mpr hAx), if_pos hyF]
      linarith [chain7_le_polyLen r hAx.le hAB.le hBQU.le hQUE hEy hyF]
    · push Not at hAx hyF; rw [if_neg (not_le.mpr hAx), if_neg (not_le.mpr hyF)]
      linarith [chain7_le_polyLen r hAx.le hAB.le hBQU.le hQUE hEF.le hyF.le]
  let Vp : ℂ := W.L • dir (Real.pi / 3)
  let M : ℂ → ℂ := fun z => reflectLine Vp (W.v_lo + Real.pi / 3) (rotC (Real.pi / 3) z)
  have hM_dist : ∀ z w : ℂ, ‖M z - M w‖ = ‖z - w‖ := fun z w => by
    dsimp [M]; rw [reflectLine_dist, ← map_sub, (rotC _).norm_map]
  let QU' : ℂ := reflectLine 0 (Real.pi / 6 - W.u_lo) (r QU)
  let E'' : ℂ := rotC (Real.pi / 3) (r E)
  have hrot_dir : ∀ θ φ, rotC θ (dir φ) = dir (φ + θ) := fun θ φ => by
    simp only [rotC_apply, dir, ← Complex.exp_add]; congr 1; push_cast; ring
  have hB_QU' : ‖r B - QU'‖ = ‖r QU - r B‖ := by
    have hB_fix : reflectLine 0 (Real.pi / 6 - W.u_lo) (r B) = r B := by
      have h1 : r B = 0 + tB • dir (Real.pi / 6 - W.u_lo) := by rw [zero_add, hOnB.2]
      (conv_lhs => rw [h1]); rw [reflectLine_fix_ray]; exact h1.symm
    dsimp [QU']; (conv_lhs => rw [← hB_fix]); rw [reflectLine_dist, norm_sub_rev]
  have hQU'_E'' : ‖QU' - E''‖ = ‖r E - r QU‖ := by
    have hrot_comp : ∀ z : ℂ, rotC (Real.pi / 3) z =
        reflectLine 0 (Real.pi / 3 - W.u_lo) (reflectLine 0 (Real.pi / 6 - W.u_lo) z) := fun z => by
      rw [reflectLine_comp, sub_zero, zero_add,
        show 2 * (Real.pi / 3 - W.u_lo - (Real.pi / 6 - W.u_lo)) = Real.pi / 3 by ring]
      simp [rotC_apply, dir, mul_comm]
    have hQU'_fix : reflectLine 0 (Real.pi / 3 - W.u_lo) QU' = QU' := by
      have h1 : QU' = 0 + tQU • dir (Real.pi / 3 - W.u_lo) := by
        dsimp [QU']; rw [hOnQU.2, show tQU • dir (-W.u_lo) = 0 + tQU • dir (-W.u_lo) by ring, reflectLine_dir]
        congr 3; ring
      (conv_lhs => rw [h1]); rw [reflectLine_fix_ray]; exact h1.symm
    dsimp [E'']; rw [hrot_comp]; (conv_lhs => rw [← hQU'_fix]); rw [reflectLine_dist, reflectLine_dist, norm_sub_rev]
  have hM_E : M (r E) = E'' := by
    dsimp [M, E'']
    have h1 : rotC (Real.pi / 3) (r E) = Vp + (-tE) • dir (W.v_lo + Real.pi / 3) := by
      rw [hOnE.2, map_sub, map_smul, hrot_dir,
        show rotC (Real.pi / 3) (W.L : ℂ) = Vp by dsimp [Vp]; simp [rotC_apply, dir, mul_comm],
        neg_smul]; ring
    (conv_lhs => rw [h1]); rw [reflectLine_fix_ray]; exact h1.symm
  -- Left (A_use, X_use)!
  have hleft : ∃ (A_use X_use : ℂ) (rA : ℝ), 0 ≤ rA ∧
      A_use - (W.L : ℂ) = (-rA) • dir α_eff ∧
      1 < ‖X_use - (W.L : ℂ)‖ ∧
      cross (dir (-(Real.pi / 6 - W.v_lo))) (X_use - (W.L : ℂ)) ≤ 0 ∧
      0 ≤ cross (dir W.v_lo) (X_use - (W.L : ℂ)) ∧
      ‖A_use - X_use‖ + ‖X_use - r B‖ ≤ leftLen := by
    by_cases hAx : A ≤ x
    · have hA_eq : A_eff = r A := by
        rw [show A_eff = tA_eff • dir (-W.u_lo) from rfl, show tA_eff = tA by dsimp [tA_eff]; rw [if_pos hAx], ← hOnA.2]
      refine ⟨r A, r x, ‖(W.L : ℂ) - A_eff‖, norm_nonneg _, ?_, hx_far, W.hV_top x, W.hV_bot x, ?_⟩
      · rw [← hA_eq, show A_eff - (W.L : ℂ) = -((W.L : ℂ) - A_eff) by ring, neg_smul,
          ← dir_arg_eq_smul ((W.L : ℂ) - A_eff)]
      · dsimp [leftLen]; rw [if_pos hAx, norm_sub_rev (r A) (r x), norm_sub_rev (r x) (r B)]
    · push Not at hAx
      have hfig7 := fig7_obtuse_dist (tA := tA) W.hL.le W.hu_lo0 W.hu_lo_le (by linarith [htAQU, htQU_le]) (W.hU_bot x)
      rw [← hOnA.2] at hfig7
      by_cases hclamp : ‖r x - r A‖ ≤ tA
      · have htA_eq : tA_eff = tA - ‖r x - r A‖ := by
          dsimp [tA_eff]; rw [if_neg (not_le.mpr hAx), max_eq_right (by linarith)]
        have hA_eq : A_eff = r A - ‖r x - r A‖ • dir (-W.u_lo) := by
          rw [show A_eff = tA_eff • dir (-W.u_lo) from rfl, htA_eq, hOnA.2, sub_smul]
        refine ⟨A_eff, A_eff, ‖(W.L : ℂ) - A_eff‖, norm_nonneg _, ?_,
          by rw [hA_eq]; linarith, hA_eff_mem.2.2.1, hA_eff_mem.2.2.2, ?_⟩
        · rw [show A_eff - (W.L : ℂ) = -((W.L : ℂ) - A_eff) by ring, neg_smul,
            ← dir_arg_eq_smul ((W.L : ℂ) - A_eff)]
        · rw [sub_self, norm_zero, zero_add]
          dsimp [leftLen]; rw [if_neg (not_le.mpr hAx)]
          have htri : ‖A_eff - r B‖ ≤ ‖A_eff - r A‖ + ‖r A - r B‖ := by
            have : A_eff - r B = (A_eff - r A) + (r A - r B) := by ring
            rw [this]; exact norm_add_le _ _
          have hAA : ‖A_eff - r A‖ = ‖r x - r A‖ := by
            rw [hA_eq, show r A - ‖r x - r A‖ • dir (-W.u_lo) - r A = -(‖r x - r A‖ • dir (-W.u_lo)) by ring,
              norm_neg, norm_smul, Real.norm_of_nonneg (norm_nonneg _), dir_norm, mul_one]
          rw [norm_sub_rev (r A) (r x), norm_sub_rev (r B) (r A)]; linarith
      · push Not at hclamp
        have htA0 : tA_eff = 0 := by
          dsimp [tA_eff]; rw [if_neg (not_le.mpr hAx), max_eq_left (by linarith)]
        have hα0 : α_eff = 0 := by
          change Complex.arg ((W.L : ℂ) - tA_eff • dir (-W.u_lo)) = 0
          rw [htA0, zero_smul, sub_zero]
          exact Complex.arg_eq_zero_iff.mpr ⟨W.hL.le, rfl⟩
        let r_rem : ℝ := ‖r x - r A‖ - tA
        have hr_pos : 0 < r_rem := by dsimp [r_rem]; linarith
        let Z : ℂ := -(r_rem : ℂ)
        refine ⟨Z, Z, W.L + r_rem, by linarith [W.hL], ?_, ?_, ?_, ?_, ?_⟩
        · rw [hα0, dir_zero, neg_smul, Complex.real_smul, mul_one]; dsimp [Z]; push_cast; ring
        · have hbar_le : ‖(r A - ‖r x - r A‖ • dir (-W.u_lo)) - (W.L : ℂ)‖ ≤ r_rem + W.L := by
            have h1 : (r A - ‖r x - r A‖ • dir (-W.u_lo)) - (W.L : ℂ) =
                (-r_rem) • dir (-W.u_lo) + (-(W.L : ℂ)) := by
              rw [show r_rem = ‖r x - r A‖ - tA from rfl, hOnA.2, Complex.real_smul, Complex.real_smul, Complex.real_smul]
              push_cast; ring
            rw [h1]
            calc ‖(-r_rem) • dir (-W.u_lo) + (-(W.L : ℂ))‖
                ≤ ‖(-r_rem) • dir (-W.u_lo)‖ + ‖-(W.L : ℂ)‖ := norm_add_le _ _
              _ = r_rem + W.L := by
                  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hr_pos, dir_norm, mul_one,
                    norm_neg, Complex.norm_of_nonneg W.hL.le]
          have hZL : ‖Z - (W.L : ℂ)‖ = r_rem + W.L := by
            dsimp [Z]; rw [show -(r_rem : ℂ) - (W.L : ℂ) = -((r_rem + W.L : ℝ) : ℂ) by push_cast; ring,
              norm_neg, Complex.norm_of_nonneg (by linarith [W.hL])]
          linarith
        · dsimp [Z]; unfold cross; rw [dir_re, dir_im, Real.sin_neg]
          simp only [sub_im, neg_im, ofReal_im, neg_zero, sub_self, mul_zero, sub_re, neg_re, ofReal_re]
          have := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ Real.pi / 6 - W.v_lo by linarith [W.hv_lo_le])
            (by linarith [W.hv_lo0, Real.pi_pos])
          nlinarith [W.hL]
        · dsimp [Z]; unfold cross; rw [dir_re, dir_im]
          simp only [sub_im, neg_im, ofReal_im, neg_zero, sub_self, mul_zero, sub_re, neg_re, ofReal_re]
          have := Real.sin_nonneg_of_nonneg_of_le_pi W.hv_lo0 (by linarith [W.hv_lo_le, Real.pi_pos])
          nlinarith [W.hL]
        · rw [sub_self, norm_zero, zero_add]
          dsimp [leftLen]; rw [if_neg (not_le.mpr hAx)]
          have htri : ‖Z - r B‖ ≤ ‖Z‖ + ‖r B‖ := by
            have : Z - r B = Z + (-r B) := by ring
            rw [this]; exact (norm_add_le Z (-r B)).trans (by rw [norm_neg (r B)])
          have hZn : ‖Z‖ = r_rem := by dsimp [Z]; rw [norm_neg, Complex.norm_of_nonneg hr_pos.le]
          have hBtri : ‖r B‖ ≤ ‖r A‖ + ‖r B - r A‖ := by
            have : r B = r A + (r B - r A) := by ring
            (conv_lhs => rw [this]); exact norm_add_le _ _
          have hAn : ‖r A‖ = tA := by rw [hOnA.2, norm_smul, Real.norm_of_nonneg hOnA.1, dir_norm, mul_one]
          rw [norm_sub_rev (r A) (r x)]; dsimp [r_rem] at hZn; linarith
  obtain ⟨A_use, X_use, rA, hrA0, hA_ray, hX_far, hX_Vtop, hX_Vbot, hleft_len⟩ := hleft
  -- Frame around V = W.L with +y along bis = 5π/6 + (α_eff + β_eff)/2!
  let θ_rot : ℝ := -(Real.pi / 3) - (α_eff + β_eff) / 2
  let frame : ℂ → ℂ := fun z => rotC θ_rot (z - (W.L : ℂ))
  have hframe_dist : ∀ z w : ℂ, ‖frame z - frame w‖ = ‖z - w‖ := fun z w => by
    dsimp [frame]; rw [← map_sub, (rotC _).norm_map]; congr 1; ring
  have hAf_le : Real.sqrt 3 * (frame A_use).re + (frame A_use).im ≤ 0 := by
    have h1 : frame A_use = rA • dir (2 * Real.pi / 3 + (α_eff - β_eff) / 2) := by
      change rotC θ_rot (A_use - (W.L : ℂ)) = rA • dir (2 * Real.pi / 3 + (α_eff - β_eff) / 2)
      rw [hA_ray, map_smul, hrot_dir, neg_smul, ← smul_neg]
      have hd : -dir (α_eff + θ_rot) = dir (2 * Real.pi / 3 + (α_eff - β_eff) / 2) := by
        rw [show 2 * Real.pi / 3 + (α_eff - β_eff) / 2 = (α_eff + θ_rot) + Real.pi by dsimp [θ_rot]; ring,
          dir_add (α_eff + θ_rot) Real.pi, dir_pi, mul_neg_one]
      rw [hd]
    rw [h1]; simp only [smul_re, smul_im, smul_eq_mul, dir_re, dir_im]
    have hid : Real.sqrt 3 * Real.cos (2 * Real.pi / 3 + (α_eff - β_eff) / 2) +
        Real.sin (2 * Real.pi / 3 + (α_eff - β_eff) / 2) = -2 * Real.sin ((α_eff - β_eff) / 2) := by
      rw [Real.cos_add, Real.sin_add]
      have hc : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
        rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
      have hs : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
        rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
      rw [hc, hs]
      have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      linear_combination -(Real.sin ((α_eff - β_eff) / 2) / 2) * hsq3
    have hsn : 0 ≤ Real.sin ((α_eff - β_eff) / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hα_bounds.2, W.hv_lo_le, hβ_bounds.1, Real.pi_pos])
    have hmul : Real.sqrt 3 * (rA * Real.cos (2 * Real.pi / 3 + (α_eff - β_eff) / 2)) +
        rA * Real.sin (2 * Real.pi / 3 + (α_eff - β_eff) / 2) =
        rA * (-2 * Real.sin ((α_eff - β_eff) / 2)) := by linear_combination rA * hid
    nlinarith
  have hXf_Q2 : (frame X_use).re ≤ 0 ∧ 0 ≤ (frame X_use).im := by
    dsimp [frame]
    have hdec := wedge_coord_decomp (-(Real.pi / 6 - W.v_lo)) (X_use - (W.L : ℂ))
    rw [show -(Real.pi / 6 - W.v_lo) + Real.pi / 6 = W.v_lo by ring] at hdec
    have h1 : rotC θ_rot (X_use - (W.L : ℂ)) =
        (2 * cross (dir W.v_lo) (X_use - (W.L : ℂ))) • dir (Real.pi / 2 + W.v_lo - (α_eff + β_eff) / 2) +
        (-2 * cross (dir (-(Real.pi / 6 - W.v_lo))) (X_use - (W.L : ℂ))) • dir (2 * Real.pi / 3 + W.v_lo - (α_eff + β_eff) / 2) := by
      conv_lhs => rw [hdec]
      rw [map_add, map_smul, map_smul, hrot_dir, hrot_dir]
      have hd1 : dir (-(Real.pi / 6 - W.v_lo) + θ_rot) = -dir (Real.pi / 2 + W.v_lo - (α_eff + β_eff) / 2) := by
        rw [show -(Real.pi / 6 - W.v_lo) + θ_rot = (Real.pi / 2 + W.v_lo - (α_eff + β_eff) / 2) - Real.pi by
          dsimp [θ_rot]; ring, dir_sub, dir_neg, dir_pi, map_neg, map_one, mul_neg_one]
      have hd2 : dir (W.v_lo + θ_rot) = -dir (2 * Real.pi / 3 + W.v_lo - (α_eff + β_eff) / 2) := by
        rw [show W.v_lo + θ_rot = (2 * Real.pi / 3 + W.v_lo - (α_eff + β_eff) / 2) - Real.pi by
          dsimp [θ_rot]; ring, dir_sub, dir_neg, dir_pi, map_neg, map_one, mul_neg_one]
      rw [hd1, hd2]; simp only [Complex.real_smul]; push_cast; ring
    rw [h1]; simp only [add_re, add_im, smul_re, smul_im, smul_eq_mul, dir_re, dir_im]
    have hδ0 : 0 ≤ W.v_lo - (α_eff + β_eff) / 2 := by linarith [hα_bounds.2, hβ_le_α]
    have hδ_le : W.v_lo - (α_eff + β_eff) / 2 ≤ Real.pi / 6 := by linarith [W.hv_lo_le, hα_bounds.1, hβ_bounds.1]
    have hc1 : Real.cos (Real.pi / 2 + W.v_lo - (α_eff + β_eff) / 2) ≤ 0 := by
      rw [show Real.pi / 2 + W.v_lo - (α_eff + β_eff) / 2 = (W.v_lo - (α_eff + β_eff) / 2) + Real.pi / 2 by ring,
        Real.cos_add_pi_div_two]
      linarith [Real.sin_nonneg_of_nonneg_of_le_pi hδ0 (by linarith [Real.pi_pos])]
    have hs1 : 0 ≤ Real.sin (Real.pi / 2 + W.v_lo - (α_eff + β_eff) / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hc2 : Real.cos (2 * Real.pi / 3 + W.v_lo - (α_eff + β_eff) / 2) ≤ 0 :=
      (Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).le
    have hs2 : 0 ≤ Real.sin (2 * Real.pi / 3 + W.v_lo - (α_eff + β_eff) / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    exact ⟨by nlinarith, by nlinarith⟩
  have hXf_gt : 1 < ‖frame X_use‖ := by dsimp [frame]; rw [(rotC _).norm_map]; exact hX_far
  -- Helper: given Y_use, F_use with rightLen bound, total transformed chain ≤ 1!
  have hchain_of_right : ∀ Y_use F_use : ℂ, ‖r E - Y_use‖ + ‖Y_use - F_use‖ ≤ rightLen →
      ‖frame A_use - frame X_use‖ + ‖frame X_use - frame (M Y_use)‖ +
        ‖frame (M Y_use) - frame (M F_use)‖ ≤ 1 := by
    intro Y_use F_use hR
    rw [hframe_dist, hframe_dist, hframe_dist, hM_dist]
    have htri : ‖X_use - M Y_use‖ ≤ ‖X_use - r B‖ + ‖r B - QU'‖ + ‖QU' - E''‖ + ‖E'' - M Y_use‖ := by
      have : X_use - M Y_use = ((X_use - r B) + (r B - QU')) + ((QU' - E'') + (E'' - M Y_use)) := by ring
      rw [this]
      have h1 := norm_add_le ((X_use - r B) + (r B - QU')) ((QU' - E'') + (E'' - M Y_use))
      have h2 := norm_add_le (X_use - r B) (r B - QU')
      have h3 := norm_add_le (QU' - E'') (E'' - M Y_use)
      linarith
    have hEY : ‖E'' - M Y_use‖ = ‖r E - Y_use‖ := by rw [← hM_E, hM_dist]
    linarith
  -- Right side: either clamped past L (y > F and tF < ‖r y - r F‖), OR Y_use ∈ wedgeSet W!
  by_cases hright_clamp : F < y ∧ tF < ‖r y - r F‖
  · rcases hright_clamp with ⟨hFy, hgt_tF⟩
    have htF0 : tF_eff = 0 := by
      dsimp [tF_eff]; rw [if_neg (not_le.mpr hFy), max_eq_left (by linarith)]
    have hβ0 : β_eff = 0 := by
      change Complex.arg ((W.L : ℂ) - tF_eff • dir (-(Real.pi / 6 - W.v_lo))) = 0
      rw [htF0, zero_smul, sub_zero]
      exact Complex.arg_eq_zero_iff.mpr ⟨W.hL.le, rfl⟩
    let s_rem : ℝ := ‖r y - r F‖ - tF
    have hs_pos : 0 < s_rem := by dsimp [s_rem]; linarith
    let Y_use : ℂ := (W.L : ℂ) + s_rem • dir (2 * W.v_lo - Real.pi / 3)
    have hMY_eq : M Y_use - (W.L : ℂ) = (W.L + s_rem) • dir (2 * Real.pi / 3) := by
      have hrotY : rotC (Real.pi / 3) Y_use = Vp + s_rem • dir (2 * W.v_lo) := by
        rw [show Y_use = (W.L : ℂ) + s_rem • dir (2 * W.v_lo - Real.pi / 3) from rfl, map_add, map_smul, hrot_dir,
          show rotC (Real.pi / 3) (W.L : ℂ) = Vp by dsimp [Vp]; simp [rotC_apply, dir, mul_comm]]
        congr 2; ring
      have hM : M Y_use = Vp + s_rem • dir (2 * Real.pi / 3) := by
        dsimp [M]; rw [hrotY, reflectLine_dir]; congr 3; ring
      have hVpL : Vp - (W.L : ℂ) = W.L • dir (2 * Real.pi / 3) := by
        show W.L • dir (Real.pi / 3) - (W.L : ℂ) = W.L • dir (2 * Real.pi / 3)
        apply Complex.ext
        · simp [dir_re, dir_im, Real.cos_pi_div_three,
            show Real.cos (2 * Real.pi / 3) = -(1 / 2) by
              rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]]; ring
        · simp [dir_re, dir_im, Real.sin_pi_div_three,
            show Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 by
              rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]]
      rw [hM, show Vp + s_rem • dir (2 * Real.pi / 3) - (W.L : ℂ) = (Vp - (W.L : ℂ)) + s_rem • dir (2 * Real.pi / 3) by ring,
        hVpL, add_smul]
    have hfar_clamp : 1 < W.L + s_rem := by
      let Xr : ℂ := (W.L : ℂ) - r y
      have hXr_bot : 0 ≤ cross (dir (-(Real.pi / 6 - W.v_lo))) Xr := by
        dsimp [Xr]; rw [show (W.L : ℂ) - r y = -(r y - (W.L : ℂ)) by ring, cross_neg_right]
        linarith [W.hV_top y]
      have hfig7 := fig7_obtuse_dist (u_lo := Real.pi / 6 - W.v_lo) (tA := tF) W.hL.le
        (by linarith [W.hv_lo_le]) (by linarith [W.hv_lo0]) (by linarith [htFQV, htQV_le]) hXr_bot
      have hXrL : ‖Xr - (W.L : ℂ)‖ = ‖r y‖ := by
        dsimp [Xr]; rw [show (W.L : ℂ) - r y - (W.L : ℂ) = -r y by ring, norm_neg]
      have hXrd : ‖Xr - tF • dir (-(Real.pi / 6 - W.v_lo))‖ = ‖r y - r F‖ := by
        have : Xr - tF • dir (-(Real.pi / 6 - W.v_lo)) = -(r y - r F) := by
          rw [show Xr = (W.L : ℂ) - r y from rfl, hOnF.2]; ring
        rw [this, norm_neg]
      rw [hXrL, hXrd] at hfig7
      have hbar_le : ‖(tF • dir (-(Real.pi / 6 - W.v_lo)) - ‖r y - r F‖ • dir (-(Real.pi / 6 - W.v_lo))) - (W.L : ℂ)‖ ≤
          s_rem + W.L := by
        have h1 : (tF • dir (-(Real.pi / 6 - W.v_lo)) - ‖r y - r F‖ • dir (-(Real.pi / 6 - W.v_lo))) - (W.L : ℂ) =
            (-s_rem) • dir (-(Real.pi / 6 - W.v_lo)) + (-(W.L : ℂ)) := by
          rw [show s_rem = ‖r y - r F‖ - tF from rfl, Complex.real_smul, Complex.real_smul, Complex.real_smul]
          push_cast; ring
        rw [h1]
        calc ‖(-s_rem) • dir (-(Real.pi / 6 - W.v_lo)) + (-(W.L : ℂ))‖
            ≤ ‖(-s_rem) • dir (-(Real.pi / 6 - W.v_lo))‖ + ‖-(W.L : ℂ)‖ := norm_add_le _ _
          _ = s_rem + W.L := by
              rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hs_pos, dir_norm, mul_one,
                norm_neg, Complex.norm_of_nonneg W.hL.le]
      linarith
    have hYf_eq : frame (M Y_use) = (W.L + s_rem) • dir (Real.pi / 3 - α_eff / 2) := by
      change rotC θ_rot (M Y_use - (W.L : ℂ)) = (W.L + s_rem) • dir (Real.pi / 3 - α_eff / 2)
      rw [hMY_eq, map_smul, hrot_dir]
      congr 2; dsimp [θ_rot]; rw [hβ0]; ring
    have hR_len : ‖r E - Y_use‖ + ‖Y_use - Y_use‖ ≤ rightLen := by
      rw [sub_self, norm_zero, add_zero]
      dsimp [rightLen]; rw [if_neg (not_le.mpr hFy)]
      have htri1 : ‖r E - Y_use‖ ≤ ‖r E - (W.L : ℂ)‖ + ‖(W.L : ℂ) - Y_use‖ := by
        have : r E - Y_use = (r E - (W.L : ℂ)) + ((W.L : ℂ) - Y_use) := by ring
        rw [this]; exact norm_add_le _ _
      have hLY : ‖(W.L : ℂ) - Y_use‖ = s_rem := by
        rw [show (W.L : ℂ) - Y_use = -(s_rem • dir (2 * W.v_lo - Real.pi / 3)) by
          rw [show Y_use = (W.L : ℂ) + s_rem • dir (2 * W.v_lo - Real.pi / 3) from rfl]; ring,
          norm_neg, norm_smul, Real.norm_of_nonneg hs_pos.le, dir_norm, mul_one]
      have htri2 : ‖r E - (W.L : ℂ)‖ ≤ ‖r F - r E‖ + ‖r F - (W.L : ℂ)‖ := by
        have : r E - (W.L : ℂ) = (r E - r F) + (r F - (W.L : ℂ)) := by ring
        rw [this, norm_sub_rev (r F) (r E)]; exact norm_add_le _ _
      have hFL : ‖r F - (W.L : ℂ)‖ = tF := by
        rw [hOnF.2, show (W.L : ℂ) - tF • dir (-(Real.pi / 6 - W.v_lo)) - (W.L : ℂ) =
          -(tF • dir (-(Real.pi / 6 - W.v_lo))) by ring, norm_neg, norm_smul,
          Real.norm_of_nonneg hOnF.1, dir_norm, mul_one]
      dsimp [s_rem] at hLY; linarith
    have hchain_le1 := hchain_of_right Y_use Y_use hR_len
    have hYf_le : -Real.sqrt 3 * (frame (M Y_use)).re + (frame (M Y_use)).im ≤ 0 := by
      rw [hYf_eq]; simp only [smul_re, smul_im, smul_eq_mul, dir_re, dir_im]
      have hid : -Real.sqrt 3 * Real.cos (Real.pi / 3 - α_eff / 2) + Real.sin (Real.pi / 3 - α_eff / 2) =
          -2 * Real.sin (α_eff / 2) := by
        rw [Real.cos_sub, Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
        have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        linear_combination -(Real.sin (α_eff / 2) / 2) * hsq3
      have hsn : 0 ≤ Real.sin (α_eff / 2) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hα_bounds.1]) (by linarith [hα_bounds.2, W.hv_lo_le, Real.pi_pos])
      have hmul : -Real.sqrt 3 * ((W.L + s_rem) * Real.cos (Real.pi / 3 - α_eff / 2)) +
          (W.L + s_rem) * Real.sin (Real.pi / 3 - α_eff / 2) =
          (W.L + s_rem) * (-2 * Real.sin (α_eff / 2)) := by linear_combination (W.L + s_rem) * hid
      nlinarith [W.hL]
    have hYf_re : 0 ≤ (frame (M Y_use)).re := by
      rw [hYf_eq]; simp only [smul_re, smul_eq_mul, dir_re]
      have := Real.cos_nonneg_of_mem_Icc (x := Real.pi / 3 - α_eff / 2)
        ⟨by linarith [hα_bounds.2, W.hv_lo_le, Real.pi_pos], by linarith [hα_bounds.1, Real.pi_pos]⟩
      nlinarith [W.hL]
    have hYf_im : 0 ≤ (frame (M Y_use)).im := by
      rw [hYf_eq]; simp only [smul_im, smul_eq_mul, dir_im]
      have := Real.sin_nonneg_of_nonneg_of_le_pi (x := Real.pi / 3 - α_eff / 2)
        (by linarith [hα_bounds.2, W.hv_lo_le, Real.pi_pos]) (by linarith [hα_bounds.1, Real.pi_pos])
      nlinarith [W.hL]
    have hYf_gt : 1 < ‖frame (M Y_use)‖ := by
      rw [hYf_eq, norm_smul, Real.norm_of_nonneg (by linarith [W.hL]), dir_norm, mul_one]; exact hfar_clamp
    have hgt := sector60_chain_gt_one hAf_le hYf_le hXf_Q2.1 hXf_Q2.2 hYf_re hYf_im hXf_gt hYf_gt
    linarith
  · -- Unclamped right side: Y_use ∈ wedgeSet W and F_use = F_eff!
    have hright_unclamped : ∃ Y_use : ℂ, Y_use ∈ wedgeSet W ∧ 1 < ‖Y_use‖ ∧
        ‖r E - Y_use‖ + ‖Y_use - F_eff‖ ≤ rightLen := by
      by_cases hyF : y ≤ F
      · have hFeq : F_eff = r F := by
          rw [show F_eff = (W.L : ℂ) - tF_eff • dir (-(Real.pi / 6 - W.v_lo)) from rfl,
            show tF_eff = tF by dsimp [tF_eff]; rw [if_pos hyF], ← hOnF.2]
        refine ⟨r y, ⟨W.hU_bot y, W.hU_top y, W.hV_top y, W.hV_bot y⟩, hy_far, ?_⟩
        dsimp [rightLen]; rw [if_pos hyF, hFeq, norm_sub_rev (r E) (r y), norm_sub_rev (r y) (r F)]
      · push Not at hyF
        have hle_tF : ‖r y - r F‖ ≤ tF := not_lt.mp fun hgt => hright_clamp ⟨hyF, hgt⟩
        have htF_eq : tF_eff = tF - ‖r y - r F‖ := by
          dsimp [tF_eff]; rw [if_neg (not_le.mpr hyF), max_eq_right (by linarith)]
        have hF_eq : F_eff = r F + ‖r y - r F‖ • dir (-(Real.pi / 6 - W.v_lo)) := by
          rw [show F_eff = (W.L : ℂ) - tF_eff • dir (-(Real.pi / 6 - W.v_lo)) from rfl, htF_eq, hOnF.2, sub_smul]; ring
        let Xr : ℂ := (W.L : ℂ) - r y
        have hXr_bot : 0 ≤ cross (dir (-(Real.pi / 6 - W.v_lo))) Xr := by
          dsimp [Xr]; rw [show (W.L : ℂ) - r y = -(r y - (W.L : ℂ)) by ring, cross_neg_right]
          linarith [W.hV_top y]
        have hfig7 := fig7_obtuse_dist (u_lo := Real.pi / 6 - W.v_lo) (tA := tF) W.hL.le
          (by linarith [W.hv_lo_le]) (by linarith [W.hv_lo0]) (by linarith [htFQV, htQV_le]) hXr_bot
        have hXrL : ‖Xr - (W.L : ℂ)‖ = ‖r y‖ := by
          dsimp [Xr]; rw [show (W.L : ℂ) - r y - (W.L : ℂ) = -r y by ring, norm_neg]
        have hXrd : ‖Xr - tF • dir (-(Real.pi / 6 - W.v_lo))‖ = ‖r y - r F‖ := by
          have : Xr - tF • dir (-(Real.pi / 6 - W.v_lo)) = -(r y - r F) := by
            rw [show Xr = (W.L : ℂ) - r y from rfl, hOnF.2]; ring
          rw [this, norm_neg]
        have hFbar : ‖(tF • dir (-(Real.pi / 6 - W.v_lo)) - ‖r y - r F‖ • dir (-(Real.pi / 6 - W.v_lo))) - (W.L : ℂ)‖ =
            ‖F_eff‖ := by
          have : (tF • dir (-(Real.pi / 6 - W.v_lo)) - ‖r y - r F‖ • dir (-(Real.pi / 6 - W.v_lo))) - (W.L : ℂ) =
              -F_eff := by
            rw [show F_eff = (W.L : ℂ) - tF_eff • dir (-(Real.pi / 6 - W.v_lo)) from rfl, htF_eq, sub_smul]; ring
          rw [this, norm_neg]
        rw [hXrL, hXrd, hFbar] at hfig7
        refine ⟨F_eff, hF_eff_mem, by linarith, ?_⟩
        rw [sub_self, norm_zero, add_zero]
        dsimp [rightLen]; rw [if_neg (not_le.mpr hyF)]
        have htri : ‖r E - F_eff‖ ≤ ‖r E - r F‖ + ‖r F - F_eff‖ := by
          have : r E - F_eff = (r E - r F) + (r F - F_eff) := by ring
          rw [this]; exact norm_add_le _ _
        have hFF : ‖r F - F_eff‖ = ‖r y - r F‖ := by
          rw [hF_eq, show r F - (r F + ‖r y - r F‖ • dir (-(Real.pi / 6 - W.v_lo))) =
            -(‖r y - r F‖ • dir (-(Real.pi / 6 - W.v_lo))) by ring, norm_neg, norm_smul,
            Real.norm_of_nonneg (norm_nonneg _), dir_norm, mul_one]
        rw [norm_sub_rev (r F) (r E)]; linarith
    obtain ⟨Y_use, hY_mem, hY_far, hR_len⟩ := hright_unclamped
    have hchain_le1 := hchain_of_right Y_use F_eff hR_len
    exact case24_unclamped_finish W.hL W.hu_lo0 W.hu_lo_le W.hv_lo0 W.hv_lo_le
      hα_bounds hβ_bounds hβ_le_α hY_mem.1 hY_mem.2.1 hY_mem.2.2.1 hY_far rfl
      hAf_le hXf_Q2 hXf_gt hchain_le1

lemma case24_contradiction {N : ℕ} {r : Fin (N + 1) → ℂ}
    (hgp : GenPos r) (hsimp : IsSimplePoly r) (hlen : polyLen r ≤ 1) (huncov : ¬ CoveredUnit r)
    (W : TwoWedgeBase r) (hcase : IsCase24 W) : False := by
  rcases hcase with ⟨A, B, QU, QV, E, F, tA, tB, tQU, tQV, tE, tF,
    hAB, hBQU, hQUE, hBQV, hQVE, hEF, htAQU, htFQV, hOnA, hOnB, hOnQU, hOnQV, hOnE, hOnF⟩
  obtain ⟨x, hxB, hx_far⟩ := exists_far_before_B hgp hsimp huncov W hAB hBQU htAQU hOnA hOnB hOnQU
  obtain ⟨y, hEy, hy_far⟩ := exists_far_after_Vbot hgp hsimp huncov W hQVE hEF htFQV hOnQV hOnE hOnF
  by_cases hαβ :
      Complex.arg ((W.L : ℂ) - (if y ≤ F then tF else max 0 (tF - ‖r y - r F‖)) • dir (-(Real.pi / 6 - W.v_lo))) ≤
      Complex.arg ((W.L : ℂ) - (if A ≤ x then tA else max 0 (tA - ‖r x - r A‖)) • dir (-W.u_lo))
  · exact case24_wlog_contradiction hlen W hAB hBQU hQUE hEF htAQU htFQV
      hOnA hOnB hOnQU hOnQV hOnE hOnF hxB hx_far hEy hy_far hαβ
  · push Not at hαβ
    let r' : Fin (N + 1) → ℂ := fun k => (W.L : ℂ) - r k.rev
    have hr'_eq : ∀ k, r' k = rotC Real.pi (r k.rev) + (W.L : ℂ) := fun k => by
      simp only [r', rotC_apply, Complex.exp_pi_mul_I]; ring
    have hlen' : polyLen r' ≤ 1 := by
      have h1 : polyLen (fun k => rotC Real.pi (r k.rev) + (W.L : ℂ)) = polyLen r := by
        rw [polyLen_of_rot_trans, polyLen_of_rev]
      have heq : r' = fun k => rotC Real.pi (r k.rev) + (W.L : ℂ) := funext hr'_eq
      rw [heq, h1]; exact hlen
    let W' := twoWedgeBase_rot180 W
    have hOnF' : OnUbot W' F.rev tF := ⟨hOnF.1, by
      show (W.L : ℂ) - r F.rev.rev = tF • dir (-(Real.pi / 6 - W.v_lo)); rw [Fin.rev_rev, hOnF.2]; ring⟩
    have hOnE' : OnUtop W' E.rev tE := ⟨hOnE.1, by
      show (W.L : ℂ) - r E.rev.rev = tE • dir (Real.pi / 6 - (Real.pi / 6 - W.v_lo))
      rw [Fin.rev_rev, hOnE.2, show Real.pi / 6 - (Real.pi / 6 - W.v_lo) = W.v_lo by ring]; ring⟩
    have hOnQV' : OnUbot W' QV.rev tQV := ⟨hOnQV.1, by
      show (W.L : ℂ) - r QV.rev.rev = tQV • dir (-(Real.pi / 6 - W.v_lo)); rw [Fin.rev_rev, hOnQV.2]; ring⟩
    have hOnQU' : OnVtop W' QU.rev tQU := ⟨hOnQU.1, by
      show (W.L : ℂ) - r QU.rev.rev = (W.L : ℂ) - tQU • dir (-(Real.pi / 6 - (Real.pi / 6 - W.u_lo)))
      rw [Fin.rev_rev, hOnQU.2, show -(Real.pi / 6 - (Real.pi / 6 - W.u_lo)) = -W.u_lo by ring]⟩
    have hOnB' : OnVbot W' B.rev tB := ⟨hOnB.1, by
      show (W.L : ℂ) - r B.rev.rev = (W.L : ℂ) - tB • dir (Real.pi / 6 - W.u_lo)
      rw [Fin.rev_rev, hOnB.2]⟩
    have hOnA' : OnVtop W' A.rev tA := ⟨hOnA.1, by
      show (W.L : ℂ) - r A.rev.rev = (W.L : ℂ) - tA • dir (-(Real.pi / 6 - (Real.pi / 6 - W.u_lo)))
      rw [Fin.rev_rev, hOnA.2, show -(Real.pi / 6 - (Real.pi / 6 - W.u_lo)) = -W.u_lo by ring]⟩
    have hx'_far : 1 < ‖r' y.rev - (W'.L : ℂ)‖ := by
      dsimp [r', W', twoWedgeBase_rot180]
      rw [Fin.rev_rev, show (W.L : ℂ) - r y - (W.L : ℂ) = -r y by ring, norm_neg]; exact hy_far
    have hy'_far : 1 < ‖r' x.rev‖ := by
      dsimp [r']; rw [Fin.rev_rev, show (W.L : ℂ) - r x = -(r x - (W.L : ℂ)) by ring, norm_neg]; exact hx_far
    have hnorm_yF : ‖r' y.rev - r' F.rev‖ = ‖r y - r F‖ := by
      dsimp [r']; rw [Fin.rev_rev, Fin.rev_rev, show ((W.L : ℂ) - r y) - ((W.L : ℂ) - r F) = -(r y - r F) by ring, norm_neg]
    have hnorm_xA : ‖r' x.rev - r' A.rev‖ = ‖r x - r A‖ := by
      dsimp [r']; rw [Fin.rev_rev, Fin.rev_rev, show ((W.L : ℂ) - r x) - ((W.L : ℂ) - r A) = -(r x - r A) by ring, norm_neg]
    have hαβ' :
        Complex.arg ((W'.L : ℂ) - (if x.rev ≤ A.rev then tA else max 0 (tA - ‖r' x.rev - r' A.rev‖)) •
          dir (-(Real.pi / 6 - W'.v_lo))) ≤
        Complex.arg ((W'.L : ℂ) - (if F.rev ≤ y.rev then tF else max 0 (tF - ‖r' y.rev - r' F.rev‖)) •
          dir (-W'.u_lo)) := by
      dsimp [W', twoWedgeBase_rot180]
      rw [hnorm_xA, hnorm_yF, show -(Real.pi / 6 - (Real.pi / 6 - W.u_lo)) = -W.u_lo by ring]
      have hiff1 : (x.rev ≤ A.rev) ↔ (A ≤ x) := Fin.rev_le_rev
      have hiff2 : (F.rev ≤ y.rev) ↔ (y ≤ F) := Fin.rev_le_rev
      simp only [hiff1, hiff2]
      exact hαβ.le
    exact case24_wlog_contradiction hlen' W'
      (Fin.rev_lt_rev.mpr hEF) (Fin.rev_lt_rev.mpr hQVE) (Fin.rev_le_rev.mpr hBQV) (Fin.rev_lt_rev.mpr hAB)
      htFQV htAQU hOnF' hOnE' hOnQV' hOnQU' hOnB' hOnA'
      (Fin.rev_le_rev.mpr hEy) hx'_far (Fin.rev_le_rev.mpr hxB) hy'_far hαβ'

/- Section 5D: Final assembly -/

theorem simple_poly_cover (N : ℕ) (r : Fin (N + 1) → ℂ) (hN : 2 ≤ N)
    (hgp : GenPos r) (hsimp : IsSimplePoly r) (hlen : polyLen r ≤ 1) :
    CoveredUnit r := by
  by_contra huncov
  obtain ⟨r', W, hgp', hsimp', hlen', huncov', hcases⟩ :=
    extract_two_wedge_case hN hgp hsimp hlen huncov
  rcases hcases with h1 | h3 | h24
  · exact case1_contradiction hgp' hsimp' hlen' huncov' W h1
  · exact case3_contradiction hgp' hsimp' hlen' huncov' W h3
  · exact case24_contradiction hgp' hsimp' hlen' huncov' W h24

end MoserWormUpper

theorem OMA.solution : type_of% @MoserWorm.convex_mosers_worm_problem_upper_bound := by
  refine ⟨MoserWormUpper.sectorR2 MoserWormUpper.R0, ?_,
    MoserWormUpper.sectorR2_convex MoserWormUpper.R0, MoserWormUpper.volume_sectorR2_R0⟩
  apply MoserWormUpper.worm_covered_of_simple_poly_cover
  intro N r hN hgp hsimp hlen
  obtain ⟨θ, v, hcov⟩ := MoserWormUpper.simple_poly_cover N r hN hgp hsimp hlen
  exact ⟨θ, v, false, fun k => by simpa using hcov k⟩
