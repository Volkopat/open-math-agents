import OMAReductions.R_Bloch_blochConstant_upper_bound_R1

/-!
# Ahlfors-Grunsky Upper Bound for Bloch's Constant (H1)

Self-contained proof of `OMA.R_Bloch_blochConstant_upper_bound_R1.H1` following
L. V. Ahlfors and H. Grunsky, Math. Z. 42 (1937), 671-673.
-/

/- ==================== Bloch_Part1.lean ==================== -/
/-
# Ahlfors-Grunsky Proof — Part 1: Geometry, Hyperbolic/Euclidean Triangles, Reflections, Lattice
-/

namespace BlochAG

open Complex Metric Set Filter Topology Real

noncomputable section

/- ## 1. Basic Constants -/

def ω : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

def R : ℝ := 1 / Real.sqrt (1 + Real.sqrt 3)

def cAG : ℝ :=
  Real.Gamma (1 / 3) * Real.Gamma (11 / 12) / (Real.Gamma (1 / 4) * Real.sqrt (1 + Real.sqrt 3))

lemma sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

lemma sq_sqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma one_add_sqrt3_pos : (0 : ℝ) < 1 + Real.sqrt 3 := by linarith [sqrt3_pos]

lemma R_pos : 0 < R := by
  unfold R
  exact one_div_pos.mpr (Real.sqrt_pos.mpr one_add_sqrt3_pos)

lemma R_ne_zero : R ≠ 0 := R_pos.ne'

lemma R_sq : R ^ 2 = (Real.sqrt 3 - 1) / 2 := by
  unfold R
  rw [div_pow, one_pow, Real.sq_sqrt one_add_sqrt3_pos.le]
  have h1 : (1 + Real.sqrt 3 : ℝ) ≠ 0 := one_add_sqrt3_pos.ne'
  field_simp
  nlinarith [sq_sqrt3]

lemma R_sq_mul : (1 + Real.sqrt 3) * R ^ 2 = 1 := by
  rw [R_sq]; nlinarith [sq_sqrt3]

lemma R_lt_one : R < 1 := by
  have h : R ^ 2 < 1 ^ 2 := by
    rw [R_sq, one_pow]
    have h3 : Real.sqrt 3 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  nlinarith [R_pos]

lemma cAG_pos : 0 < cAG := by
  unfold cAG
  have h1 : (0 : ℝ) < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : (0 : ℝ) < Real.Gamma (11 / 12) := Real.Gamma_pos_of_pos (by norm_num)
  have h3 : (0 : ℝ) < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have h4 : (0 : ℝ) < Real.sqrt (1 + Real.sqrt 3) := Real.sqrt_pos.mpr one_add_sqrt3_pos
  positivity

lemma ω_re : ω.re = -1 / 2 := rfl
lemma ω_im : ω.im = Real.sqrt 3 / 2 := rfl

lemma ω_sq : ω ^ 2 = ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩ := by
  apply Complex.ext
  · simp [ω, sq]; nlinarith [sq_sqrt3]
  · simp [ω, sq]; ring

lemma ω_cube : ω ^ 3 = 1 := by
  rw [pow_succ, ω_sq]
  apply Complex.ext
  · simp [ω]; nlinarith [sq_sqrt3]
  · simp [ω]; ring

lemma ω_sq_add_ω_add_one : ω ^ 2 + ω + 1 = 0 := by
  rw [ω_sq]; apply Complex.ext
  · simp [ω]
  · simp [ω]

lemma star_ω : starRingEnd ℂ ω = ω ^ 2 := by
  rw [ω_sq]; apply Complex.ext <;> simp [ω]

lemma star_ω_sq : starRingEnd ℂ (ω ^ 2) = ω := by
  rw [← star_ω, RingHomCompTriple.comp_apply, RingHom.id_apply]

lemma norm_ω : ‖ω‖ = 1 := by
  have hsq : ‖ω‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [ω_re, ω_im]
    nlinarith [sq_sqrt3]
  nlinarith [norm_nonneg ω]

lemma ω_ne_zero : ω ≠ 0 := by
  intro h; have := norm_ω; rw [h, norm_zero] at this; norm_num at this

lemma norm_ω_pow (k : ℕ) : ‖ω ^ k‖ = 1 := by
  rw [norm_pow, norm_ω, one_pow]

lemma ω_eq_exp : ω = Complex.exp (↑(2 * Real.pi / 3) * I) := by
  rw [Complex.exp_mul_I]
  apply Complex.ext
  · simp only [ω_re, add_re, Complex.cos_ofReal_re, mul_re, Complex.sin_ofReal_re, I_re, mul_zero,
      Complex.sin_ofReal_im, I_im, mul_one, sub_self, add_zero]
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    ring
  · simp only [ω_im, add_im, Complex.cos_ofReal_im, mul_im, Complex.sin_ofReal_re, I_im, mul_one,
      Complex.sin_ofReal_im, I_re, mul_zero, add_zero, zero_add]
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
      Real.sin_pi_div_three]

lemma one_add_ω : 1 + ω = ⟨1 / 2, Real.sqrt 3 / 2⟩ := by
  apply Complex.ext
  · simp [ω]; ring
  · simp [ω]

lemma norm_one_add_ω : ‖1 + ω‖ = 1 := by
  have h : 1 + ω = -(ω ^ 2) := by linear_combination ω_sq_add_ω_add_one
  rw [h, norm_neg, norm_pow, norm_ω, one_pow]

/- ## 2. Pseudo-Hyperbolic Distance on the Unit Disk -/

def hypDist (z w : ℂ) : ℝ := ‖(z - w) / (1 - starRingEnd ℂ w * z)‖

lemma one_sub_conj_mul_ne_zero {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    1 - starRingEnd ℂ w * z ≠ 0 := by
  intro h
  have h1 : starRingEnd ℂ w * z = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖starRingEnd ℂ w * z‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, RCLike.norm_conj] at h2
  nlinarith [norm_nonneg z, norm_nonneg w]

lemma normSq_one_sub_conj_mul_sub (z w : ℂ) :
    Complex.normSq (1 - starRingEnd ℂ w * z) - Complex.normSq (z - w) =
      (1 - Complex.normSq z) * (1 - Complex.normSq w) := by
  simp only [Complex.normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
  ring

lemma hypDist_nonneg (z w : ℂ) : 0 ≤ hypDist z w := norm_nonneg _

lemma hypDist_self (z : ℂ) : hypDist z z = 0 := by simp [hypDist]

lemma hypDist_comm (z w : ℂ) : hypDist z w = hypDist w z := by
  unfold hypDist
  rw [norm_div, norm_div]
  congr 1
  · exact norm_sub_rev z w
  · have h : starRingEnd ℂ (1 - starRingEnd ℂ w * z) = 1 - starRingEnd ℂ z * w := by
      simp [mul_comm]
    rw [← h, RCLike.norm_conj]

lemma hypDist_lt_one {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) : hypDist z w < 1 := by
  unfold hypDist
  rw [norm_div, div_lt_one (norm_pos_iff.mpr (one_sub_conj_mul_ne_zero hz hw))]
  have hsq : Complex.normSq (z - w) < Complex.normSq (1 - starRingEnd ℂ w * z) := by
    have hdiff := normSq_one_sub_conj_mul_sub z w
    have hz2 : Complex.normSq z < 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg z]
    have hw2 : Complex.normSq w < 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg w]
    nlinarith
  have h1 : ‖z - w‖ ^ 2 < ‖1 - starRingEnd ℂ w * z‖ ^ 2 := by
    simpa [Complex.sq_norm] using hsq
  nlinarith [norm_nonneg (z - w), norm_nonneg (1 - starRingEnd ℂ w * z)]

lemma hypDist_zero_right (z : ℂ) : hypDist z 0 = ‖z‖ := by
  simp [hypDist]

lemma hypDist_zero_left (z : ℂ) : hypDist 0 z = ‖z‖ := by
  rw [hypDist_comm, hypDist_zero_right]

lemma hypDist_eq_zero_iff {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    hypDist z w = 0 ↔ z = w := by
  unfold hypDist
  rw [norm_eq_zero, div_eq_zero_iff, sub_eq_zero]
  exact ⟨fun h => h.resolve_right (one_sub_conj_mul_ne_zero hz hw), Or.inl⟩

/-- Möbius automorphism of the unit disk sending `a` to `0`. -/
def mobiusToZero (a z : ℂ) : ℂ := (z - a) / (1 - starRingEnd ℂ a * z)

lemma mobiusToZero_mem_ball {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖mobiusToZero a z‖ < 1 := hypDist_lt_one hz ha

lemma mobiusToZero_inv {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    mobiusToZero (-a) (mobiusToZero a z) = z := by
  unfold mobiusToZero
  have h1 : 1 - starRingEnd ℂ a * z ≠ 0 := one_sub_conj_mul_ne_zero hz ha
  have h2 : 1 - starRingEnd ℂ (-a) * ((z - a) / (1 - starRingEnd ℂ a * z)) ≠ 0 := by
    have hma : ‖-a‖ < 1 := by simpa using ha
    exact one_sub_conj_mul_ne_zero (mobiusToZero_mem_ball ha hz) hma
  have h3 : (1 : ℝ) - ‖a‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg a]
  have h4 : (1 : ℂ) - starRingEnd ℂ a * a ≠ 0 := by
    rw [Complex.conj_mul']
    exact_mod_cast h3
  rw [div_eq_iff h2]
  simp only [map_neg, sub_neg_eq_add]
  have h5 : (z - a) / (1 - starRingEnd ℂ a * z) + a =
      ((1 - starRingEnd ℂ a * a) * z) / (1 - starRingEnd ℂ a * z) := by
    rw [div_add' _ _ _ h1]; congr 1; ring
  have h6 : 1 - -(starRingEnd ℂ a) * ((z - a) / (1 - starRingEnd ℂ a * z)) =
      (1 - starRingEnd ℂ a * a) / (1 - starRingEnd ℂ a * z) := by
    rw [neg_mul, sub_neg_eq_add, mul_div_assoc', one_add_div h1]; congr 1; ring
  rw [h5, h6]; ring

lemma hypDist_mobiusToZero {a z w : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    hypDist (mobiusToZero a z) (mobiusToZero a w) = hypDist z w := by
  unfold hypDist mobiusToZero
  have h1 : 1 - starRingEnd ℂ a * z ≠ 0 := one_sub_conj_mul_ne_zero hz ha
  have h2 : 1 - starRingEnd ℂ a * w ≠ 0 := one_sub_conj_mul_ne_zero hw ha
  have h2c : 1 - a * starRingEnd ℂ w ≠ 0 := by
    have : starRingEnd ℂ (1 - starRingEnd ℂ a * w) = 1 - a * starRingEnd ℂ w := by
      simp [mul_comm]
    rw [← this]; exact (map_ne_zero _).mpr h2
  have h3 : (1 : ℂ) - starRingEnd ℂ a * a ≠ 0 := by
    rw [Complex.conj_mul']
    exact_mod_cast (by nlinarith [norm_nonneg a] : (1 : ℝ) - ‖a‖ ^ 2 ≠ 0)
  have hnum : (z - a) / (1 - starRingEnd ℂ a * z) - (w - a) / (1 - starRingEnd ℂ a * w) =
      (1 - starRingEnd ℂ a * a) * (z - w) /
        ((1 - starRingEnd ℂ a * z) * (1 - starRingEnd ℂ a * w)) := by
    rw [div_sub_div _ _ h1 h2]; congr 1; ring
  have hden : 1 - starRingEnd ℂ ((w - a) / (1 - starRingEnd ℂ a * w)) *
        ((z - a) / (1 - starRingEnd ℂ a * z)) =
      (1 - starRingEnd ℂ a * a) * (1 - starRingEnd ℂ w * z) /
        ((1 - a * starRingEnd ℂ w) * (1 - starRingEnd ℂ a * z)) := by
    simp only [map_div₀, map_sub, map_one, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    have h2c' : 1 - a * starRingEnd ℂ w ≠ 0 := h2c
    rw [div_mul_div_comm, one_sub_div (mul_ne_zero h2c' h1)]
    congr 1; ring
  rw [hnum, hden, norm_div, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul]
  have hnorm_eq : ‖1 - a * starRingEnd ℂ w‖ = ‖1 - starRingEnd ℂ a * w‖ := by
    have : starRingEnd ℂ (1 - starRingEnd ℂ a * w) = 1 - a * starRingEnd ℂ w := by
      simp [mul_comm]
    rw [← this, RCLike.norm_conj]
  rw [hnorm_eq, norm_div]
  have hn1 : ‖1 - starRingEnd ℂ a * z‖ ≠ 0 := norm_ne_zero_iff.mpr h1
  have hn2 : ‖1 - starRingEnd ℂ a * w‖ ≠ 0 := norm_ne_zero_iff.mpr h2
  have hn3 : ‖1 - starRingEnd ℂ a * a‖ ≠ 0 := norm_ne_zero_iff.mpr h3
  have hn4 : ‖1 - starRingEnd ℂ w * z‖ ≠ 0 := norm_ne_zero_iff.mpr (one_sub_conj_mul_ne_zero hz hw)
  field_simp

lemma hypDist_triangle_zero {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    hypDist z w ≤ ‖z‖ + ‖w‖ := by
  have h1 : 1 - starRingEnd ℂ w * z ≠ 0 := one_sub_conj_mul_ne_zero hz hw
  have hns : Complex.normSq (1 - starRingEnd ℂ w * z) =
      Complex.normSq (z - w) + (1 - Complex.normSq z) * (1 - Complex.normSq w) := by
    linarith [normSq_one_sub_conj_mul_sub z w]
  have ha : 0 ≤ ‖z‖ := norm_nonneg z
  have hb : 0 ≤ ‖w‖ := norm_nonneg w
  have ht : ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
  have ht2 : Complex.normSq (z - w) ≤ (‖z‖ + ‖w‖) ^ 2 := by
    rw [← Complex.sq_norm]; nlinarith [norm_nonneg (z - w)]
  have hpos : 0 < (1 - Complex.normSq z) * (1 - Complex.normSq w) := by
    have hz2 : Complex.normSq z < 1 := by rw [← Complex.sq_norm]; nlinarith
    have hw2 : Complex.normSq w < 1 := by rw [← Complex.sq_norm]; nlinarith
    nlinarith
  have hfrac : Complex.normSq (z - w) / Complex.normSq (1 - starRingEnd ℂ w * z) ≤
      (‖z‖ + ‖w‖) ^ 2 / (1 + ‖z‖ * ‖w‖) ^ 2 := by
    have hd1 : 0 < Complex.normSq (1 - starRingEnd ℂ w * z) := Complex.normSq_pos.mpr h1
    have hd2 : 0 < (1 + ‖z‖ * ‖w‖) ^ 2 := by positivity
    rw [div_le_div_iff₀ hd1 hd2, hns]
    have hkey : (1 + ‖z‖ * ‖w‖) ^ 2 =
        (‖z‖ + ‖w‖) ^ 2 + (1 - Complex.normSq z) * (1 - Complex.normSq w) := by
      rw [← Complex.sq_norm z, ← Complex.sq_norm w]; ring
    rw [hkey]
    nlinarith
  have hle1 : (‖z‖ + ‖w‖) ^ 2 / (1 + ‖z‖ * ‖w‖) ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 := by
    have hge : (1 : ℝ) ≤ (1 + ‖z‖ * ‖w‖) ^ 2 := by nlinarith [mul_nonneg ha hb]
    exact div_le_self (by positivity) hge
  have hsq : hypDist z w ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 := by
    unfold hypDist
    rw [norm_div, div_pow, Complex.sq_norm, Complex.sq_norm]
    exact hfrac.trans hle1
  nlinarith [hypDist_nonneg z w]

lemma hypDist_triangle {z u w : ℂ} (hz : ‖z‖ < 1) (hu : ‖u‖ < 1) (hw : ‖w‖ < 1) :
    hypDist z w ≤ hypDist z u + hypDist u w := by
  rw [← hypDist_mobiusToZero hu hz hw]
  have hz' := mobiusToZero_mem_ball hu hz
  have hw' := mobiusToZero_mem_ball hu hw
  calc hypDist (mobiusToZero u z) (mobiusToZero u w)
      ≤ ‖mobiusToZero u z‖ + ‖mobiusToZero u w‖ := hypDist_triangle_zero hz' hw'
    _ = hypDist z u + hypDist w u := rfl
    _ = hypDist z u + hypDist u w := by rw [hypDist_comm w u]

def hypBall (z₀ : ℂ) (ρ : ℝ) : Set ℂ := {z : ℂ | ‖z‖ < 1 ∧ hypDist z z₀ < ρ}

lemma mem_hypBall_iff {z₀ z : ℂ} {ρ : ℝ} :
    z ∈ hypBall z₀ ρ ↔ ‖z‖ < 1 ∧ hypDist z z₀ < ρ := Iff.rfl

lemma hypBall_subset_ball (z₀ : ℂ) (ρ : ℝ) : hypBall z₀ ρ ⊆ ball 0 1 := fun _ h => by
  simpa [Metric.mem_ball, dist_zero_right] using h.1

lemma self_mem_hypBall {z₀ : ℂ} {ρ : ℝ} (hz₀ : ‖z₀‖ < 1) (hρ : 0 < ρ) :
    z₀ ∈ hypBall z₀ ρ := ⟨hz₀, by rw [hypDist_self]; exact hρ⟩

lemma isOpen_hypBall {z₀ : ℂ} {ρ : ℝ} (hz₀ : ‖z₀‖ < 1) : IsOpen (hypBall z₀ ρ) := by
  have hcont : ContinuousOn (fun z => hypDist z z₀) (ball 0 1) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
    refine ContinuousAt.continuousWithinAt ?_
    unfold hypDist
    exact (((continuousAt_id.sub continuousAt_const).div
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
      (one_sub_conj_mul_ne_zero hz1 hz₀)).norm)
  have h1 : hypBall z₀ ρ = ball (0 : ℂ) 1 ∩ (fun z => hypDist z z₀) ⁻¹' Iio ρ := by
    ext z; simp [hypBall, Metric.mem_ball, dist_zero_right]
  rw [h1]
  exact hcont.isOpen_inter_preimage isOpen_ball isOpen_Iio

lemma isPreconnected_hypBall {z₀ : ℂ} {ρ : ℝ} (hz₀ : ‖z₀‖ < 1) (_hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    IsPreconnected (hypBall z₀ ρ) := by
  have himg : hypBall z₀ ρ = mobiusToZero (-z₀) '' ball 0 ρ := by
    ext z
    constructor
    · rintro ⟨hz1, hdist⟩
      refine ⟨mobiusToZero z₀ z, ?_, mobiusToZero_inv hz₀ hz1⟩
      simpa [Metric.mem_ball, dist_zero_right, mobiusToZero, hypDist] using hdist
    · rintro ⟨w, hw, rfl⟩
      have hw1 : ‖w‖ < 1 := lt_of_lt_of_le (by simpa [Metric.mem_ball, dist_zero_right] using hw) hρ1
      have hm : ‖-z₀‖ < 1 := by simpa using hz₀
      refine ⟨mobiusToZero_mem_ball hm hw1, ?_⟩
      have hinv : mobiusToZero z₀ (mobiusToZero (-z₀) w) = w := by
        simpa [neg_neg] using mobiusToZero_inv hm hw1
      have : hypDist (mobiusToZero (-z₀) w) z₀ = ‖w‖ := by
        unfold hypDist; change ‖mobiusToZero z₀ (mobiusToZero (-z₀) w)‖ = ‖w‖; rw [hinv]
      rw [this]
      simpa [Metric.mem_ball, dist_zero_right] using hw
  rw [himg]
  have hcont : ContinuousOn (mobiusToZero (-z₀)) (ball 0 ρ) := by
    intro w hw
    have hw1 : ‖w‖ < 1 := lt_of_lt_of_le (by simpa [Metric.mem_ball, dist_zero_right] using hw) hρ1
    have hm : ‖-z₀‖ < 1 := by simpa using hz₀
    exact ((continuousAt_id.sub continuousAt_const).div
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
      (one_sub_conj_mul_ne_zero hw1 hm)).continuousWithinAt
  exact (convex_ball (0 : ℂ) ρ).isPreconnected.image _ hcont

lemma continuousOn_hypDist :
    ContinuousOn (fun p : ℂ × ℂ => hypDist p.1 p.2) (ball 0 1 ×ˢ ball 0 1) := by
  intro ⟨z, w⟩ ⟨hz, hw⟩
  have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  have hw1 : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
  refine ContinuousAt.continuousWithinAt ?_
  unfold hypDist
  have hnum : ContinuousAt (fun p : ℂ × ℂ => p.1 - p.2) (z, w) :=
    continuous_fst.continuousAt.sub continuous_snd.continuousAt
  have hden : ContinuousAt (fun p : ℂ × ℂ => (1 : ℂ) - starRingEnd ℂ p.2 * p.1) (z, w) :=
    continuousAt_const.sub ((Complex.continuous_conj.comp continuous_snd).continuousAt.mul
      continuous_fst.continuousAt)
  exact (hnum.div hden (one_sub_conj_mul_ne_zero hz1 hw1)).norm

/- ## 3. Hyperbolic Equilateral Triangle `Δ₁` and Reflections `r_j` -/

/-- Circle center `a₀` of the geodesic side between `R` and `R * ω`. -/
def a0 : ℂ := (((2 + Real.sqrt 3) * R : ℝ) : ℂ) * (1 + ω)

def sideCenter (j : Fin 3) : ℂ := ω ^ (j : ℕ) * a0

lemma norm_a0 : ‖a0‖ = (2 + Real.sqrt 3) * R := by
  unfold a0
  rw [norm_mul, Complex.norm_real, norm_one_add_ω, mul_one, Real.norm_of_nonneg]
  have := R_pos; have := sqrt3_pos; positivity

lemma norm_sideCenter (j : Fin 3) : ‖sideCenter j‖ = (2 + Real.sqrt 3) * R := by
  unfold sideCenter
  rw [norm_mul, norm_ω_pow, one_mul, norm_a0]

lemma norm_a0_sq : ‖a0‖ ^ 2 = (2 + Real.sqrt 3) ^ 2 * ((Real.sqrt 3 - 1) / 2) := by
  rw [norm_a0, mul_pow, R_sq]

lemma one_lt_norm_a0_sq : 1 < ‖a0‖ ^ 2 := by
  rw [norm_a0_sq]
  nlinarith [sq_sqrt3, sqrt3_pos]

lemma one_lt_norm_sideCenter (j : Fin 3) : 1 < ‖sideCenter j‖ := by
  have h : 1 < ‖sideCenter j‖ ^ 2 := by
    rw [norm_sideCenter, ← norm_a0]; exact one_lt_norm_a0_sq
  nlinarith [norm_nonneg (sideCenter j)]

lemma sideCenter_sq_sub_one_pos (j : Fin 3) : 0 < ‖sideCenter j‖ ^ 2 - 1 := by
  have := one_lt_norm_sideCenter j
  nlinarith [norm_nonneg (sideCenter j)]

/-- Hyperbolic reflection across side `j` of `Δ₁`. -/
def hypRefl (j : Fin 3) (z : ℂ) : ℂ :=
  (sideCenter j * starRingEnd ℂ z - 1) / (starRingEnd ℂ z - starRingEnd ℂ (sideCenter j))

lemma conj_sub_conj_sideCenter_ne_zero (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) :
    starRingEnd ℂ z - starRingEnd ℂ (sideCenter j) ≠ 0 := by
  intro h
  have h1 : starRingEnd ℂ z = starRingEnd ℂ (sideCenter j) := sub_eq_zero.mp h
  have h2 : ‖starRingEnd ℂ z‖ = ‖starRingEnd ℂ (sideCenter j)‖ := congrArg norm h1
  rw [RCLike.norm_conj, RCLike.norm_conj] at h2
  linarith [one_lt_norm_sideCenter j]

lemma normSq_sub_sideCenter_iff (j : Fin 3) (z : ℂ) :
    ‖z - sideCenter j‖ ^ 2 - (‖sideCenter j‖ ^ 2 - 1) =
      ‖z‖ ^ 2 - 2 * (z * starRingEnd ℂ (sideCenter j)).re + 1 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, sub_re, sub_im, mul_re, conj_re, conj_im]
  ring

lemma hypRefl_mem_ball (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) : ‖hypRefl j z‖ < 1 := by
  unfold hypRefl
  have hden := conj_sub_conj_sideCenter_ne_zero j hz
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hden)]
  have hdiff : Complex.normSq (starRingEnd ℂ z - starRingEnd ℂ (sideCenter j)) -
      Complex.normSq (sideCenter j * starRingEnd ℂ z - 1) =
      (Complex.normSq (sideCenter j) - 1) * (1 - Complex.normSq z) := by
    simp only [Complex.normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
    ring
  have h1 : 0 < Complex.normSq (sideCenter j) - 1 := by
    rw [← Complex.sq_norm]; exact sideCenter_sq_sub_one_pos j
  have h2 : 0 < 1 - Complex.normSq z := by
    rw [← Complex.sq_norm]; nlinarith [norm_nonneg z]
  have hsq : ‖sideCenter j * starRingEnd ℂ z - 1‖ ^ 2 <
      ‖starRingEnd ℂ z - starRingEnd ℂ (sideCenter j)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]; nlinarith
  nlinarith [norm_nonneg (sideCenter j * starRingEnd ℂ z - 1),
    norm_nonneg (starRingEnd ℂ z - starRingEnd ℂ (sideCenter j))]

lemma hypRefl_invol (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) : hypRefl j (hypRefl j z) = z := by
  have h1 : starRingEnd ℂ z - starRingEnd ℂ (sideCenter j) ≠ 0 :=
    conj_sub_conj_sideCenter_ne_zero j hz
  have h1c : z - sideCenter j ≠ 0 := by
    intro h; apply h1
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  have h2 : starRingEnd ℂ (hypRefl j z) - starRingEnd ℂ (sideCenter j) ≠ 0 :=
    conj_sub_conj_sideCenter_ne_zero j (hypRefl_mem_ball j hz)
  have ha1 : sideCenter j * starRingEnd ℂ (sideCenter j) - 1 ≠ 0 := by
    rw [Complex.mul_conj, ← Complex.sq_norm]
    exact_mod_cast (sideCenter_sq_sub_one_pos j).ne'
  unfold hypRefl at h2 ⊢
  simp only [map_div₀, map_sub, map_mul, map_one, RingHomCompTriple.comp_apply,
    RingHom.id_apply] at h2 ⊢
  rw [div_eq_iff h2]
  have hnum : sideCenter j * ((starRingEnd ℂ (sideCenter j) * z - 1) / (z - sideCenter j)) - 1 =
      (sideCenter j * starRingEnd ℂ (sideCenter j) - 1) * z / (z - sideCenter j) := by
    rw [mul_div_assoc', div_sub_one h1c]; congr 1; ring
  have hden : (starRingEnd ℂ (sideCenter j) * z - 1) / (z - sideCenter j) -
      starRingEnd ℂ (sideCenter j) =
      (sideCenter j * starRingEnd ℂ (sideCenter j) - 1) / (z - sideCenter j) := by
    rw [div_sub' h1c]; congr 1; ring
  rw [hnum, hden]; ring

lemma hypRefl_fixed_iff (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) :
    hypRefl j z = z ↔ ‖z - sideCenter j‖ ^ 2 = ‖sideCenter j‖ ^ 2 - 1 := by
  have hden := conj_sub_conj_sideCenter_ne_zero j hz
  unfold hypRefl
  rw [div_eq_iff hden]
  have h1 : sideCenter j * starRingEnd ℂ z - 1 = z * (starRingEnd ℂ z - starRingEnd ℂ (sideCenter j)) ↔
      (Complex.normSq z - 2 * (z * starRingEnd ℂ (sideCenter j)).re + 1 : ℂ) = 0 := by
    have hre : 2 * ((z * starRingEnd ℂ (sideCenter j)).re : ℂ) =
        z * starRingEnd ℂ (sideCenter j) + sideCenter j * starRingEnd ℂ z := by
      have := Complex.add_conj (z * starRingEnd ℂ (sideCenter j))
      simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply] at this
      rw [Complex.ofReal_mul, Complex.ofReal_ofNat] at this
      linear_combination -this
    have hns : ((Complex.normSq z : ℝ) : ℂ) = z * starRingEnd ℂ z := by
      rw [Complex.mul_conj]
    rw [hre, hns]
    constructor <;> intro h <;> linear_combination -h
  rw [h1]
  have h2 : ((Complex.normSq z - 2 * (z * starRingEnd ℂ (sideCenter j)).re + 1 : ℝ) : ℂ) =
      (Complex.normSq z : ℂ) - 2 * ((z * starRingEnd ℂ (sideCenter j)).re : ℂ) + 1 := by
    push_cast; ring
  rw [← h2, Complex.ofReal_eq_zero, ← Complex.sq_norm, ← normSq_sub_sideCenter_iff, sub_eq_zero]

lemma hypRefl_side_sign (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖hypRefl j z - sideCenter j‖ ^ 2 - (‖sideCenter j‖ ^ 2 - 1) =
      -((‖sideCenter j‖ ^ 2 - 1) / ‖z - sideCenter j‖ ^ 2) *
        (‖z - sideCenter j‖ ^ 2 - (‖sideCenter j‖ ^ 2 - 1)) := by
  have hden := conj_sub_conj_sideCenter_ne_zero j hz
  have hden' : z - sideCenter j ≠ 0 := by
    intro h; apply hden; have := congrArg (starRingEnd ℂ) h; simpa using this
  have hsub : hypRefl j z - sideCenter j =
      ((‖sideCenter j‖ ^ 2 - 1 : ℝ) : ℂ) / (starRingEnd ℂ z - starRingEnd ℂ (sideCenter j)) := by
    unfold hypRefl
    rw [div_sub' hden]
    congr 1
    have hns : ((‖sideCenter j‖ : ℂ) ^ 2) = sideCenter j * starRingEnd ℂ (sideCenter j) := by
      rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.mul_conj]
    push_cast; rw [hns]; ring
  rw [hsub, norm_div, Complex.norm_real, Real.norm_of_nonneg (sideCenter_sq_sub_one_pos j).le]
  have hn : ‖starRingEnd ℂ z - starRingEnd ℂ (sideCenter j)‖ = ‖z - sideCenter j‖ := by
    have : starRingEnd ℂ (z - sideCenter j) = starRingEnd ℂ z - starRingEnd ℂ (sideCenter j) :=
      map_sub _ _ _
    rw [← this, RCLike.norm_conj]
  rw [hn, div_pow]
  have hne : ‖z - sideCenter j‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hden')
  field_simp; ring

lemma hypDist_hypRefl (j : Fin 3) {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    hypDist (hypRefl j z) (hypRefl j w) = hypDist z w := by
  unfold hypDist hypRefl
  set a := sideCenter j
  have hz' : starRingEnd ℂ z - starRingEnd ℂ a ≠ 0 := conj_sub_conj_sideCenter_ne_zero j hz
  have hw' : starRingEnd ℂ w - starRingEnd ℂ a ≠ 0 := conj_sub_conj_sideCenter_ne_zero j hw
  have hwc : w - a ≠ 0 := by
    intro h; apply hw'; have := congrArg (starRingEnd ℂ) h; simpa using this
  have ha1 : (a * starRingEnd ℂ a - 1 : ℂ) ≠ 0 := by
    rw [Complex.mul_conj, ← Complex.sq_norm]
    exact_mod_cast (sideCenter_sq_sub_one_pos j).ne'
  have hnum : (a * starRingEnd ℂ z - 1) / (starRingEnd ℂ z - starRingEnd ℂ a) -
      (a * starRingEnd ℂ w - 1) / (starRingEnd ℂ w - starRingEnd ℂ a) =
      -(a * starRingEnd ℂ a - 1) * (starRingEnd ℂ z - starRingEnd ℂ w) /
        ((starRingEnd ℂ z - starRingEnd ℂ a) * (starRingEnd ℂ w - starRingEnd ℂ a)) := by
    rw [div_sub_div _ _ hz' hw']; congr 1; ring
  have hden : 1 - starRingEnd ℂ ((a * starRingEnd ℂ w - 1) / (starRingEnd ℂ w - starRingEnd ℂ a)) *
      ((a * starRingEnd ℂ z - 1) / (starRingEnd ℂ z - starRingEnd ℂ a)) =
      (a * starRingEnd ℂ a - 1) * (1 - w * starRingEnd ℂ z) /
        ((w - a) * (starRingEnd ℂ z - starRingEnd ℂ a)) := by
    simp only [map_div₀, map_sub, map_mul, map_one, RingHomCompTriple.comp_apply, RingHom.id_apply]
    rw [div_mul_div_comm, one_sub_div (mul_ne_zero hwc hz')]; congr 1; ring
  rw [hnum, hden]
  rw [norm_div, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_neg]
  have hnw : ‖starRingEnd ℂ w - starRingEnd ℂ a‖ = ‖w - a‖ := by
    rw [← map_sub, RCLike.norm_conj]
  have hnzw : ‖starRingEnd ℂ z - starRingEnd ℂ w‖ = ‖z - w‖ := by
    rw [← map_sub, RCLike.norm_conj]
  have hn1 : ‖1 - w * starRingEnd ℂ z‖ = ‖1 - starRingEnd ℂ w * z‖ := by
    have : starRingEnd ℂ (1 - starRingEnd ℂ w * z) = 1 - w * starRingEnd ℂ z := by simp
    rw [← this, RCLike.norm_conj]
  rw [hnw, hnzw, hn1, norm_div]
  have hna : ‖a * starRingEnd ℂ a - 1‖ ≠ 0 := norm_ne_zero_iff.mpr ha1
  have hnz' : ‖starRingEnd ℂ z - starRingEnd ℂ a‖ ≠ 0 := norm_ne_zero_iff.mpr hz'
  have hnw' : ‖w - a‖ ≠ 0 := norm_ne_zero_iff.mpr hwc
  have hn1' : ‖1 - starRingEnd ℂ w * z‖ ≠ 0 := norm_ne_zero_iff.mpr (one_sub_conj_mul_ne_zero hz hw)
  field_simp

lemma hypRefl_rot (j : Fin 3) (z : ℂ) :
    hypRefl ⟨(j.val + 1) % 3, Nat.mod_lt _ (by norm_num)⟩ (ω * z) = ω * hypRefl j z := by
  unfold hypRefl sideCenter
  have hpow : ω ^ ((j.val + 1) % 3) = ω * ω ^ (j : ℕ) := by
    fin_cases j
    · simp
    · simp [pow_two]
    · simp only [Nat.reduceAdd, Nat.mod_self, pow_zero]
      linear_combination -ω_cube
  rw [hpow, map_mul, map_mul, map_mul, star_ω]
  have h1 : ω * ω ^ 2 = 1 := by rw [← pow_succ', ω_cube]
  have h2 : ω ^ 2 ≠ 0 := pow_ne_zero 2 ω_ne_zero
  calc (ω * ω ^ (j : ℕ) * a0 * (ω ^ 2 * starRingEnd ℂ z) - 1) /
        (ω ^ 2 * starRingEnd ℂ z - ω ^ 2 * (starRingEnd ℂ) (ω ^ (j : ℕ)) * (starRingEnd ℂ) a0)
      = ((ω * ω ^ 2) * (ω ^ (j : ℕ) * a0 * starRingEnd ℂ z) - 1) /
        (ω ^ 2 * (starRingEnd ℂ z - (starRingEnd ℂ) (ω ^ (j : ℕ)) * (starRingEnd ℂ) a0)) := by ring
    _ = (ω ^ (j : ℕ) * a0 * starRingEnd ℂ z - 1) /
        (ω ^ 2 * (starRingEnd ℂ z - (starRingEnd ℂ) (ω ^ (j : ℕ)) * (starRingEnd ℂ) a0)) := by
        rw [h1, one_mul]
    _ = (ω * ω ^ 2) * ((ω ^ (j : ℕ) * a0 * starRingEnd ℂ z - 1) /
        (ω ^ 2 * (starRingEnd ℂ z - (starRingEnd ℂ) (ω ^ (j : ℕ)) * (starRingEnd ℂ) a0))) := by
        rw [h1, one_mul]
    _ = ω * ((ω ^ (j : ℕ) * a0 * starRingEnd ℂ z - 1) /
        (starRingEnd ℂ z - (starRingEnd ℂ) (ω ^ (j : ℕ)) * (starRingEnd ℂ) a0)) := by
        field_simp
    _ = ω * ((ω ^ (j : ℕ) * a0 * starRingEnd ℂ z - 1) /
        (starRingEnd ℂ z - (starRingEnd ℂ) (ω ^ (j : ℕ) * a0))) := by
        rw [map_mul]

lemma hypRefl_conj_zero (z : ℂ) :
    hypRefl 2 (starRingEnd ℂ z) = starRingEnd ℂ (hypRefl 0 z) := by
  unfold hypRefl sideCenter
  have ha2 : ω ^ 2 * a0 = starRingEnd ℂ a0 := by
    unfold a0
    simp only [map_mul, Complex.conj_ofReal, map_add, map_one, star_ω]
    have : ω ^ 2 * (1 + ω) = 1 + ω ^ 2 := by
      calc ω ^ 2 * (1 + ω) = ω ^ 2 + ω ^ 3 := by ring
        _ = 1 + ω ^ 2 := by rw [ω_cube]; ring
    linear_combination (((2 + Real.sqrt 3) * R : ℝ) : ℂ) * this
  simp only [Fin.val_two, Fin.val_zero, pow_zero, one_mul, ha2, map_div₀, map_sub, map_mul,
    map_one, RingHomCompTriple.comp_apply, RingHom.id_apply]

/- ## 4. Hyperbolic Triangle `Δ₁` Properties -/

def Δ1Open : Set ℂ :=
  {z : ℂ | ‖z‖ < 1 ∧ ∀ j : Fin 3, ‖sideCenter j‖ ^ 2 - 1 < ‖z - sideCenter j‖ ^ 2}

def Δ1 : Set ℂ :=
  {z : ℂ | ‖z‖ < 1 ∧ ∀ j : Fin 3, ‖sideCenter j‖ ^ 2 - 1 ≤ ‖z - sideCenter j‖ ^ 2}

def vert1 (k : Fin 3) : ℂ := ω ^ (k : ℕ) * (R : ℂ)

lemma vert1_norm (k : Fin 3) : ‖vert1 k‖ = R := by
  unfold vert1
  rw [norm_mul, norm_ω_pow, one_mul, Complex.norm_real, Real.norm_of_nonneg R_pos.le]

lemma vert1_mem_ball (k : Fin 3) : ‖vert1 k‖ < 1 := by
  rw [vert1_norm]; exact R_lt_one

lemma a0_add_conj_a0 : a0 + starRingEnd ℂ a0 = (((2 + Real.sqrt 3) * R : ℝ) : ℂ) := by
  unfold a0
  simp only [map_mul, Complex.conj_ofReal, map_add, map_one, star_ω]
  have h : (1 + ω) + (1 + ω ^ 2) = 1 := by linear_combination ω_sq_add_ω_add_one
  linear_combination (((2 + Real.sqrt 3) * R : ℝ) : ℂ) * h

lemma a0_re : a0.re = (2 + Real.sqrt 3) * R / 2 := by
  unfold a0
  rw [one_add_ω]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  ring

lemma a0_im : a0.im = (2 + Real.sqrt 3) * R * Real.sqrt 3 / 2 := by
  unfold a0
  rw [one_add_ω]
  simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  ring

lemma vert1_zero_on_side0 : ‖vert1 0 - sideCenter 0‖ ^ 2 = ‖sideCenter 0‖ ^ 2 - 1 := by
  have h := normSq_sub_sideCenter_iff 0 (vert1 0)
  rw [sub_eq_iff_eq_add] at h
  have hv : vert1 0 = (R : ℂ) := by simp [vert1]
  have ha : sideCenter 0 = a0 := by simp [sideCenter]
  have hre : ((R : ℂ) * starRingEnd ℂ a0).re = (2 + Real.sqrt 3) * R ^ 2 / 2 := by
    simp only [mul_re, ofReal_re, ofReal_im, conj_re, conj_im, zero_mul, sub_zero, a0_re]
    ring
  rw [hv, ha] at h ⊢
  rw [Complex.norm_real, Real.norm_of_nonneg R_pos.le, hre] at h
  have hzero : R ^ 2 - 2 * ((2 + Real.sqrt 3) * R ^ 2 / 2) + 1 = 0 := by
    have := R_sq_mul; linarith
  linarith

lemma vert1_zero_on_side2 : ‖vert1 0 - sideCenter 2‖ ^ 2 = ‖sideCenter 2‖ ^ 2 - 1 := by
  have h := vert1_zero_on_side0
  have ha2 : sideCenter 2 = starRingEnd ℂ (sideCenter 0) := by
    simp only [sideCenter, Fin.val_two, Fin.val_zero, pow_zero, one_mul]
    unfold a0
    simp only [map_mul, Complex.conj_ofReal, map_add, map_one, star_ω]
    have : ω ^ 2 * (1 + ω) = 1 + ω ^ 2 := by
      calc ω ^ 2 * (1 + ω) = ω ^ 2 + ω ^ 3 := by ring
        _ = 1 + ω ^ 2 := by rw [ω_cube]; ring
    linear_combination (((2 + Real.sqrt 3) * R : ℝ) : ℂ) * this
  rw [ha2, RCLike.norm_conj]
  have hv : starRingEnd ℂ (vert1 0) = vert1 0 := by simp [vert1]
  rw [← hv, ← map_sub, RCLike.norm_conj]
  exact h

lemma vert1_zero_strict_side1 : ‖sideCenter 1‖ ^ 2 - 1 < ‖vert1 0 - sideCenter 1‖ ^ 2 := by
  rw [← sub_pos, normSq_sub_sideCenter_iff]
  have hv : vert1 0 = (R : ℂ) := by simp [vert1]
  have ha1 : sideCenter 1 = -(((2 + Real.sqrt 3) * R : ℝ) : ℂ) := by
    simp only [sideCenter, Fin.val_one, pow_one, a0]
    have : ω * (1 + ω) = -1 := by linear_combination ω_sq_add_ω_add_one
    linear_combination (((2 + Real.sqrt 3) * R : ℝ) : ℂ) * this
  rw [hv, ha1, Complex.norm_real, Real.norm_of_nonneg R_pos.le]
  simp only [map_neg, Complex.conj_ofReal, mul_neg, neg_re, mul_re, ofReal_re, ofReal_im,
    mul_zero, sub_zero]
  nlinarith [R_pos, sqrt3_pos]

lemma Δ1_rot_mem {z : ℂ} (hz : z ∈ Δ1) : ω * z ∈ Δ1 := by
  refine ⟨by rw [norm_mul, norm_ω, one_mul]; exact hz.1, fun j => ?_⟩
  have h1 : ∃ i : Fin 3, ω * sideCenter i = sideCenter j := by
    fin_cases j
    · exact ⟨2, by simp only [sideCenter, Fin.val_two, pow_zero, one_mul]; linear_combination a0 * ω_cube⟩
    · exact ⟨0, by simp [sideCenter]⟩
    · exact ⟨1, by simp [sideCenter]; ring⟩
  obtain ⟨i, hi⟩ := h1
  rw [← hi, ← mul_sub, norm_mul, norm_ω, one_mul, norm_mul, norm_ω, one_mul]
  exact hz.2 i

lemma Δ1Open_rot_mem {z : ℂ} (hz : z ∈ Δ1Open) : ω * z ∈ Δ1Open := by
  refine ⟨by rw [norm_mul, norm_ω, one_mul]; exact hz.1, fun j => ?_⟩
  have h1 : ∃ i : Fin 3, ω * sideCenter i = sideCenter j := by
    fin_cases j
    · exact ⟨2, by simp only [sideCenter, Fin.val_two, pow_zero, one_mul]; linear_combination a0 * ω_cube⟩
    · exact ⟨0, by simp [sideCenter]⟩
    · exact ⟨1, by simp [sideCenter]; ring⟩
  obtain ⟨i, hi⟩ := h1
  rw [← hi, ← mul_sub, norm_mul, norm_ω, one_mul, norm_mul, norm_ω, one_mul]
  exact hz.2 i

lemma vert1_mem_Δ1 (k : Fin 3) : vert1 k ∈ Δ1 := by
  have h0 : vert1 0 ∈ Δ1 := by
    refine ⟨vert1_mem_ball 0, fun j => ?_⟩
    fin_cases j
    · exact vert1_zero_on_side0.ge
    · exact vert1_zero_strict_side1.le
    · exact vert1_zero_on_side2.ge
  fin_cases k
  · exact h0
  · simpa [vert1] using Δ1_rot_mem h0
  · have h1 := Δ1_rot_mem h0
    have h2 := Δ1_rot_mem h1
    simpa [vert1, sq, mul_assoc] using h2

lemma zero_mem_Δ1Open : (0 : ℂ) ∈ Δ1Open := by
  refine ⟨by simp, fun j => ?_⟩
  simp only [zero_sub, norm_neg]
  linarith

lemma isOpen_Δ1Open : IsOpen Δ1Open := by
  have h1 : Δ1Open = ball (0 : ℂ) 1 ∩ ⋂ j : Fin 3,
      (fun z : ℂ => ‖z - sideCenter j‖ ^ 2) ⁻¹' Ioi (‖sideCenter j‖ ^ 2 - 1) := by
    ext z; simp [Δ1Open, Metric.mem_ball, dist_zero_right]
  rw [h1]
  refine isOpen_ball.inter (isOpen_iInter_of_finite fun j => ?_)
  exact isOpen_Ioi.preimage ((continuous_id.sub continuous_const).norm.pow 2)

/-- Every point of `Δ1` has norm at most `R` (so `Δ1` is compact inside `ball 0 1`!). -/
lemma norm_le_R_of_mem_Δ1 {z : ℂ} (hz : z ∈ Δ1) : ‖z‖ ≤ R := by
  -- Sum the three side inequalities with weights `1`: since `a_0 + a_1 + a_2 = 0`,
  -- Wait: that gives `‖z‖^2 + 1 ≥ 0` only. Instead use the max of `Re(z * conj(a_j))`!
  -- Actually: `max_j Re(z * conj(ω^j * (1 + ω))) ≥ (1/2) * ‖z‖`!
  have hmax : ∃ j : Fin 3, (1 / 2 : ℝ) * ‖z‖ ≤ (z * starRingEnd ℂ (ω ^ (j : ℕ) * (1 + ω))).re := by
    -- The three unit vectors `u_j = ω^j * (1 + ω)` sum to 0 and have pairwise angle `2π/3`.
    -- For any `z`, `(u_0·z)^2 + (u_1·z)^2 + (u_2·z)^2 = (3/2) |z|^2` and `u_0·z + u_1·z + u_2·z = 0`.
    -- If all three are `< (1/2) |z|`, then the two negatives have sum `> -|z|`, Wait:
    -- Let `x_j = Re(z * conj u_j)`. Then `x_0 + x_1 + x_2 = 0` and `x_0^2 + x_1^2 + x_2^2 = (3/2) ‖z‖^2`.
    -- By Cauchy-Schwarz / elementary algebra: `max(x_0, x_1, x_2) ≥ (1/2) ‖z‖`!
    -- Wait: check `x_0 = 1, x_1 = -1/2, x_2 = -1/2` -> sum 0, sum sq 3/2, max = 1 ≥ 1/2!
    -- Check `x_0 = 1/2, x_1 = 1/2, x_2 = -1` -> sum 0, sum sq 3/2, max = 1/2 ≥ 1/2! (EQUALITY!)
    -- Proof of algebra: if `x_0, x_1, x_2 < m` and `x_0 + x_1 + x_2 = 0`, then
    -- `x_0^2 + x_1^2 + x_2^2 = 2(x_0^2 + x_0 x_1 + x_1^2)` and since `-2m < x_0 + x_1 = -x_2`...
    -- Even simpler: `(m - x_0)(m - x_1)(m - x_2) = m^3 - m(x_0 x_1 + x_1 x_2 + x_2 x_0) - x_0 x_1 x_2`?
    -- No, just `x_i ≤ m` for all `i`, and `x_0 + x_1 + x_2 = 0` implies `-2m ≤ x_i ≤ m` for all `i`,
    -- and `(m - x_0)(2m + x_0) ≥ 0`, wait: `x_0^2 + x_1^2 + x_2^2 ≤ 6 m^2`!
    -- CHECK: if `x_i ≤ m` and `x_0 + x_1 + x_2 = 0`, then `(m - x_0)(m - x_1) ≥ 0` etc.,
    -- expand `(m - x_0) + (m - x_1) + (m - x_2) = 3m`, so sum of squares of `y_i = m - x_i ≥ 0`:
    -- `∑ y_i^2 ≤ (∑ y_i)^2 = 9 m^2`!!
    -- WAIT: `∑ (m - x_i)^2 = 3 m^2 - 2 m ∑ x_i + ∑ x_i^2 = 3 m^2 + ∑ x_i^2 ≤ 9 m^2`
    -- `⟹ ∑ x_i^2 ≤ 6 m^2`!!
    -- PLUG IN `∑ x_i^2 = (3/2) ‖z‖^2` and `m = (1/2) ‖z‖` -> `6 m^2 = (3/2) ‖z‖^2`!!
    -- THAT'S LITERALLY ONE LINE!!
    by_contra hlt
    push Not at hlt
    set m : ℝ := (1 / 2) * ‖z‖
    set x0 : ℝ := (z * starRingEnd ℂ (ω ^ (0 : ℕ) * (1 + ω))).re
    set x1 : ℝ := (z * starRingEnd ℂ (ω ^ (1 : ℕ) * (1 + ω))).re
    set x2 : ℝ := (z * starRingEnd ℂ (ω ^ (2 : ℕ) * (1 + ω))).re
    have hx0 : x0 < m := hlt 0
    have hx1 : x1 < m := hlt 1
    have hx2 : x2 < m := hlt 2
    have hsum : x0 + x1 + x2 = 0 := by
      have h012 : (ω ^ (0 : ℕ) + ω ^ (1 : ℕ) + ω ^ (2 : ℕ) : ℂ) = 0 := by
        simp only [pow_zero, pow_one]; linear_combination ω_sq_add_ω_add_one
      have htot : z * starRingEnd ℂ (ω ^ (0 : ℕ) * (1 + ω)) +
          z * starRingEnd ℂ (ω ^ (1 : ℕ) * (1 + ω)) +
          z * starRingEnd ℂ (ω ^ (2 : ℕ) * (1 + ω)) = 0 := by
        have : ω ^ (0 : ℕ) * (1 + ω) + ω ^ (1 : ℕ) * (1 + ω) + ω ^ (2 : ℕ) * (1 + ω) = 0 := by
          linear_combination (1 + ω) * h012
        calc _ = z * starRingEnd ℂ (ω ^ (0 : ℕ) * (1 + ω) + ω ^ (1 : ℕ) * (1 + ω) +
              ω ^ (2 : ℕ) * (1 + ω)) := by simp [mul_add, map_add]
          _ = 0 := by rw [this, map_zero, mul_zero]
      have := congrArg Complex.re htot
      simpa [x0, x1, x2] using this
    have hsq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 = (3 / 2) * ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hx0' : x0 = (1 / 2) * z.re + (Real.sqrt 3 / 2) * z.im := by
        simp only [x0, pow_zero, one_mul, one_add_ω, mul_re, conj_re, conj_im]; ring
      have hx1' : x1 = -z.re := by
        have h1 : ω ^ (1 : ℕ) * (1 + ω) = -1 := by
          simp only [pow_one]; linear_combination ω_sq_add_ω_add_one
        simp only [x1, h1, map_neg, map_one, mul_neg, mul_one, neg_re]
      have hx2' : x2 = (1 / 2) * z.re - (Real.sqrt 3 / 2) * z.im := by
        have h2 : ω ^ (2 : ℕ) * (1 + ω) = ⟨1 / 2, -(Real.sqrt 3 / 2)⟩ := by
          rw [ω_sq, one_add_ω]; apply Complex.ext <;> simp <;> nlinarith [sq_sqrt3]
        simp only [x2, h2, mul_re, conj_re, conj_im]; ring
      rw [hx0', hx1', hx2']
      nlinarith [sq_sqrt3]
    have hy0 : 0 < m - x0 := by linarith
    have hy1 : 0 < m - x1 := by linarith
    have hy2 : 0 < m - x2 := by linarith
    have hcomb : (m - x0) ^ 2 + (m - x1) ^ 2 + (m - x2) ^ 2 <
        ((m - x0) + (m - x1) + (m - x2)) ^ 2 := by nlinarith
    have hlhs : (m - x0) ^ 2 + (m - x1) ^ 2 + (m - x2) ^ 2 = 3 * m ^ 2 + (3 / 2) * ‖z‖ ^ 2 := by
      nlinarith [hsum, hsq]
    have hrhs : ((m - x0) + (m - x1) + (m - x2)) ^ 2 = 9 * m ^ 2 := by
      have : (m - x0) + (m - x1) + (m - x2) = 3 * m := by linarith
      rw [this]; ring
    rw [hlhs, hrhs] at hcomb
    have hm2 : 6 * m ^ 2 = (3 / 2) * ‖z‖ ^ 2 := by simp only [m]; ring
    linarith
  obtain ⟨j, hj⟩ := hmax
  have hside := hz.2 j
  have hiff := normSq_sub_sideCenter_iff j z
  have hge : 0 ≤ ‖z‖ ^ 2 - 2 * (z * starRingEnd ℂ (sideCenter j)).re + 1 := by linarith
  have hre_eq : (z * starRingEnd ℂ (sideCenter j)).re =
      ((2 + Real.sqrt 3) * R) * (z * starRingEnd ℂ (ω ^ (j : ℕ) * (1 + ω))).re := by
    unfold sideCenter a0
    have hmul : ω ^ (j : ℕ) * ((((2 + Real.sqrt 3) * R : ℝ) : ℂ) * (1 + ω)) =
        (((2 + Real.sqrt 3) * R : ℝ) : ℂ) * (ω ^ (j : ℕ) * (1 + ω)) := by ring
    rw [hmul, map_mul, Complex.conj_ofReal, ← mul_assoc, mul_comm z, mul_assoc]
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [hre_eq] at hge
  have hc_pos : 0 < (2 + Real.sqrt 3) * R := by have := R_pos; have := sqrt3_pos; positivity
  have hquad : 0 ≤ ‖z‖ ^ 2 - ((2 + Real.sqrt 3) * R) * ‖z‖ + 1 := by
    nlinarith
  -- Factor: `‖z‖^2 - (2 + √3) R ‖z‖ + 1 = (R - ‖z‖) * (1/R - ‖z‖)`!
  have hsum_R : (2 + Real.sqrt 3) * R = R + 1 / R := by
    have hR := R_ne_zero
    field_simp
    have hR2 := R_sq_mul
    nlinarith [sq_sqrt3]
  rw [hsum_R] at hquad
  have hfac : 0 ≤ (R - ‖z‖) * (1 / R - ‖z‖) := by
    have : (R - ‖z‖) * (1 / R - ‖z‖) = ‖z‖ ^ 2 - (R + 1 / R) * ‖z‖ + 1 := by
      have hR := R_ne_zero; field_simp; ring
    linarith
  have hinv : 0 < 1 / R - ‖z‖ := by
    have h1 : 1 < 1 / R := (one_lt_div R_pos).mpr R_lt_one
    linarith [hz.1]
  nlinarith

lemma Δ1_eq_closed :
    Δ1 = {z : ℂ | ‖z‖ ≤ R ∧ ∀ j : Fin 3, ‖sideCenter j‖ ^ 2 - 1 ≤ ‖z - sideCenter j‖ ^ 2} := by
  ext z
  exact ⟨fun h => ⟨norm_le_R_of_mem_Δ1 h, h.2⟩, fun h => ⟨lt_of_le_of_lt h.1 R_lt_one, h.2⟩⟩

lemma isCompact_Δ1 : IsCompact Δ1 := by
  rw [Δ1_eq_closed]
  have hsub : {z : ℂ | ‖z‖ ≤ R ∧ ∀ j : Fin 3, ‖sideCenter j‖ ^ 2 - 1 ≤ ‖z - sideCenter j‖ ^ 2} =
      closedBall (0 : ℂ) R ∩ ⋂ j : Fin 3,
        (fun z : ℂ => ‖z - sideCenter j‖ ^ 2) ⁻¹' Ici (‖sideCenter j‖ ^ 2 - 1) := by
    ext z; simp [Metric.mem_closedBall, dist_zero_right]
  rw [hsub]
  refine (isCompact_closedBall (0 : ℂ) R).inter_right (isClosed_iInter fun j => ?_)
  exact isClosed_Ici.preimage ((continuous_id.sub continuous_const).norm.pow 2)

lemma isClosed_Δ1 : IsClosed Δ1 := isCompact_Δ1.isClosed

lemma isBounded_Δ1Open : Bornology.IsBounded Δ1Open :=
  (isCompact_Δ1.isBounded).subset fun _ h => ⟨h.1, fun j => (h.2 j).le⟩

/-- Star-shapedness of `Δ1` and `Δ1Open` around `0`. -/
lemma smul_mem_Δ1Open_of_mem_Δ1 {z : ℂ} (hz : z ∈ Δ1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (t : ℂ) * z ∈ Δ1Open := by
  have hnorm : ‖(t : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
    nlinarith [hz.1, norm_nonneg z]
  refine ⟨hnorm, fun j => ?_⟩
  rw [← sub_pos, normSq_sub_sideCenter_iff]
  have hj := hz.2 j
  have hiff := normSq_sub_sideCenter_iff j z
  have h1 : 0 ≤ ‖z‖ ^ 2 - 2 * (z * starRingEnd ℂ (sideCenter j)).re + 1 := by linarith
  have hre : ((t : ℂ) * z * starRingEnd ℂ (sideCenter j)).re =
      t * (z * starRingEnd ℂ (sideCenter j)).re := by
    rw [mul_assoc]; simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  have hnt : ‖(t : ℂ) * z‖ ^ 2 = t ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0, mul_pow]
  rw [hnt, hre]
  set b := (z * starRingEnd ℂ (sideCenter j)).re
  by_cases hb : b ≤ ‖z‖ ^ 2
  · have hstep : t ^ 2 * ‖z‖ ^ 2 - 2 * (t * b) + 1 ≥ (1 - t) ^ 2 * ‖z‖ ^ 2 + (1 - ‖z‖ ^ 2) := by
      nlinarith
    have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [hz.1, norm_nonneg z]
    nlinarith
  · push Not at hb
    -- Since `b > ‖z‖^2` and `t < 1`, `(t^2 - 1) ‖z‖^2 - 2(t - 1) b = (1 - t) (2 b - (1 + t) ‖z‖^2) > 0`!
    have hpos : 0 < (1 - t) * (2 * b - (1 + t) * ‖z‖ ^ 2) := by
      have h2 : 0 < 2 * b - (1 + t) * ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      nlinarith
    nlinarith

lemma smul_mem_Δ1 {z : ℂ} (hz : z ∈ Δ1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : ℂ) * z ∈ Δ1 := by
  rcases eq_or_lt_of_le ht1 with rfl | hlt
  · simpa using hz
  · have h := smul_mem_Δ1Open_of_mem_Δ1 hz ht0 hlt
    exact ⟨h.1, fun j => (h.2 j).le⟩

lemma closure_Δ1Open : closure Δ1Open = Δ1 := by
  apply Subset.antisymm
  · exact isClosed_Δ1.closure_subset_iff.mpr fun _ h => ⟨h.1, fun j => (h.2 j).le⟩
  · intro z hz
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, ht0, ht1, hdist⟩ : ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ (1 - t) * ‖z‖ < ε := by
      refine ⟨1 - min (1 / 2) (ε / (2 * (‖z‖ + 1))), ?_, ?_, ?_⟩
      · have : min (1 / 2) (ε / (2 * (‖z‖ + 1))) ≤ 1 / 2 := min_le_left _ _
        linarith
      · have : 0 < min (1 / 2) (ε / (2 * (‖z‖ + 1))) := lt_min (by norm_num) (by positivity)
        linarith
      · have hle : min (1 / 2) (ε / (2 * (‖z‖ + 1))) ≤ ε / (2 * (‖z‖ + 1)) := min_le_right _ _
        have hpos : 0 < 2 * (‖z‖ + 1) := by positivity
        have h1 : (1 - (1 - min (1 / 2) (ε / (2 * (‖z‖ + 1))))) * ‖z‖ ≤
            (ε / (2 * (‖z‖ + 1))) * ‖z‖ := by
          rw [sub_sub_cancel]; exact mul_le_mul_of_nonneg_right hle (norm_nonneg z)
        have h2 : (ε / (2 * (‖z‖ + 1))) * ‖z‖ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]; nlinarith [norm_nonneg z]
        linarith
    refine ⟨(t : ℂ) * z, smul_mem_Δ1Open_of_mem_Δ1 hz ht0 ht1, ?_⟩
    rw [dist_eq_norm, show z - (t : ℂ) * z = ((1 - t : ℝ) : ℂ) * z by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact hdist

lemma interior_Δ1 : interior Δ1 = Δ1Open := by
  apply Subset.antisymm
  · intro z hz
    have hmem : z ∈ Δ1 := interior_subset hz
    refine ⟨hmem.1, fun j => ?_⟩
    by_contra hle
    push Not at hle
    have heq : ‖z - sideCenter j‖ ^ 2 = ‖sideCenter j‖ ^ 2 - 1 := le_antisymm hle (hmem.2 j)
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hz
    obtain ⟨δ, hδ, hball⟩ := hz
    -- Move slightly towards `sideCenter j` to violate the inequality!
    have hne : z - sideCenter j ≠ 0 := by
      intro h0
      rw [h0, norm_zero, zero_pow two_ne_zero] at heq
      linarith [sideCenter_sq_sub_one_pos j]
    set s : ℝ := min (1 / 2) (δ / (2 * ‖z - sideCenter j‖))
    have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
    have hs1 : s < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    set w : ℂ := z - (s : ℂ) * (z - sideCenter j)
    have hw_ball : w ∈ ball z δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : w - z = -((s : ℂ) * (z - sideCenter j)) := by simp [w]
      rw [this, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      have hsle : s ≤ δ / (2 * ‖z - sideCenter j‖) := min_le_right _ _
      have hpos : 0 < ‖z - sideCenter j‖ := norm_pos_iff.mpr hne
      have : s * ‖z - sideCenter j‖ ≤ δ / 2 := by
        calc s * ‖z - sideCenter j‖ ≤ (δ / (2 * ‖z - sideCenter j‖)) * ‖z - sideCenter j‖ :=
              mul_le_mul_of_nonneg_right hsle hpos.le
          _ = δ / 2 := by field_simp
      linarith
    have hw_Δ1 := hball hw_ball
    have hw_sub : w - sideCenter j = ((1 - s : ℝ) : ℂ) * (z - sideCenter j) := by
      simp only [w]; push_cast; ring
    have hw_ineq := hw_Δ1.2 j
    rw [hw_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), mul_pow, heq] at hw_ineq
    have hpos := sideCenter_sq_sub_one_pos j
    have hlt1 : (1 - s) ^ 2 < 1 := by nlinarith
    nlinarith
  · exact interior_maximal (fun _ h => ⟨h.1, fun j => (h.2 j).le⟩) isOpen_Δ1Open

lemma frontier_Δ1Open : frontier Δ1Open = Δ1 \ Δ1Open := by
  rw [frontier, closure_Δ1Open, isOpen_Δ1Open.interior_eq]

/- ## 5. Vertex Coordinate `T_0` and Dihedral Group `D_6` Around `v_0 = R` -/

/-- Complex phase `e^(-iπ/6) = √3/2 - i/2`. -/
def zeta12Inv : ℂ := ⟨Real.sqrt 3 / 2, -1 / 2⟩
/-- Complex phase `e^(iπ/6) = √3/2 + i/2`. -/
def zeta12 : ℂ := ⟨Real.sqrt 3 / 2, 1 / 2⟩

lemma zeta12_mul_conj : zeta12 * zeta12Inv = 1 := by
  apply Complex.ext <;> simp [zeta12, zeta12Inv] <;> nlinarith [sq_sqrt3]

lemma zeta12_sq : zeta12 ^ 2 = ⟨1 / 2, Real.sqrt 3 / 2⟩ := by
  apply Complex.ext <;> simp [zeta12, sq] <;> nlinarith [sq_sqrt3]

lemma zeta12_pow_six : (zeta12 ^ 2) ^ 3 = -1 := by
  rw [zeta12_sq]
  apply Complex.ext
  · simp only [pow_succ, pow_zero, one_mul, mul_re, mul_im, neg_re, one_re]
    linear_combination -(3 / 8 : ℝ) * sq_sqrt3
  · simp only [pow_succ, pow_zero, one_mul, mul_re, mul_im, neg_im, one_im, neg_zero]
    linear_combination -(Real.sqrt 3 / 8) * sq_sqrt3

lemma star_zeta12Inv : starRingEnd ℂ zeta12Inv = zeta12 := by
  apply Complex.ext
  · simp [zeta12Inv, zeta12]
  · simp [zeta12Inv, zeta12]; ring

lemma mobiusToZero_R_hypRefl0 {z : ℂ} (hz : ‖z‖ < 1) :
    mobiusToZero (R : ℂ) (hypRefl 0 z) = zeta12Inv * starRingEnd ℂ (mobiusToZero (R : ℂ) z) := by
  unfold mobiusToZero hypRefl
  simp only [sideCenter, Fin.val_zero, pow_zero, one_mul, map_div₀, map_sub, map_mul, map_one,
    Complex.conj_ofReal]
  have h1 : starRingEnd ℂ z - starRingEnd ℂ a0 ≠ 0 := by
    simpa [sideCenter] using conj_sub_conj_sideCenter_ne_zero 0 hz
  have h2 : 1 - (R : ℂ) * starRingEnd ℂ z ≠ 0 := by
    have : 1 - starRingEnd ℂ (R : ℂ) * starRingEnd ℂ z ≠ 0 := by
      refine one_sub_conj_mul_ne_zero ?_ ?_
      · simpa [RCLike.norm_conj] using hz
      · simpa [Complex.norm_real, Real.norm_of_nonneg R_pos.le] using R_lt_one
    simpa [Complex.conj_ofReal] using this
  have h3 : 1 - (R : ℂ) * ((a0 * starRingEnd ℂ z - 1) / (starRingEnd ℂ z - starRingEnd ℂ a0)) ≠ 0 := by
    have hr := hypRefl_mem_ball 0 hz
    have hR : ‖(R : ℂ)‖ < 1 := by
      simpa [Complex.norm_real, Real.norm_of_nonneg R_pos.le] using R_lt_one
    simpa [hypRefl, sideCenter, Complex.conj_ofReal] using one_sub_conj_mul_ne_zero hr hR
  have hsum : (R : ℂ) * (a0 + starRingEnd ℂ a0) = 1 + (R : ℂ) ^ 2 := by
    rw [a0_add_conj_a0]
    have hR2 : (2 + Real.sqrt 3) * R ^ 2 = 1 + R ^ 2 := by linarith [R_sq_mul]
    exact_mod_cast (by linarith : R * ((2 + Real.sqrt 3) * R) = 1 + R ^ 2)
  have hrot : a0 - (R : ℂ) = zeta12Inv * ((R : ℂ) - starRingEnd ℂ a0) := by
    apply Complex.ext
    · simp only [sub_re, sub_im, mul_re, conj_re, conj_im, ofReal_re, ofReal_im, zeta12Inv, a0_re, a0_im]
      ring
    · simp only [sub_re, sub_im, mul_im, conj_re, conj_im, ofReal_re, ofReal_im, zeta12Inv, a0_re, a0_im]
      linear_combination -(R * Real.sqrt 3 / 4) * sq_sqrt3
  have hrel1 : (R : ℂ) * starRingEnd ℂ a0 - 1 = -(R : ℂ) * (a0 - (R : ℂ)) := by
    linear_combination hsum
  have hrel2 : 1 - (R : ℂ) * a0 = -(R : ℂ) * ((R : ℂ) - starRingEnd ℂ a0) := by
    linear_combination -hsum
  have hL : (a0 * starRingEnd ℂ z - 1) - (R : ℂ) * (starRingEnd ℂ z - starRingEnd ℂ a0) =
      (a0 - (R : ℂ)) * (starRingEnd ℂ z - (R : ℂ)) := by linear_combination hrel1
  have hR_den : (starRingEnd ℂ z - starRingEnd ℂ a0) - (R : ℂ) * (a0 * starRingEnd ℂ z - 1) =
      ((R : ℂ) - starRingEnd ℂ a0) * (1 - (R : ℂ) * starRingEnd ℂ z) := by
    linear_combination (starRingEnd ℂ z) * hrel2
  have hnum_eq : (a0 * starRingEnd ℂ z - 1) / (starRingEnd ℂ z - starRingEnd ℂ a0) - (R : ℂ) =
      ((a0 - (R : ℂ)) * (starRingEnd ℂ z - (R : ℂ))) / (starRingEnd ℂ z - starRingEnd ℂ a0) := by
    rw [div_sub' h1]; congr 1; linear_combination hL
  have hden_eq : 1 - (R : ℂ) * ((a0 * starRingEnd ℂ z - 1) / (starRingEnd ℂ z - starRingEnd ℂ a0)) =
      (((R : ℂ) - starRingEnd ℂ a0) * (1 - (R : ℂ) * starRingEnd ℂ z)) /
        (starRingEnd ℂ z - starRingEnd ℂ a0) := by
    rw [mul_div_assoc', one_sub_div h1]; congr 1
  rw [mul_div_assoc' zeta12Inv, div_eq_div_iff h3 h2, hnum_eq, hden_eq, hrot]
  ring

lemma mobiusToZero_R_hypRefl2 {z : ℂ} (hz : ‖z‖ < 1) :
    mobiusToZero (R : ℂ) (hypRefl 2 z) = zeta12 * starRingEnd ℂ (mobiusToZero (R : ℂ) z) := by
  have hcz : ‖starRingEnd ℂ z‖ < 1 := by simpa [RCLike.norm_conj] using hz
  have h0 := congrArg (starRingEnd ℂ) (mobiusToZero_R_hypRefl0 hcz)
  have hconj_m : ∀ w : ℂ, starRingEnd ℂ (mobiusToZero (R : ℂ) w) =
      mobiusToZero (R : ℂ) (starRingEnd ℂ w) := by
    intro w; unfold mobiusToZero
    simp [Complex.conj_ofReal]
  rw [hconj_m, map_mul, ← hypRefl_conj_zero, RingHomCompTriple.comp_apply, RingHom.id_apply,
    hconj_m, RingHomCompTriple.comp_apply, RingHom.id_apply, star_zeta12Inv] at h0
  exact h0

lemma mobiusToZero_R_rot20 {z : ℂ} (hz : ‖z‖ < 1) :
    mobiusToZero (R : ℂ) (hypRefl 2 (hypRefl 0 z)) =
      zeta12 ^ 2 * mobiusToZero (R : ℂ) z := by
  rw [mobiusToZero_R_hypRefl2 (hypRefl_mem_ball 0 hz), mobiusToZero_R_hypRefl0 hz,
    map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply, star_zeta12Inv]
  ring

lemma mobiusToZero_R_halfTurn {z : ℂ} (hz : ‖z‖ < 1) :
    mobiusToZero (R : ℂ) ((hypRefl 2 ∘ hypRefl 0)^[3] z) = -mobiusToZero (R : ℂ) z := by
  have h1 := hypRefl_mem_ball 2 (hypRefl_mem_ball 0 hz)
  have h2 := hypRefl_mem_ball 2 (hypRefl_mem_ball 0 h1)
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
  rw [mobiusToZero_R_rot20 h2, mobiusToZero_R_rot20 h1, mobiusToZero_R_rot20 hz]
  have : zeta12 ^ 2 * (zeta12 ^ 2 * (zeta12 ^ 2 * mobiusToZero (R : ℂ) z)) =
      (zeta12 ^ 2) ^ 3 * mobiusToZero (R : ℂ) z := by ring
  rw [this, zeta12_pow_six, neg_one_mul]

/- ## 6. Euclidean Equilateral Triangle `Δ₂`, Reflections `R_j`, and Target Lattice `L` -/

def Δ2Open : Set ℂ :=
  {w : ℂ | ∀ j : Fin 3, -(cAG / 2) < (ω ^ (j : ℕ) * w).re}

def Δ2 : Set ℂ :=
  {w : ℂ | ∀ j : Fin 3, -(cAG / 2) ≤ (ω ^ (j : ℕ) * w).re}

def vert2 (k : Fin 3) : ℂ := ω ^ (k : ℕ) * (cAG : ℂ)

def targetLattice : Set ℂ :=
  {w : ℂ | ∃ m n : ℤ, w = (cAG : ℂ) * (1 + (m : ℂ) * (ω - 1) + (n : ℂ) * (ω ^ 2 - 1))}

/-- Euclidean reflection across side `j` of `Δ₂` (connecting `vert2 j` and `vert2 (j+1)`). -/
def eucRefl (j : Fin 3) (w : ℂ) : ℂ :=
  match j with
  | ⟨0, _⟩ => -ω * starRingEnd ℂ w + (cAG : ℂ) * (1 + ω)
  | ⟨1, _⟩ => -starRingEnd ℂ w - (cAG : ℂ)
  | ⟨2, _⟩ => -(ω ^ 2) * starRingEnd ℂ w + (cAG : ℂ) * (1 + ω ^ 2)

lemma eucRefl_invol (j : Fin 3) (w : ℂ) : eucRefl j (eucRefl j w) = w := by
  fin_cases j
  · simp only [eucRefl, map_add, map_mul, map_neg, map_one, Complex.conj_ofReal, star_ω,
      RingHomCompTriple.comp_apply, RingHom.id_apply]
    linear_combination (w - (cAG : ℂ)) * ω_cube
  · simp [eucRefl]
  · simp only [eucRefl, map_add, map_mul, map_neg, map_one, Complex.conj_ofReal, star_ω_sq,
      RingHomCompTriple.comp_apply, RingHom.id_apply]
    linear_combination (w - (cAG : ℂ)) * ω_cube

lemma eucRefl_rot (j : Fin 3) (w : ℂ) :
    eucRefl ⟨(j.val + 1) % 3, Nat.mod_lt _ (by norm_num)⟩ (ω * w) = ω * eucRefl j w := by
  fin_cases j
  · simp only [eucRefl, map_mul, star_ω]
    linear_combination -(cAG : ℂ) * ω_sq_add_ω_add_one
  · simp only [eucRefl, map_mul, star_ω]
    linear_combination -ω * starRingEnd ℂ w * ω_cube + (cAG : ℂ) * ω_sq_add_ω_add_one
  · simp only [eucRefl, map_mul, star_ω]
    linear_combination -(cAG : ℂ) * ω_cube

lemma eucRefl_rot20_cube (w : ℂ) : (eucRefl 2 ∘ eucRefl 0)^[3] w = w := by
  have hstep : ∀ z : ℂ, eucRefl 2 (eucRefl 0 z) = ω * z + (cAG : ℂ) * (1 - ω) := by
    intro z
    simp only [eucRefl, map_add, map_mul, map_neg, map_one, Complex.conj_ofReal, star_ω,
      RingHomCompTriple.comp_apply, RingHom.id_apply]
    linear_combination (ω * z - (cAG : ℂ) * ω) * ω_cube
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, hstep]
  linear_combination w * ω_cube + (cAG : ℂ) * (1 - ω) * ω_sq_add_ω_add_one

lemma eucRefl_preserves_lattice (j : Fin 3) {w : ℂ} (hw : w ∈ targetLattice) :
    eucRefl j w ∈ targetLattice := by
  obtain ⟨m, n, rfl⟩ := hw
  fin_cases j
  · refine ⟨m + n, -n, ?_⟩
    simp only [eucRefl, map_mul, map_add, map_one, map_sub, map_intCast, Complex.conj_ofReal,
      star_ω, star_ω_sq, Int.cast_add, Int.cast_neg]
    linear_combination -(cAG : ℂ) * (m : ℂ) * ω_cube
  · refine ⟨1 - n, 1 - m, ?_⟩
    simp only [eucRefl, map_mul, map_add, map_one, map_sub, map_intCast, Complex.conj_ofReal,
      star_ω, star_ω_sq, Int.cast_sub, Int.cast_one]
    linear_combination -(cAG : ℂ) * ω_sq_add_ω_add_one
  · refine ⟨-m, m + n, ?_⟩
    simp only [eucRefl, map_mul, map_add, map_one, map_sub, map_intCast, Complex.conj_ofReal,
      star_ω, star_ω_sq, Int.cast_add, Int.cast_neg]
    linear_combination -(cAG : ℂ) * ((n : ℂ) + (m : ℂ) * ω) * ω_cube

lemma lattice_inter_Δ2 {w : ℂ} (hwL : w ∈ targetLattice) (hwT : w ∈ Δ2) :
    w = vert2 0 ∨ w = vert2 1 ∨ w = vert2 2 := by
  obtain ⟨m, n, rfl⟩ := hwL
  have hc := cAG_pos
  have h0 : -(cAG / 2) ≤ (ω ^ (0 : ℕ) * ((cAG : ℂ) * (1 + (m : ℂ) * (ω - 1) + (n : ℂ) * (ω ^ 2 - 1)))).re :=
    hwT 0
  have h1 : -(cAG / 2) ≤ (ω ^ (1 : ℕ) * ((cAG : ℂ) * (1 + (m : ℂ) * (ω - 1) + (n : ℂ) * (ω ^ 2 - 1)))).re :=
    hwT 1
  have h2 : -(cAG / 2) ≤ (ω ^ (2 : ℕ) * ((cAG : ℂ) * (1 + (m : ℂ) * (ω - 1) + (n : ℂ) * (ω ^ 2 - 1)))).re :=
    hwT 2
  have hre0 : (ω ^ (0 : ℕ) * ((cAG : ℂ) * (1 + (m : ℂ) * (ω - 1) + (n : ℂ) * (ω ^ 2 - 1)))).re =
      cAG * (1 - (3 / 2 : ℝ) * (m : ℝ) - (3 / 2 : ℝ) * (n : ℝ)) := by
    simp only [pow_zero, one_mul, mul_re, ofReal_re, ofReal_im, add_re, sub_re, intCast_re,
      intCast_im, ω_re, ω_sq, zero_mul, sub_zero, one_re]
    ring
  have hre1 : (ω ^ (1 : ℕ) * ((cAG : ℂ) * (1 + (m : ℂ) * (ω - 1) + (n : ℂ) * (ω ^ 2 - 1)))).re =
      cAG * (-(1 / 2 : ℝ) + (3 / 2 : ℝ) * (n : ℝ)) := by
    have hmul : ω ^ (1 : ℕ) * ((cAG : ℂ) * (1 + (m : ℂ) * (ω - 1) + (n : ℂ) * (ω ^ 2 - 1))) =
        (cAG : ℂ) * (ω + (m : ℂ) * (ω ^ 2 - ω) + (n : ℂ) * (1 - ω)) := by
      simp only [pow_one]
      linear_combination (cAG : ℂ) * (n : ℂ) * ω_cube
    rw [hmul]
    simp only [mul_re, ofReal_re, ofReal_im, add_re, sub_re, intCast_re, intCast_im, ω_re, ω_sq,
      zero_mul, sub_zero, one_re]
    ring
  have hre2 : (ω ^ (2 : ℕ) * ((cAG : ℂ) * (1 + (m : ℂ) * (ω - 1) + (n : ℂ) * (ω ^ 2 - 1)))).re =
      cAG * (-(1 / 2 : ℝ) + (3 / 2 : ℝ) * (m : ℝ)) := by
    have hmul : ω ^ (2 : ℕ) * ((cAG : ℂ) * (1 + (m : ℂ) * (ω - 1) + (n : ℂ) * (ω ^ 2 - 1))) =
        (cAG : ℂ) * (ω ^ 2 + (m : ℂ) * (1 - ω ^ 2) + (n : ℂ) * (ω - ω ^ 2)) := by
      linear_combination (cAG : ℂ) * ((m : ℂ) + (n : ℂ) * ω) * ω_cube
    rw [hmul]
    simp only [mul_re, ofReal_re, ofReal_im, add_re, sub_re, intCast_re, intCast_im, ω_re, ω_sq,
      zero_mul, sub_zero, one_re]
    ring
  rw [hre0] at h0; rw [hre1] at h1; rw [hre2] at h2
  have hm_ge : (0 : ℤ) ≤ m := by
    have : (0 : ℝ) ≤ (m : ℝ) := by nlinarith
    exact_mod_cast this
  have hn_ge : (0 : ℤ) ≤ n := by
    have : (0 : ℝ) ≤ (n : ℝ) := by nlinarith
    exact_mod_cast this
  have hmn_le : m + n ≤ 1 := by
    have : (m : ℝ) + (n : ℝ) ≤ 1 := by nlinarith
    exact_mod_cast this
  have hcases : (m = 0 ∧ n = 0) ∨ (m = 1 ∧ n = 0) ∨ (m = 0 ∧ n = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; simp [vert2]
  · right; left; simp [vert2]; ring
  · right; right; simp [vert2]; ring

lemma zero_mem_Δ2Open : (0 : ℂ) ∈ Δ2Open := by
  intro j; simp [cAG_pos]

lemma isOpen_Δ2Open : IsOpen Δ2Open := by
  have h1 : Δ2Open = ⋂ j : Fin 3,
      (fun w : ℂ => (ω ^ (j : ℕ) * w).re) ⁻¹' Ioi (-(cAG / 2)) := by
    ext w; simp [Δ2Open]
  rw [h1]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_Ioi.preimage (Complex.continuous_re.comp (continuous_const.mul continuous_id))

lemma isClosed_Δ2 : IsClosed Δ2 := by
  have h1 : Δ2 = ⋂ j : Fin 3,
      (fun w : ℂ => (ω ^ (j : ℕ) * w).re) ⁻¹' Ici (-(cAG / 2)) := by
    ext w; simp [Δ2]
  rw [h1]
  exact isClosed_iInter fun j =>
    isClosed_Ici.preimage (Complex.continuous_re.comp (continuous_const.mul continuous_id))

lemma norm_le_cAG_of_mem_Δ2 {w : ℂ} (hw : w ∈ Δ2) : ‖w‖ ≤ cAG := by
  -- Use `∑_{j} (Re(ω^j w))^2 = (3/2) ‖w‖^2`, `∑_j Re(ω^j w) = 0`, and `Re(ω^j w) ≥ -cAG/2`!
  set x0 := (ω ^ (0 : ℕ) * w).re
  set x1 := (ω ^ (1 : ℕ) * w).re
  set x2 := (ω ^ (2 : ℕ) * w).re
  have hx0 : -(cAG / 2) ≤ x0 := hw 0
  have hx1 : -(cAG / 2) ≤ x1 := hw 1
  have hx2 : -(cAG / 2) ≤ x2 := hw 2
  have hsum : x0 + x1 + x2 = 0 := by
    have h012 : (ω ^ (0 : ℕ) * w + ω ^ (1 : ℕ) * w + ω ^ (2 : ℕ) * w : ℂ) = 0 := by
      simp only [pow_zero, pow_one]; linear_combination w * ω_sq_add_ω_add_one
    have := congrArg Complex.re h012
    simpa [x0, x1, x2] using this
  have hsq : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 = (3 / 2) * ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hx0' : x0 = w.re := by simp [x0]
    have hx1' : x1 = -(1 / 2) * w.re - (Real.sqrt 3 / 2) * w.im := by
      simp only [x1, pow_one, mul_re, ω_re, ω_im]; ring
    have hx2' : x2 = -(1 / 2) * w.re + (Real.sqrt 3 / 2) * w.im := by
      simp only [x2, ω_sq, mul_re]; ring
    rw [hx0', hx1', hx2']; nlinarith [sq_sqrt3]
  set y0 := x0 + cAG / 2
  set y1 := x1 + cAG / 2
  set y2 := x2 + cAG / 2
  have hy0 : 0 ≤ y0 := by simp only [y0]; linarith
  have hy1 : 0 ≤ y1 := by simp only [y1]; linarith
  have hy2 : 0 ≤ y2 := by simp only [y2]; linarith
  have hle : y0 ^ 2 + y1 ^ 2 + y2 ^ 2 ≤ (y0 + y1 + y2) ^ 2 := by nlinarith
  have hysum : y0 + y1 + y2 = 3 * (cAG / 2) := by simp only [y0, y1, y2]; linarith
  have hysq : y0 ^ 2 + y1 ^ 2 + y2 ^ 2 = (3 / 2) * ‖w‖ ^ 2 + 3 * (cAG / 2) ^ 2 := by
    simp only [y0, y1, y2]; nlinarith [hsum, hsq]
  rw [hysum, hysq] at hle
  have hnorm2 : ‖w‖ ^ 2 ≤ cAG ^ 2 := by nlinarith
  nlinarith [norm_nonneg w, cAG_pos]

lemma isBounded_Δ2Open : Bornology.IsBounded Δ2Open := by
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := cAG)).subset fun w hw => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_cAG_of_mem_Δ2 fun j => (hw j).le

lemma smul_mem_Δ2Open_of_mem_Δ2 {w : ℂ} (hw : w ∈ Δ2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (t : ℂ) * w ∈ Δ2Open := by
  intro j
  have hmul : ω ^ (j : ℕ) * ((t : ℂ) * w) = (t : ℂ) * (ω ^ (j : ℕ) * w) := by ring
  rw [hmul, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  nlinarith [hw j, cAG_pos]

lemma smul_mem_Δ2 {w : ℂ} (hw : w ∈ Δ2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : ℂ) * w ∈ Δ2 := by
  rcases eq_or_lt_of_le ht1 with rfl | hlt
  · simpa using hw
  · exact fun j => (smul_mem_Δ2Open_of_mem_Δ2 hw ht0 hlt j).le

lemma closure_Δ2Open : closure Δ2Open = Δ2 := by
  apply Subset.antisymm
  · exact isClosed_Δ2.closure_subset_iff.mpr fun _ h j => (h j).le
  · intro w hw
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, ht0, ht1, hdist⟩ : ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ (1 - t) * ‖w‖ < ε := by
      refine ⟨1 - min (1 / 2) (ε / (2 * (‖w‖ + 1))), ?_, ?_, ?_⟩
      · have : min (1 / 2) (ε / (2 * (‖w‖ + 1))) ≤ 1 / 2 := min_le_left _ _; linarith
      · have : 0 < min (1 / 2) (ε / (2 * (‖w‖ + 1))) := lt_min (by norm_num) (by positivity)
        linarith
      · have hle : min (1 / 2) (ε / (2 * (‖w‖ + 1))) ≤ ε / (2 * (‖w‖ + 1)) := min_le_right _ _
        have hpos : 0 < 2 * (‖w‖ + 1) := by positivity
        have h1 : (1 - (1 - min (1 / 2) (ε / (2 * (‖w‖ + 1))))) * ‖w‖ ≤
            (ε / (2 * (‖w‖ + 1))) * ‖w‖ := by
          rw [sub_sub_cancel]; exact mul_le_mul_of_nonneg_right hle (norm_nonneg w)
        have h2 : (ε / (2 * (‖w‖ + 1))) * ‖w‖ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]; nlinarith [norm_nonneg w]
        linarith
    refine ⟨(t : ℂ) * w, smul_mem_Δ2Open_of_mem_Δ2 hw ht0 ht1, ?_⟩
    rw [dist_eq_norm, show w - (t : ℂ) * w = ((1 - t : ℝ) : ℂ) * w by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact hdist

lemma interior_Δ2 : interior Δ2 = Δ2Open := by
  apply Subset.antisymm
  · intro w hw j
    have hmem : w ∈ Δ2 := interior_subset hw
    by_contra hle
    push Not at hle
    have heq : (ω ^ (j : ℕ) * w).re = -(cAG / 2) := le_antisymm hle (hmem j)
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hw
    obtain ⟨δ, hδ, hball⟩ := hw
    set w' : ℂ := w - ((δ / 2 : ℝ) : ℂ) * starRingEnd ℂ (ω ^ (j : ℕ))
    have hw'_ball : w' ∈ ball w δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : w' - w = -(((δ / 2 : ℝ) : ℂ) * starRingEnd ℂ (ω ^ (j : ℕ))) := by simp [w']
      rw [this, norm_neg, norm_mul, Complex.norm_real, RCLike.norm_conj, norm_ω_pow, mul_one,
        Real.norm_of_nonneg (by linarith)]
      linarith
    have hw'_ineq := (hball hw'_ball) j
    have hmul : ω ^ (j : ℕ) * w' = ω ^ (j : ℕ) * w - ((δ / 2 : ℝ) : ℂ) := by
      simp only [w', mul_sub]
      have h1 : ω ^ (j : ℕ) * starRingEnd ℂ (ω ^ (j : ℕ)) = 1 := by
        rw [Complex.mul_conj, ← Complex.sq_norm, norm_ω_pow]; norm_num
      calc ω ^ (j : ℕ) * w - ω ^ (j : ℕ) * (((δ / 2 : ℝ) : ℂ) * starRingEnd ℂ (ω ^ (j : ℕ)))
          = ω ^ (j : ℕ) * w - ((δ / 2 : ℝ) : ℂ) * (ω ^ (j : ℕ) * starRingEnd ℂ (ω ^ (j : ℕ))) := by
              ring
        _ = ω ^ (j : ℕ) * w - ((δ / 2 : ℝ) : ℂ) := by rw [h1, mul_one]
    rw [hmul, sub_re, ofReal_re, heq] at hw'_ineq
    linarith
  · exact interior_maximal (fun _ h j => (h j).le) isOpen_Δ2Open

lemma frontier_Δ2Open : frontier Δ2Open = Δ2 \ Δ2Open := by
  rw [frontier, closure_Δ2Open, isOpen_Δ2Open.interior_eq]

end

end BlochAG

/- ==================== Bloch_Part2A.lean ==================== -/
/-
# Ahlfors-Grunsky Proof — Part 2A: Euler Integrals, Hypergeometric ODE, and Maps `u6`, `u3`
-/

namespace BlochAG

open Complex Metric Set Filter Topology Real MeasureTheory intervalIntegral

noncomputable section

/- ## 1. Slit Domain and Elementary `cpow` Helpers -/

def slitSet : Set ℂ := {ξ : ℂ | ¬ (1 ≤ ξ.re ∧ ξ.im = 0)}

lemma isOpen_slitSet : IsOpen slitSet := by
  have h : slitSet = ({ξ : ℂ | 1 ≤ ξ.re} ∩ {ξ : ℂ | ξ.im = 0})ᶜ := rfl
  rw [h]
  exact ((isClosed_Ici.preimage Complex.continuous_re).inter
    (isClosed_singleton.preimage Complex.continuous_im)).isOpen_compl

lemma zero_mem_slitSet : (0 : ℂ) ∈ slitSet := by
  simp [slitSet]

lemma ball_subset_slitSet : ball (0 : ℂ) 1 ⊆ slitSet := by
  intro ξ hξ ⟨hre, _⟩
  have h1 : ‖ξ‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hξ
  linarith [Complex.re_le_norm ξ]

lemma slitSet_conj {ξ : ℂ} (hξ : ξ ∈ slitSet) : starRingEnd ℂ ξ ∈ slitSet := by
  intro ⟨hre, him⟩
  exact hξ ⟨by simpa using hre, by simpa using him⟩

lemma one_sub_mul_mem_slitPlane {ξ : ℂ} (hξ : ξ ∈ slitSet) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 - ξ * (t : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : ξ.im = 0
  · left
    have hre : ξ.re < 1 := by
      by_contra h
      push Not at h
      exact hξ ⟨h, him⟩
    simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    by_cases hre0 : ξ.re ≤ 0
    · nlinarith
    · push Not at hre0; nlinarith
  · rcases eq_or_lt_of_le ht0 with rfl | htpos
    · left; simp
    · right
      simp only [sub_im, one_im, mul_im, ofReal_re, ofReal_im, mul_zero, zero_add, zero_sub,
        neg_ne_zero]
      exact mul_ne_zero him htpos.ne'

lemma one_sub_mul_re_pos_of_norm_le_one {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < (1 - ξ * (t : ℂ)).re := by
  simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  have hre : ξ.re ≤ 1 := (Complex.re_le_norm ξ).trans hξ
  nlinarith

lemma one_sub_mul_norm_ge {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {t : ℝ} (ht0 : 0 ≤ t) :
    1 - t ≤ ‖1 - ξ * (t : ℂ)‖ := by
  calc 1 - t = ‖(1 : ℂ)‖ - ‖(t : ℂ)‖ := by
        rw [norm_one, Complex.norm_real, Real.norm_of_nonneg ht0]
    _ ≤ ‖(1 : ℂ)‖ - ‖ξ * (t : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
        nlinarith [norm_nonneg ξ]
    _ ≤ ‖(1 : ℂ) - ξ * (t : ℂ)‖ := norm_sub_norm_le 1 (ξ * (t : ℂ))

lemma norm_cpow_ofReal_exp {w : ℂ} (hw : w ≠ 0) (r : ℝ) :
    ‖w ^ (r : ℂ)‖ = ‖w‖ ^ r := by
  rw [Complex.norm_cpow_of_ne_zero hw]
  simp

lemma cpow_ofReal_exp_re {w : ℂ} (hw : w ≠ 0) (r : ℝ) :
    (w ^ (r : ℂ)).re = ‖w‖ ^ r * Real.cos (r * Complex.arg w) := by
  rw [Complex.cpow_def_of_ne_zero hw, Complex.exp_re]
  simp only [mul_re, Complex.log_re, Complex.log_im, ofReal_re, ofReal_im, mul_zero, sub_zero,
    mul_im, zero_add]
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hw), mul_comm (Real.log ‖w‖) r, mul_comm (Complex.arg w) r]

lemma cpow_ofReal_exp_re_ge {w : ℂ} (hw : 0 < w.re) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ‖w‖ ^ (-a) * Real.cos (a * (Real.pi / 2)) ≤ (w ^ ((-a : ℝ) : ℂ)).re := by
  have hw0 : w ≠ 0 := by intro h; rw [h, zero_re] at hw; linarith
  rw [cpow_ofReal_exp_re hw0 (-a), neg_mul, Real.cos_neg]
  have harg : |Complex.arg w| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have hle1 : |a * Complex.arg w| ≤ a * (Real.pi / 2) := by
    rw [abs_mul, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left harg.le ha0
  have hle2 : a * (Real.pi / 2) ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcos : Real.cos (a * (Real.pi / 2)) ≤ Real.cos (a * Complex.arg w) := by
    rw [← Real.cos_abs (a * Complex.arg w)]
    exact Real.strictAntiOn_cos.antitoneOn ⟨abs_nonneg _, hle1.trans hle2⟩
      ⟨by positivity, hle2⟩ hle1
  exact mul_le_mul_of_nonneg_left hcos (Real.rpow_nonneg (norm_nonneg w) (-a))

lemma exists_ball_norm_lower_bound {ξ₀ : ℂ} (hξ₀ : ξ₀ ∈ slitSet) :
    ∃ δ > 0, ∃ m > 0, closedBall ξ₀ δ ⊆ slitSet ∧
      ∀ ξ ∈ closedBall ξ₀ δ, ∀ t ∈ Icc (0 : ℝ) 1, m ≤ ‖1 - ξ * (t : ℂ)‖ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_slitSet ξ₀ hξ₀
  refine ⟨r / 2, half_pos hr, ?_⟩
  have hsub : closedBall ξ₀ (r / 2) ⊆ slitSet :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hcomp : IsCompact (closedBall ξ₀ (r / 2) ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall ξ₀ (r / 2)).prod isCompact_Icc
  have hne : (closedBall ξ₀ (r / 2) ×ˢ Icc (0 : ℝ) 1).Nonempty :=
    ⟨(ξ₀, 0), mem_closedBall_self (half_pos hr).le, left_mem_Icc.mpr zero_le_one⟩
  have hcont : ContinuousOn (fun p : ℂ × ℝ => ‖1 - p.1 * (p.2 : ℂ)‖)
      (closedBall ξ₀ (r / 2) ×ˢ Icc (0 : ℝ) 1) :=
    ((continuous_const.sub (continuous_fst.mul (Complex.continuous_ofReal.comp continuous_snd))).norm).continuousOn
  obtain ⟨⟨ξm, tm⟩, hmem, hmin⟩ := hcomp.exists_isMinOn hne hcont
  have hm_pos : 0 < ‖1 - ξm * (tm : ℂ)‖ :=
    norm_pos_iff.mpr (Complex.slitPlane_ne_zero (one_sub_mul_mem_slitPlane (hsub hmem.1) hmem.2.1 hmem.2.2))
  exact ⟨‖1 - ξm * (tm : ℂ)‖, hm_pos, hsub, fun ξ hξ t ht => hmin (show (ξ, t) ∈ _ from ⟨hξ, ht⟩)⟩

/- ## 2. General Euler Integral -/

def eulerIntegrand (a b c : ℝ) (ξ : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ ((b - 1 : ℝ) : ℂ) * (1 - (t : ℂ)) ^ ((c - b - 1 : ℝ) : ℂ) *
    (1 - ξ * (t : ℂ)) ^ ((-a : ℝ) : ℂ)

def eulerInt (a b c : ℝ) (ξ : ℂ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..1, eulerIntegrand a b c ξ t

lemma betaWeight_integrable {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    IntervalIntegrable (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (d - 1)) volume 0 1 := by
  have h := Complex.betaIntegral_convergent (u := (b : ℂ)) (v := (d : ℂ))
    (by simpa using hb) (by simpa using hd)
  have hnorm := h.norm
  refine hnorm.congr_ae ?_
  change ∀ᵐ t ∂(volume.restrict (uIoc 0 1)), _
  rw [ae_restrict_iff' measurableSet_uIoc]
  have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by
    rw [ae_iff]; simp
  filter_upwards [hne1] with t htne1 ht
  rw [uIoc_of_le zero_le_one] at ht
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 htne1
  simp only [norm_mul]
  rw [show (b : ℂ) - 1 = ((b - 1 : ℝ) : ℂ) by push_cast; rfl,
    show (d : ℂ) - 1 = ((d - 1 : ℝ) : ℂ) by push_cast; rfl,
    show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp

lemma eulerIntegrand_aestronglyMeasurable (a b c : ℝ) (ξ : ℂ) :
    AEStronglyMeasurable (eulerIntegrand a b c ξ) (volume.restrict (uIoc 0 1)) := by
  have hmeas : Measurable (eulerIntegrand a b c ξ) := by
    unfold eulerIntegrand
    have h1 : Measurable (fun t : ℝ => (t : ℂ) ^ ((b - 1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.pow_const _
    have h2 : Measurable (fun t : ℝ => (1 - (t : ℂ)) ^ ((c - b - 1 : ℝ) : ℂ)) :=
      (measurable_const.sub Complex.continuous_ofReal.measurable).pow_const _
    have h3 : Measurable (fun t : ℝ => (1 - ξ * (t : ℂ)) ^ ((-a : ℝ) : ℂ)) :=
      (measurable_const.sub (measurable_const.mul Complex.continuous_ofReal.measurable)).pow_const _
    exact (h1.mul h2).mul h3
  exact hmeas.aestronglyMeasurable

lemma continuousAt_cpow_const_comp {α : Type*} [TopologicalSpace α] {g : α → ℂ} {x : α} {c : ℂ}
    (hg : ContinuousAt g x) (hslit : g x ∈ Complex.slitPlane) :
    ContinuousAt (fun y => g y ^ c) x :=
  ((Complex.hasStrictDerivAt_cpow_const (c := c) hslit).hasDerivAt.continuousAt).comp hg

lemma eulerIntegrand_integrable_of_slitSet {a b c : ℝ} (hb : 0 < b) (hcb : 0 < c - b)
    {ξ : ℂ} (hξ : ξ ∈ slitSet) :
    IntervalIntegrable (eulerIntegrand a b c ξ) volume 0 1 := by
  have hcont : ContinuousOn (fun t : ℝ => (1 - ξ * (t : ℂ)) ^ ((-a : ℝ) : ℂ)) (Icc 0 1) := by
    intro t ht
    exact (continuousAt_cpow_const_comp (g := fun t : ℝ => (1 : ℂ) - ξ * (t : ℂ))
      (by fun_prop) (one_sub_mul_mem_slitPlane hξ ht.1 ht.2)).continuousWithinAt
  have hbeta := Complex.betaIntegral_convergent (u := (b : ℂ)) (v := ((c - b : ℝ) : ℂ))
    (by simpa using hb) (by simpa using hcb)
  have hmul := hbeta.mul_continuousOn (by rwa [uIcc_of_le zero_le_one])
  refine hmul.congr_ae ?_
  change ∀ᵐ t ∂(volume.restrict (uIoc 0 1)), _
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards with t _
  simp only [eulerIntegrand]
  congr 1
  congr 1 <;> · push_cast; ring

lemma eulerInt_hasDerivAt {a b c : ℝ} (hb : 0 < b) (hcb : 0 < c - b)
    {ξ₀ : ℂ} (hξ₀ : ξ₀ ∈ slitSet) :
    HasDerivAt (eulerInt a b c) ((a : ℂ) * eulerInt (a + 1) (b + 1) (c + 1) ξ₀) ξ₀ := by
  obtain ⟨δ, hδ, _m, _hm, hsub, _hlow⟩ := exists_ball_norm_lower_bound hξ₀
  have hM : ∃ M : ℝ, 0 < M ∧ ∀ ξ ∈ closedBall ξ₀ δ, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(1 - ξ * (t : ℂ)) ^ ((-(a + 1) : ℝ) : ℂ)‖ ≤ M := by
    have hcomp : IsCompact (closedBall ξ₀ δ ×ˢ Icc (0 : ℝ) 1) :=
      (isCompact_closedBall ξ₀ δ).prod isCompact_Icc
    have hcont : ContinuousOn (fun p : ℂ × ℝ => ‖(1 - p.1 * (p.2 : ℂ)) ^ ((-(a + 1) : ℝ) : ℂ)‖)
        (closedBall ξ₀ δ ×ˢ Icc (0 : ℝ) 1) := by
      intro ⟨ξ, t⟩ ⟨hξ, ht⟩
      exact (continuousAt_cpow_const_comp (g := fun p : ℂ × ℝ => (1 : ℂ) - p.1 * (p.2 : ℂ))
        (by fun_prop) (one_sub_mul_mem_slitPlane (hsub hξ) ht.1 ht.2)).norm.continuousWithinAt
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont
    refine ⟨max C 1, by positivity, fun ξ hξ t ht => ?_⟩
    have h1 := hC (ξ, t) ⟨hξ, ht⟩
    rw [Real.norm_of_nonneg (norm_nonneg _)] at h1
    exact h1.trans (le_max_left _ _)
  obtain ⟨M, _hMpos, hMle⟩ := hM
  let F : ℂ → ℝ → ℂ := fun ξ t => eulerIntegrand a b c ξ t
  let F' : ℂ → ℝ → ℂ := fun ξ t => (a : ℂ) * eulerIntegrand (a + 1) (b + 1) (c + 1) ξ t
  let bound : ℝ → ℝ := fun t => (|a| * M) * (t ^ (b - 1) * (1 - t) ^ (c - b - 1))
  have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by rw [ae_iff]; simp
  have hdiff_res := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1) (F := F) (F' := F') (x₀ := ξ₀) (s := closedBall ξ₀ δ)
    (bound := bound)
    (closedBall_mem_nhds ξ₀ hδ)
    (Eventually.of_forall fun ξ => eulerIntegrand_aestronglyMeasurable a b c ξ)
    (eulerIntegrand_integrable_of_slitSet hb hcb hξ₀)
    ((eulerIntegrand_aestronglyMeasurable (a + 1) (b + 1) (c + 1) ξ₀).const_mul (a : ℂ))
    ?_
    ((betaWeight_integrable hb hcb).const_mul (|a| * M))
    ?_
  · have h2 := hdiff_res.2
    simp only [F, F'] at h2
    rw [intervalIntegral.integral_const_mul] at h2
    exact h2
  · filter_upwards [hne1] with t htne1 ht ξ hξ
    rw [uIoc_of_le zero_le_one] at ht
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 htne1
    simp only [F', eulerIntegrand, bound, norm_mul]
    have h1 : ‖(t : ℂ) ^ ((b + 1 - 1 : ℝ) : ℂ)‖ = t ^ b := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1]; simp
    have h2 : ‖(1 - (t : ℂ)) ^ ((c + 1 - (b + 1) - 1 : ℝ) : ℂ)‖ = (1 - t) ^ (c - b - 1) := by
      rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      simp only [ofReal_re]
      congr 1; ring
    have htb : t ^ b ≤ t ^ (b - 1) := by
      have heq : t ^ b = t ^ (b - 1) * t := by
        rw [show b = (b - 1) + 1 by ring, Real.rpow_add ht.1, Real.rpow_one]
        congr 1; ring
      rw [heq]
      exact mul_le_of_le_one_right (Real.rpow_nonneg ht.1.le _) ht1.le
    rw [h1, h2, Complex.norm_real, Real.norm_eq_abs]
    have h3 := hMle ξ hξ t ⟨ht.1.le, ht1.le⟩
    have hnn1 : 0 ≤ t ^ (b - 1) := Real.rpow_nonneg ht.1.le _
    have hnn2 : 0 ≤ (1 - t) ^ (c - b - 1) := Real.rpow_nonneg (by linarith) _
    calc |a| * (t ^ b * (1 - t) ^ (c - b - 1) * ‖(1 - ξ * (t : ℂ)) ^ ((-(a + 1) : ℝ) : ℂ)‖)
        ≤ |a| * (t ^ (b - 1) * (1 - t) ^ (c - b - 1) * M) := by gcongr
      _ = |a| * M * (t ^ (b - 1) * (1 - t) ^ (c - b - 1)) := by ring
  · filter_upwards with t ht ξ hξ
    rw [uIoc_of_le zero_le_one] at ht
    have hslit := one_sub_mul_mem_slitPlane (hsub hξ) ht.1.le ht.2
    have hinner : HasDerivAt (fun x : ℂ => 1 - x * (t : ℂ)) (-(t : ℂ)) ξ := by
      simpa using ((hasDerivAt_id ξ).mul_const (t : ℂ)).const_sub 1
    have hcpow := hinner.cpow_const (c := ((-a : ℝ) : ℂ)) hslit
    have hfull := hcpow.const_mul ((t : ℂ) ^ ((b - 1 : ℝ) : ℂ) * (1 - (t : ℂ)) ^ ((c - b - 1 : ℝ) : ℂ))
    refine hfull.congr_deriv ?_
    simp only [F', eulerIntegrand]
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have htb : (t : ℂ) ^ ((b + 1 - 1 : ℝ) : ℂ) = (t : ℂ) ^ ((b - 1 : ℝ) : ℂ) * (t : ℂ) := by
      rw [show ((b + 1 - 1 : ℝ) : ℂ) = ((b - 1 : ℝ) : ℂ) + 1 by push_cast; ring,
        Complex.cpow_add _ _ ht0, Complex.cpow_one]
    have hcb_eq : ((c + 1 - (b + 1) - 1 : ℝ) : ℂ) = ((c - b - 1 : ℝ) : ℂ) := by push_cast; ring
    have ha_eq : ((-a : ℝ) : ℂ) - 1 = ((-(a + 1) : ℝ) : ℂ) := by push_cast; ring
    rw [htb, hcb_eq, ha_eq]
    push_cast; ring

lemma eulerInt_differentiableOn {a b c : ℝ} (hb : 0 < b) (hcb : 0 < c - b) :
    DifferentiableOn ℂ (eulerInt a b c) slitSet := fun _ hξ =>
  (eulerInt_hasDerivAt hb hcb hξ).differentiableAt.differentiableWithinAt

lemma eulerInt_deriv {a b c : ℝ} (hb : 0 < b) (hcb : 0 < c - b) {ξ : ℂ} (hξ : ξ ∈ slitSet) :
    deriv (eulerInt a b c) ξ = (a : ℂ) * eulerInt (a + 1) (b + 1) (c + 1) ξ :=
  (eulerInt_hasDerivAt hb hcb hξ).deriv

lemma eulerInt_hasDerivAt_deriv {a b c : ℝ} (hb : 0 < b) (hcb : 0 < c - b)
    {ξ : ℂ} (hξ : ξ ∈ slitSet) :
    HasDerivAt (deriv (eulerInt a b c))
      ((a : ℂ) * ((a + 1 : ℝ) : ℂ) * eulerInt (a + 2) (b + 2) (c + 2) ξ) ξ := by
  have heq : deriv (eulerInt a b c) =ᶠ[𝓝 ξ]
      fun x => (a : ℂ) * eulerInt (a + 1) (b + 1) (c + 1) x := by
    filter_upwards [isOpen_slitSet.mem_nhds hξ] with x hx
    exact eulerInt_deriv hb hcb hx
  have hd := (eulerInt_hasDerivAt (a := a + 1) (b := b + 1) (c := c + 1)
    (by linarith) (by linarith) hξ).const_mul (a : ℂ)
  have h1 : eulerInt (a + 1 + 1) (b + 1 + 1) (c + 1 + 1) ξ =
      eulerInt (a + 2) (b + 2) (c + 2) ξ := by ring_nf
  rw [h1, ← mul_assoc] at hd
  exact hd.congr_of_eventuallyEq heq

lemma eulerInt_second_deriv {a b c : ℝ} (hb : 0 < b) (hcb : 0 < c - b)
    {ξ : ℂ} (hξ : ξ ∈ slitSet) :
    deriv (deriv (eulerInt a b c)) ξ =
      (a : ℂ) * ((a + 1 : ℝ) : ℂ) * eulerInt (a + 2) (b + 2) (c + 2) ξ :=
  (eulerInt_hasDerivAt_deriv hb hcb hξ).deriv

/- ## 3. Gauss Hypergeometric ODE for `eulerInt` -/

lemma eulerInt_hypergeom_ode {a b c : ℝ} (hb : 0 < b) (hcb : 0 < c - b)
    {ξ : ℂ} (hξ : ξ ∈ slitSet) :
    ξ * (1 - ξ) * deriv (deriv (eulerInt a b c)) ξ +
      ((c : ℂ) - ((a + b + 1 : ℝ) : ℂ) * ξ) * deriv (eulerInt a b c) ξ -
      (a : ℂ) * (b : ℂ) * eulerInt a b c ξ = 0 := by
  rw [eulerInt_second_deriv hb hcb hξ, eulerInt_deriv hb hcb hξ]
  have hint0 := eulerIntegrand_integrable_of_slitSet (a := a) hb hcb hξ
  have hint1 := eulerIntegrand_integrable_of_slitSet (a := a + 1) (b := b + 1) (c := c + 1)
    (by linarith) (by linarith) hξ
  have hint2 := eulerIntegrand_integrable_of_slitSet (a := a + 2) (b := b + 2) (c := c + 2)
    (by linarith) (by linarith) hξ
  unfold eulerInt
  set C2 : ℂ := ξ * (1 - ξ) * ((a : ℂ) * ((a + 1 : ℝ) : ℂ))
  set C1 : ℂ := ((c : ℂ) - ((a + b + 1 : ℝ) : ℂ) * ξ) * (a : ℂ)
  set C0 : ℂ := (a : ℂ) * (b : ℂ)
  have hcomb :
      ξ * (1 - ξ) * ((a : ℂ) * ((a + 1 : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1, eulerIntegrand (a + 2) (b + 2) (c + 2) ξ t) +
        ((c : ℂ) - ((a + b + 1 : ℝ) : ℂ) * ξ) * ((a : ℂ) * ∫ t in (0 : ℝ)..1, eulerIntegrand (a + 1) (b + 1) (c + 1) ξ t) -
        (a : ℂ) * (b : ℂ) * ∫ t in (0 : ℝ)..1, eulerIntegrand a b c ξ t =
      ∫ t in (0 : ℝ)..1, (C2 * eulerIntegrand (a + 2) (b + 2) (c + 2) ξ t +
        C1 * eulerIntegrand (a + 1) (b + 1) (c + 1) ξ t - C0 * eulerIntegrand a b c ξ t) := by
    rw [intervalIntegral.integral_sub ((hint2.const_mul C2).add (hint1.const_mul C1)) (hint0.const_mul C0),
      intervalIntegral.integral_add (hint2.const_mul C2) (hint1.const_mul C1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    simp only [C2, C1, C0]; ring
  rw [hcomb]
  -- Exact antiderivative: `G(t) = -a * t^b * (1 - t)^(c - b) * (1 - ξ * t)^(-a - 1)`!
  let G : ℝ → ℂ := fun t =>
    -(a : ℂ) * ((t : ℂ) ^ (b : ℂ) * (1 - (t : ℂ)) ^ ((c - b : ℝ) : ℂ) *
      (1 - ξ * (t : ℂ)) ^ ((-(a + 1) : ℝ) : ℂ))
  have hG_deriv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt G (C2 * eulerIntegrand (a + 2) (b + 2) (c + 2) ξ t +
        C1 * eulerIntegrand (a + 1) (b + 1) (c + 1) ξ t - C0 * eulerIntegrand a b c ξ t) t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have h1t0 : (1 - (t : ℂ)) ≠ 0 := by
      rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.ofReal_ne_zero.mpr (by linarith [ht.2])
    have hslit_t : (t : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr ht.1
    have hslit_1t : 1 - (t : ℂ) ∈ Complex.slitPlane := by
      rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.2])
    have hslit_ξt : 1 - ξ * (t : ℂ) ∈ Complex.slitPlane :=
      one_sub_mul_mem_slitPlane hξ ht.1.le ht.2.le
    have hξt0 : 1 - ξ * (t : ℂ) ≠ 0 := Complex.slitPlane_ne_zero hslit_ξt
    have hd1 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (b : ℂ))
        ((b : ℂ) * (t : ℂ) ^ ((b : ℂ) - 1)) t := by
      simpa using (Complex.hasStrictDerivAt_cpow_const (c := (b : ℂ)) hslit_t).hasDerivAt.comp_ofReal
    have hd2 : HasDerivAt (fun x : ℝ => (1 - (x : ℂ)) ^ ((c - b : ℝ) : ℂ))
        (((c - b : ℝ) : ℂ) * (1 - (t : ℂ)) ^ (((c - b : ℝ) : ℂ) - 1) * (-1)) t := by
      have hinner : HasDerivAt (fun x : ℝ => (1 : ℂ) - (x : ℂ)) (-1) t :=
        (Complex.ofRealCLM.hasDerivAt (x := t)).const_sub 1
      have hc := (Complex.hasStrictDerivAt_cpow_const (c := ((c - b : ℝ) : ℂ)) hslit_1t).hasDerivAt
      simpa only [Function.comp_def, smul_eq_mul, mul_comm] using hc.scomp t hinner
    have hd3 : HasDerivAt (fun x : ℝ => (1 - ξ * (x : ℂ)) ^ ((-(a + 1) : ℝ) : ℂ))
        (((-(a + 1) : ℝ) : ℂ) * (1 - ξ * (t : ℂ)) ^ (((-(a + 1) : ℝ) : ℂ) - 1) * (-ξ)) t := by
      have hinner : HasDerivAt (fun x : ℝ => (1 : ℂ) - ξ * (x : ℂ)) (-ξ) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul ξ).const_sub 1
      have hc := (Complex.hasStrictDerivAt_cpow_const (c := ((-(a + 1) : ℝ) : ℂ)) hslit_ξt).hasDerivAt
      simpa only [Function.comp_def, smul_eq_mul, mul_comm] using hc.scomp t hinner
    have hprod := ((hd1.mul hd2).mul hd3).const_mul (-(a : ℂ))
    refine hprod.congr_deriv ?_
    set P1 : ℂ := (t : ℂ) ^ ((b - 1 : ℝ) : ℂ)
    set P2 : ℂ := (1 - (t : ℂ)) ^ ((c - b - 1 : ℝ) : ℂ)
    set P3 : ℂ := (1 - ξ * (t : ℂ)) ^ ((-(a + 2) : ℝ) : ℂ)
    have htb : (t : ℂ) ^ (b : ℂ) = P1 * (t : ℂ) := by
      simp only [P1]
      rw [show (b : ℂ) = ((b - 1 : ℝ) : ℂ) + 1 by push_cast; ring, Complex.cpow_add _ _ ht0,
        Complex.cpow_one]
    have htb1 : (t : ℂ) ^ ((b + 1 - 1 : ℝ) : ℂ) = P1 * (t : ℂ) := by
      simp only [P1]
      rw [show ((b + 1 - 1 : ℝ) : ℂ) = ((b - 1 : ℝ) : ℂ) + 1 by push_cast; ring,
        Complex.cpow_add _ _ ht0, Complex.cpow_one]
    have htb2 : (t : ℂ) ^ ((b + 2 - 1 : ℝ) : ℂ) = P1 * (t : ℂ) ^ 2 := by
      simp only [P1]
      rw [show ((b + 2 - 1 : ℝ) : ℂ) = ((b - 1 : ℝ) : ℂ) + 2 by push_cast; ring,
        Complex.cpow_add _ _ ht0, Complex.cpow_two]
    have h1tb : (1 - (t : ℂ)) ^ ((c - b : ℝ) : ℂ) = P2 * (1 - (t : ℂ)) := by
      simp only [P2]
      rw [show ((c - b : ℝ) : ℂ) = ((c - b - 1 : ℝ) : ℂ) + 1 by push_cast; ring,
        Complex.cpow_add _ _ h1t0, Complex.cpow_one]
    have hξa0 : (1 - ξ * (t : ℂ)) ^ ((-a : ℝ) : ℂ) = P3 * (1 - ξ * (t : ℂ)) ^ 2 := by
      simp only [P3]
      rw [show ((-a : ℝ) : ℂ) = ((-(a + 2) : ℝ) : ℂ) + 2 by push_cast; ring,
        Complex.cpow_add _ _ hξt0, Complex.cpow_two]
    have hξa1 : (1 - ξ * (t : ℂ)) ^ ((-(a + 1) : ℝ) : ℂ) = P3 * (1 - ξ * (t : ℂ)) := by
      simp only [P3]
      rw [show ((-(a + 1) : ℝ) : ℂ) = ((-(a + 2) : ℝ) : ℂ) + 1 by push_cast; ring,
        Complex.cpow_add _ _ hξt0, Complex.cpow_one]
    have he1 : (b : ℂ) - 1 = ((b - 1 : ℝ) : ℂ) := by push_cast; ring
    have he2 : ((c - b : ℝ) : ℂ) - 1 = ((c - b - 1 : ℝ) : ℂ) := by push_cast; ring
    have he3 : ((-(a + 1) : ℝ) : ℂ) - 1 = ((-(a + 2) : ℝ) : ℂ) := by push_cast; ring
    have he4 : ((c + 1 - (b + 1) - 1 : ℝ) : ℂ) = ((c - b - 1 : ℝ) : ℂ) := by push_cast; ring
    have he5 : ((c + 2 - (b + 2) - 1 : ℝ) : ℂ) = ((c - b - 1 : ℝ) : ℂ) := by push_cast; ring
    simp only [eulerIntegrand, C2, C1, C0, he1, he2, he3, he4, he5, Pi.mul_apply]
    rw [htb, htb1, htb2, h1tb, hξa0, hξa1]
    simp only [P1, P2, P3]
    push_cast; ring
  have hG_tendsto_0 : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (t : ℂ) ^ (b : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun z : ℂ => z ^ (b : ℂ)) 0 :=
        Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by simpa using hb)
      have h0 : ((0 : ℂ) ^ (b : ℂ)) = 0 := Complex.zero_cpow (by exact_mod_cast hb.ne')
      have hinner : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
        simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
      rw [← h0]
      exact (hc.tendsto.comp hinner).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t : ℝ => (1 - (t : ℂ)) ^ ((c - b : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hc : ContinuousAt (fun t : ℝ => (1 - (t : ℂ)) ^ ((c - b : ℝ) : ℂ)) 0 :=
        continuousAt_cpow_const_comp (by fun_prop) (by simp : (1 - ((0 : ℝ) : ℂ)) ∈ Complex.slitPlane)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun t : ℝ => (1 - ξ * (t : ℂ)) ^ ((-(a + 1) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hc : ContinuousAt (fun t : ℝ => (1 - ξ * (t : ℂ)) ^ ((-(a + 1) : ℝ) : ℂ)) 0 :=
        continuousAt_cpow_const_comp (by fun_prop) (by simp : (1 - ξ * ((0 : ℝ) : ℂ)) ∈ Complex.slitPlane)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa [G] using ((h1.mul h2).mul h3).const_mul (-(a : ℂ))
  have hG_tendsto_1 : Tendsto G (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (t : ℂ) ^ (b : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
      have hc : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (b : ℂ)) 1 :=
        continuousAt_cpow_const_comp (by fun_prop) (by simp : ((1 : ℝ) : ℂ) ∈ Complex.slitPlane)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t : ℝ => (1 - (t : ℂ)) ^ ((c - b : ℝ) : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun z : ℂ => z ^ ((c - b : ℝ) : ℂ)) 0 :=
        Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by simpa using hcb)
      have h0 : ((0 : ℂ) ^ ((c - b : ℝ) : ℂ)) = 0 := Complex.zero_cpow (by exact_mod_cast hcb.ne')
      have hinner : Tendsto (fun t : ℝ => (1 : ℂ) - (t : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (0 : ℂ)) := by
        simpa using (tendsto_const_nhds (x := (1 : ℂ))).sub (Complex.continuous_ofReal.tendsto (1 : ℝ))
      rw [← h0]
      exact (hc.tendsto.comp hinner).mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun t : ℝ => (1 - ξ * (t : ℂ)) ^ ((-(a + 1) : ℝ) : ℂ))
        (𝓝[<] (1 : ℝ)) (𝓝 ((1 - ξ) ^ ((-(a + 1) : ℝ) : ℂ))) := by
      have hslit1 : 1 - ξ * ((1 : ℝ) : ℂ) ∈ Complex.slitPlane :=
        one_sub_mul_mem_slitPlane hξ zero_le_one le_rfl
      have hc : ContinuousAt (fun t : ℝ => (1 - ξ * (t : ℂ)) ^ ((-(a + 1) : ℝ) : ℂ)) 1 :=
        continuousAt_cpow_const_comp (by fun_prop) hslit1
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa [G] using ((h1.mul h2).mul h3).const_mul (-(a : ℂ))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    hG_deriv ((hint2.const_mul C2).add (hint1.const_mul C1) |>.sub (hint0.const_mul C0))
    hG_tendsto_0 hG_tendsto_1
  simpa using hftc

/- ## 4. Continuity on `closedBall 0 1`, Values at `0` and `1`, Conjugation, Positivity -/

lemma eulerInt_continuousOn_closedBall {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hcba : 0 < c - b - a) :
    ContinuousOn (eulerInt a b c) (closedBall 0 1) := by
  have h1 : eulerInt a b c = fun ξ : ℂ =>
      ∫ t in Ioc (0 : ℝ) 1, eulerIntegrand a b c ξ t := funext fun ξ =>
    intervalIntegral.integral_of_le zero_le_one
  rw [h1]
  let bound : ℝ → ℝ := fun t => t ^ (b - 1) * (1 - t) ^ (c - b - a - 1)
  have hbound_int : Integrable bound (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have := betaWeight_integrable hb hcba
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
  have hne1 : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 1)), t ∈ Ioo (0 : ℝ) 1 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by rw [ae_iff]; simp
    filter_upwards [hne] with t htne ht
    exact ⟨ht.1, lt_of_le_of_ne ht.2 htne⟩
  refine MeasureTheory.continuousOn_of_dominated (bound := bound) ?_ ?_ hbound_int ?_
  · intro ξ _
    simpa [uIoc_of_le zero_le_one] using eulerIntegrand_aestronglyMeasurable a b c ξ
  · intro ξ hξ
    have hξ1 : ‖ξ‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hξ
    filter_upwards [hne1] with t ht
    simp only [eulerIntegrand, bound, norm_mul]
    have h1t : 0 < 1 - t := by linarith [ht.2]
    have hξt_ne : 1 - ξ * (t : ℂ) ≠ 0 := by
      have hre := one_sub_mul_re_pos_of_norm_le_one hξ1 ht.1.le ht.2
      intro h; rw [h, zero_re] at hre; linarith
    have hn1 : ‖(t : ℂ) ^ ((b - 1 : ℝ) : ℂ)‖ = t ^ (b - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1]; simp
    have hn2 : ‖(1 - (t : ℂ)) ^ ((c - b - 1 : ℝ) : ℂ)‖ = (1 - t) ^ (c - b - 1) := by
      rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos h1t]; simp
    have hn3 : ‖(1 - ξ * (t : ℂ)) ^ ((-a : ℝ) : ℂ)‖ ≤ (1 - t) ^ (-a) := by
      rw [norm_cpow_ofReal_exp hξt_ne (-a)]
      exact Real.rpow_le_rpow_of_nonpos h1t (one_sub_mul_norm_ge hξ1 ht.1.le) (by linarith)
    rw [hn1, hn2]
    have hrpow : (1 - t) ^ (c - b - 1) * (1 - t) ^ (-a) = (1 - t) ^ (c - b - a - 1) := by
      rw [← Real.rpow_add h1t]; congr 1; ring
    rw [← hrpow, ← mul_assoc]
    have hnn : 0 ≤ t ^ (b - 1) * (1 - t) ^ (c - b - 1) :=
      mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg h1t.le _)
    exact mul_le_mul_of_nonneg_left hn3 hnn
  · filter_upwards [hne1] with t ht
    intro ξ hξ
    have hξ1 : ‖ξ‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hξ
    have hslit : 1 - ξ * (t : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (one_sub_mul_re_pos_of_norm_le_one hξ1 ht.1.le ht.2))
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.const_mul ?_ _
    exact continuousAt_cpow_const_comp (g := fun x : ℂ => (1 : ℂ) - x * (t : ℂ))
      (by fun_prop) hslit

lemma eulerInt_zero (a b c : ℝ) :
    eulerInt a b c 0 = Complex.betaIntegral (b : ℂ) ((c - b : ℝ) : ℂ) := by
  unfold eulerInt Complex.betaIntegral
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [eulerIntegrand, zero_mul, sub_zero, Complex.one_cpow, mul_one]
  congr 1 <;> · push_cast; ring

lemma eulerInt_one (a b c : ℝ) :
    eulerInt a b c 1 = Complex.betaIntegral (b : ℂ) ((c - b - a : ℝ) : ℂ) := by
  unfold eulerInt Complex.betaIntegral
  refine intervalIntegral.integral_congr_ae ?_
  have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by rw [ae_iff]; simp
  filter_upwards [hne1] with t htne1 ht
  rw [uIoc_of_le zero_le_one] at ht
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 htne1
  have h1t : (1 : ℂ) - (t : ℂ) ≠ 0 := by
    rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  simp only [eulerIntegrand, one_mul, mul_assoc]
  congr 1
  · push_cast; ring
  · rw [← Complex.cpow_add _ _ h1t]
    congr 1; push_cast; ring

lemma eulerIntegrand_integrable_of_norm_le_one {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hcba : 0 < c - b - a) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) :
    IntervalIntegrable (eulerIntegrand a b c ξ) volume 0 1 := by
  have hbound := betaWeight_integrable hb hcba
  refine hbound.mono_fun' (eulerIntegrand_aestronglyMeasurable a b c ξ) ?_
  change ∀ᵐ t ∂(volume.restrict (uIoc 0 1)), _
  rw [ae_restrict_iff' measurableSet_uIoc]
  have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by rw [ae_iff]; simp
  filter_upwards [hne1] with t htne1 ht
  rw [uIoc_of_le zero_le_one] at ht
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 htne1
  have h1t : 0 < 1 - t := by linarith
  have hξt_ne : 1 - ξ * (t : ℂ) ≠ 0 := by
    have hre := one_sub_mul_re_pos_of_norm_le_one hξ ht.1.le ht1
    intro h; rw [h, zero_re] at hre; linarith
  simp only [eulerIntegrand, norm_mul]
  have hn1 : ‖(t : ℂ) ^ ((b - 1 : ℝ) : ℂ)‖ = t ^ (b - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1]; simp
  have hn2 : ‖(1 - (t : ℂ)) ^ ((c - b - 1 : ℝ) : ℂ)‖ = (1 - t) ^ (c - b - 1) := by
    rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos h1t]; simp
  have hn3 : ‖(1 - ξ * (t : ℂ)) ^ ((-a : ℝ) : ℂ)‖ ≤ (1 - t) ^ (-a) := by
    rw [norm_cpow_ofReal_exp hξt_ne (-a)]
    exact Real.rpow_le_rpow_of_nonpos h1t (one_sub_mul_norm_ge hξ ht.1.le) (by linarith)
  rw [hn1, hn2]
  have hrpow : (1 - t) ^ (c - b - 1) * (1 - t) ^ (-a) = (1 - t) ^ (c - b - a - 1) := by
    rw [← Real.rpow_add h1t]; congr 1; ring
  rw [← hrpow, ← mul_assoc]
  have hnn : 0 ≤ t ^ (b - 1) * (1 - t) ^ (c - b - 1) :=
    mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg h1t.le _)
  exact mul_le_mul_of_nonneg_left hn3 hnn

lemma eulerInt_conj {a b c : ℝ} {ξ : ℂ} (hξ : ξ ∈ slitSet ∨ ‖ξ‖ ≤ 1)
    (hint : IntervalIntegrable (eulerIntegrand a b c ξ) volume 0 1) :
    eulerInt a b c (starRingEnd ℂ ξ) = starRingEnd ℂ (eulerInt a b c ξ) := by
  unfold eulerInt
  rw [show starRingEnd ℂ (∫ t in (0 : ℝ)..1, eulerIntegrand a b c ξ t) =
      Complex.conjCLE.toContinuousLinearMap (∫ t in (0 : ℝ)..1, eulerIntegrand a b c ξ t) from rfl,
    ← Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hint]
  refine intervalIntegral.integral_congr_ae ?_
  have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by rw [ae_iff]; simp
  filter_upwards [hne1] with t htne1 ht
  rw [uIoc_of_le zero_le_one] at ht
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 htne1
  have h1t_pos : 0 < 1 - t := by linarith
  have hslit_ξt : 1 - ξ * (t : ℂ) ∈ Complex.slitPlane := by
    rcases hξ with hs | hn
    · exact one_sub_mul_mem_slitPlane hs ht.1.le ht.2
    · exact Complex.mem_slitPlane_iff.mpr (Or.inl (one_sub_mul_re_pos_of_norm_le_one hn ht.1.le ht1))
  have harg_ne : ∀ w : ℂ, w ∈ Complex.slitPlane → w.arg ≠ Real.pi := by
    intro w hw hpi
    rw [Complex.mem_slitPlane_iff] at hw
    have hre := Complex.arg_eq_pi_iff.mp hpi
    rcases hw with h | h
    · linarith [hre.1]
    · exact h hre.2
  simp only [eulerIntegrand, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul]
  congr 1
  · congr 1
    · have harg : ((t : ℂ)).arg ≠ Real.pi := harg_ne _ (Complex.ofReal_mem_slitPlane.mpr ht.1)
      have h := Complex.conj_cpow (t : ℂ) ((b - 1 : ℝ) : ℂ) harg
      simpa [Complex.conj_ofReal] using h
    · have harg : (1 - (t : ℂ)).arg ≠ Real.pi := by
        rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl]
        exact harg_ne _ (Complex.ofReal_mem_slitPlane.mpr h1t_pos)
      have h := Complex.conj_cpow (1 - (t : ℂ)) ((c - b - 1 : ℝ) : ℂ) harg
      simpa [Complex.conj_ofReal] using h
  · have h := Complex.conj_cpow (1 - ξ * (t : ℂ)) ((-a : ℝ) : ℂ) (harg_ne _ hslit_ξt)
    simpa [Complex.conj_ofReal] using h

lemma eulerInt_re_ge {a b c : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 < b) (hcba : 0 < c - b - a)
    {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) :
    Real.cos (a * (Real.pi / 2)) *
        ∫ t : ℝ in (0 : ℝ)..1, t ^ (b - 1) * (1 - t) ^ (c - b - 1) * ‖1 - ξ * (t : ℂ)‖ ^ (-a) ≤
      (eulerInt a b c ξ).re := by
  have hint := eulerIntegrand_integrable_of_norm_le_one ha0 hb hcba hξ
  have hre_eq : (eulerInt a b c ξ).re =
      ∫ t : ℝ in (0 : ℝ)..1, (eulerIntegrand a b c ξ t).re := by
    unfold eulerInt
    exact (Complex.reCLM.intervalIntegral_comp_comm hint).symm
  rw [hre_eq, ← intervalIntegral.integral_const_mul]
  have hint_re : IntervalIntegrable (fun t : ℝ => (eulerIntegrand a b c ξ t).re) volume 0 1 := by
    exact ⟨Complex.reCLM.integrable_comp hint.1, Complex.reCLM.integrable_comp hint.2⟩
  have hint_norm : IntervalIntegrable
      (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (c - b - 1) * ‖1 - ξ * (t : ℂ)‖ ^ (-a)) volume 0 1 := by
    refine hint.norm.congr_ae ?_
    change ∀ᵐ t ∂(volume.restrict (uIoc 0 1)), _
    rw [ae_restrict_iff' measurableSet_uIoc]
    have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by rw [ae_iff]; simp
    filter_upwards [hne1] with t htne1 ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 htne1
    have h1t : 0 < 1 - t := by linarith
    have hξt_ne : 1 - ξ * (t : ℂ) ≠ 0 := by
      have hre := one_sub_mul_re_pos_of_norm_le_one hξ ht.1.le ht1
      intro h; rw [h, zero_re] at hre; linarith
    simp only [eulerIntegrand, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1,
      show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos h1t, norm_cpow_ofReal_exp hξt_ne (-a)]
    simp
  refine intervalIntegral.integral_mono_ae_restrict zero_le_one
    (hint_norm.const_mul _) hint_re ?_
  change ∀ᵐ t ∂(volume.restrict (Icc 0 1)), _
  rw [ae_restrict_iff' measurableSet_Icc]
  have hne01 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 ∧ t ≠ 1 := by
    have h0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by rw [ae_iff]; simp
    have h1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by rw [ae_iff]; simp
    exact h0.and h1
  filter_upwards [hne01] with t ⟨htne0, htne1⟩ ht
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 htne0.symm
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 htne1
  have h1t : 0 < 1 - t := by linarith
  have hre_pos := one_sub_mul_re_pos_of_norm_le_one hξ ht.1 ht1
  have h1 : (t : ℂ) ^ ((b - 1 : ℝ) : ℂ) = ((t ^ (b - 1) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow ht0.le (b - 1)).symm
  have h2 : (1 - (t : ℂ)) ^ ((c - b - 1 : ℝ) : ℂ) = (((1 - t) ^ (c - b - 1) : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl]
    exact (Complex.ofReal_cpow h1t.le (c - b - 1)).symm
  simp only [eulerIntegrand]
  rw [h1, h2, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hnn : 0 ≤ t ^ (b - 1) * (1 - t) ^ (c - b - 1) :=
    mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg h1t.le _)
  have hge := cpow_ofReal_exp_re_ge hre_pos ha0 ha1
  calc Real.cos (a * (Real.pi / 2)) *
        (t ^ (b - 1) * (1 - t) ^ (c - b - 1) * ‖1 - ξ * (t : ℂ)‖ ^ (-a))
      = t ^ (b - 1) * (1 - t) ^ (c - b - 1) *
        (‖1 - ξ * (t : ℂ)‖ ^ (-a) * Real.cos (a * (Real.pi / 2))) := by ring
    _ ≤ t ^ (b - 1) * (1 - t) ^ (c - b - 1) * ((1 - ξ * (t : ℂ)) ^ ((-a : ℝ) : ℂ)).re :=
        mul_le_mul_of_nonneg_left hge hnn

lemma eulerInt_re_pos {a b c : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 < b) (hcba : 0 < c - b - a)
    {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) :
    0 < (eulerInt a b c ξ).re := by
  have hcos : 0 < Real.cos (a * (Real.pi / 2)) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hge := eulerInt_re_ge ha0 ha1 hb hcba hξ
  have hint_pos : 0 < ∫ t : ℝ in (0 : ℝ)..1,
      t ^ (b - 1) * (1 - t) ^ (c - b - 1) * ‖1 - ξ * (t : ℂ)‖ ^ (-a) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    have hint_norm : IntegrableOn
        (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (c - b - 1) * ‖1 - ξ * (t : ℂ)‖ ^ (-a)) (Ioc 0 1) volume := by
      have hint := eulerIntegrand_integrable_of_norm_le_one ha0 hb hcba hξ
      have h1 : IntervalIntegrable
          (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (c - b - 1) * ‖1 - ξ * (t : ℂ)‖ ^ (-a)) volume 0 1 := by
        refine hint.norm.congr_ae ?_
        change ∀ᵐ t ∂(volume.restrict (uIoc 0 1)), _
        rw [ae_restrict_iff' measurableSet_uIoc]
        have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by rw [ae_iff]; simp
        filter_upwards [hne1] with t htne1 ht
        rw [uIoc_of_le zero_le_one] at ht
        have ht1 : t < 1 := lt_of_le_of_ne ht.2 htne1
        have hξt_ne : 1 - ξ * (t : ℂ) ≠ 0 := by
          have hre := one_sub_mul_re_pos_of_norm_le_one hξ ht.1.le ht1
          intro h; rw [h, zero_re] at hre; linarith
        simp only [eulerIntegrand, norm_mul]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1,
          show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), norm_cpow_ofReal_exp hξt_ne (-a)]
        simp
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h1
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (c - b - 1) * ‖1 - ξ * (t : ℂ)‖ ^ (-a) := by
      change ∀ᵐ t ∂(volume.restrict (Ioc 0 1)), _
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with t ht
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _)
        (Real.rpow_nonneg (by linarith [ht.2]) _)) (Real.rpow_nonneg (norm_nonneg _) _)
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn hint_norm]
    have hsub : Ioo (0 : ℝ) 1 ⊆
        Function.support (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (c - b - 1) * ‖1 - ξ * (t : ℂ)‖ ^ (-a)) ∩
          Ioc 0 1 := by
      intro t ht
      refine ⟨?_, ht.1, ht.2.le⟩
      rw [Function.mem_support]
      have h1 : 0 < t ^ (b - 1) := Real.rpow_pos_of_pos ht.1 _
      have h2 : 0 < (1 - t) ^ (c - b - 1) := Real.rpow_pos_of_pos (by linarith [ht.2]) _
      have h3 : 0 < ‖1 - ξ * (t : ℂ)‖ ^ (-a) := by
        refine Real.rpow_pos_of_pos (norm_pos_iff.mpr ?_) _
        have hre := one_sub_mul_re_pos_of_norm_le_one hξ ht.1.le ht.2
        intro h; rw [h, zero_re] at hre; linarith
      positivity
    exact lt_of_lt_of_le (by simp) (measure_mono hsub)
  exact lt_of_lt_of_le (mul_pos hcos hint_pos) hge

lemma eulerInt_ne_zero {a b c : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 < b) (hcba : 0 < c - b - a)
    {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) :
    eulerInt a b c ξ ≠ 0 := by
  intro h
  have hpos := eulerInt_re_pos ha0 ha1 hb hcba hξ
  rw [h, zero_re] at hpos
  linarith

/- ## 5. The Ahlfors-Grunsky Functions `I0`, `I1`, `J3`, `w3`, `u6`, `u3` -/

def I0 (ζ : ℂ) : ℂ := eulerInt (1 / 12) (5 / 12) (2 / 3) (ζ ^ 3)
def I1 (ζ : ℂ) : ℂ := eulerInt (3 / 4) (5 / 12) (4 / 3) (ζ ^ 3)
def J3 (ζ : ℂ) : ℂ := eulerInt (2 / 3) (1 / 3) (4 / 3) (ζ ^ 3)

def w3 (ζ : ℂ) : ℂ := (1 / 3 : ℂ) * ζ * J3 ζ

def w6_1 : ℝ :=
  Real.Gamma (1 / 4) * Real.Gamma (4 / 3) / (Real.Gamma (11 / 12) * Real.Gamma (2 / 3))

def u6 (ζ : ℂ) : ℂ := (R : ℂ) * ζ * I1 ζ / I0 ζ
def u3 (ζ : ℂ) : ℂ := ((R / w6_1 : ℝ) : ℂ) * w3 ζ

def Ω : Set ℂ := {ζ : ℂ | ζ ^ 3 ∈ slitSet}

lemma isOpen_Ω : IsOpen Ω := isOpen_slitSet.preimage (continuous_pow 3)

lemma ball_subset_Ω : ball (0 : ℂ) 1 ⊆ Ω := fun ζ hζ => by
  apply ball_subset_slitSet
  have h1 : ‖ζ‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hζ
  rw [Metric.mem_ball, dist_zero_right, norm_pow]
  exact pow_lt_one₀ (norm_nonneg ζ) h1 (by norm_num)

lemma zero_mem_Ω : (0 : ℂ) ∈ Ω := ball_subset_Ω (Metric.mem_ball_self zero_lt_one)

lemma isPreconnected_Ω : IsPreconnected Ω := by
  have hpath : IsPathConnected Ω := by
    refine ⟨0, zero_mem_Ω, fun ζ hζ => ?_⟩
    refine ⟨⟨⟨fun t => ((t : ℝ) : ℂ) * ζ, (Complex.continuous_ofReal.comp continuous_subtype_val).mul
      continuous_const⟩, by simp, by simp⟩, fun t => ?_⟩
    change (((t : ℝ) : ℂ) * ζ) ^ 3 ∈ slitSet
    intro ⟨hre, him⟩
    rw [mul_pow, ← Complex.ofReal_pow] at hre him
    simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul] at hre him
    have ht0 : 0 < (t : ℝ) := by
      by_contra hle
      push Not at hle
      have ht_eq : (t : ℝ) = 0 := le_antisymm hle t.2.1
      rw [ht_eq] at hre; norm_num at hre
    have ht3_pos : 0 < (t : ℝ) ^ 3 := pow_pos ht0 3
    have ht3_le : (t : ℝ) ^ 3 ≤ 1 := pow_le_one₀ t.2.1 t.2.2
    have him' : (ζ ^ 3).im = 0 := (mul_eq_zero.mp him).resolve_left ht3_pos.ne'
    have hre' : 1 ≤ (ζ ^ 3).re := by nlinarith
    exact hζ ⟨hre', him'⟩
  exact hpath.isConnected.isPreconnected

lemma w6_1_pos : 0 < w6_1 := by
  unfold w6_1
  have h1 : (0 : ℝ) < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : (0 : ℝ) < Real.Gamma (4 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h3 : (0 : ℝ) < Real.Gamma (11 / 12) := Real.Gamma_pos_of_pos (by norm_num)
  have h4 : (0 : ℝ) < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  positivity

lemma betaIntegral_eq_real_Gamma {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Complex.betaIntegral (x : ℂ) (y : ℂ) =
      ((Real.Gamma x * Real.Gamma y / Real.Gamma (x + y) : ℝ) : ℂ) := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (x : ℂ)) (t := (y : ℂ))
    (by simpa using hx) (by simpa using hy)
  have hne : Complex.Gamma ((x : ℂ) + (y : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.Gamma_ofReal]
    exact Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hbeta : Complex.betaIntegral (x : ℂ) (y : ℂ) =
      Complex.Gamma (x : ℂ) * Complex.Gamma (y : ℂ) / Complex.Gamma ((x : ℂ) + (y : ℂ)) := by
    rw [eq_div_iff hne, mul_comm]; exact h.symm
  rw [hbeta, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  push_cast; rfl

lemma I0_zero : I0 0 =
    ((Real.Gamma (5 / 12) * Real.Gamma (1 / 4) / Real.Gamma (2 / 3) : ℝ) : ℂ) := by
  unfold I0
  rw [zero_pow (by norm_num), eulerInt_zero]
  have h := betaIntegral_eq_real_Gamma (x := 5 / 12) (y := 1 / 4) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

lemma I1_zero : I1 0 =
    ((Real.Gamma (5 / 12) * Real.Gamma (11 / 12) / Real.Gamma (4 / 3) : ℝ) : ℂ) := by
  unfold I1
  rw [zero_pow (by norm_num), eulerInt_zero]
  have h := betaIntegral_eq_real_Gamma (x := 5 / 12) (y := 11 / 12) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

lemma I0_zero_div_I1_zero : I0 0 / I1 0 = (w6_1 : ℂ) := by
  rw [I0_zero, I1_zero]
  unfold w6_1
  have h512 : Real.Gamma (5 / 12) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h14 : Real.Gamma (1 / 4) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h23 : Real.Gamma (2 / 3) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h1112 : Real.Gamma (11 / 12) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h43 : Real.Gamma (4 / 3) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  rw [← Complex.ofReal_div]
  congr 1
  field_simp

lemma I0_one_eq_I1_one : I0 1 = I1 1 := by
  unfold I0 I1
  rw [one_pow, eulerInt_one, eulerInt_one]
  norm_num

lemma I0_ne_zero_of_norm_le_one {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) : I0 ζ ≠ 0 := by
  refine eulerInt_ne_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg ζ) hζ

lemma I1_ne_zero_of_norm_le_one {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) : I1 ζ ≠ 0 := by
  refine eulerInt_ne_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg ζ) hζ

lemma J3_ne_zero_of_norm_le_one {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) : J3 ζ ≠ 0 := by
  refine eulerInt_ne_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg ζ) hζ

lemma J3_zero : J3 0 = 3 := by
  unfold J3
  rw [zero_pow (by norm_num), eulerInt_zero]
  norm_num [Complex.betaIntegral_eval_one_right]

lemma J3_one : J3 1 = ((Real.Gamma (1 / 3) * Real.Gamma (1 / 3) / Real.Gamma (2 / 3) : ℝ) : ℂ) := by
  unfold J3
  rw [one_pow, eulerInt_one]
  have h := betaIntegral_eq_real_Gamma (x := 1 / 3) (y := 1 / 3) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

lemma w3_one : w3 1 = ((Real.Gamma (1 / 3) * Real.Gamma (4 / 3) / Real.Gamma (2 / 3) : ℝ) : ℂ) := by
  unfold w3
  rw [J3_one, mul_one]
  have h43 : Real.Gamma (4 / 3) = (1 / 3 : ℝ) * Real.Gamma (1 / 3) := by
    have := Real.Gamma_add_one (s := (1 / 3 : ℝ)) (by norm_num)
    norm_num at this
    exact this
  rw [h43]
  push_cast; ring

lemma u6_zero : u6 0 = 0 := by simp [u6]
lemma u3_zero : u3 0 = 0 := by simp [u3, w3]

lemma u6_one : u6 1 = (R : ℂ) := by
  unfold u6
  have hne : I0 1 ≠ 0 := I0_ne_zero_of_norm_le_one (by simp)
  rw [mul_one, I0_one_eq_I1_one, mul_div_cancel_right₀ _ (by rwa [← I0_one_eq_I1_one])]

lemma u3_one : u3 1 = (cAG : ℂ) := by
  unfold u3
  rw [w3_one, ← Complex.ofReal_mul]
  congr 1
  unfold cAG R w6_1
  have h13 : Real.Gamma (1 / 3) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h43 : Real.Gamma (4 / 3) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h23 : Real.Gamma (2 / 3) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h14 : Real.Gamma (1 / 4) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h1112 : Real.Gamma (11 / 12) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hsq : Real.sqrt (1 + Real.sqrt 3) ≠ 0 := (Real.sqrt_pos.mpr one_add_sqrt3_pos).ne'
  field_simp

lemma u6_rot (ζ : ℂ) : u6 (ω * ζ) = ω * u6 ζ := by
  have hcube : (ω * ζ) ^ 3 = ζ ^ 3 := by rw [mul_pow, ω_cube, one_mul]
  unfold u6 I1 I0
  rw [hcube]; ring

lemma u3_rot (ζ : ℂ) : u3 (ω * ζ) = ω * u3 ζ := by
  have hcube : (ω * ζ) ^ 3 = ζ ^ 3 := by rw [mul_pow, ω_cube, one_mul]
  unfold u3 w3 J3
  rw [hcube]; ring

lemma I0_conj {ζ : ℂ} (hζ : ζ ∈ Ω ∨ ‖ζ‖ ≤ 1) :
    I0 (starRingEnd ℂ ζ) = starRingEnd ℂ (I0 ζ) := by
  unfold I0
  rw [← map_pow]
  have hξ : ζ ^ 3 ∈ slitSet ∨ ‖ζ ^ 3‖ ≤ 1 := by
    rcases hζ with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg ζ) h)
  refine eulerInt_conj hξ ?_
  rcases hξ with h | h
  · exact eulerIntegrand_integrable_of_slitSet (by norm_num) (by norm_num) h
  · exact eulerIntegrand_integrable_of_norm_le_one (by norm_num) (by norm_num) (by norm_num) h

lemma I1_conj {ζ : ℂ} (hζ : ζ ∈ Ω ∨ ‖ζ‖ ≤ 1) :
    I1 (starRingEnd ℂ ζ) = starRingEnd ℂ (I1 ζ) := by
  unfold I1
  rw [← map_pow]
  have hξ : ζ ^ 3 ∈ slitSet ∨ ‖ζ ^ 3‖ ≤ 1 := by
    rcases hζ with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg ζ) h)
  refine eulerInt_conj hξ ?_
  rcases hξ with h | h
  · exact eulerIntegrand_integrable_of_slitSet (by norm_num) (by norm_num) h
  · exact eulerIntegrand_integrable_of_norm_le_one (by norm_num) (by norm_num) (by norm_num) h

lemma J3_conj {ζ : ℂ} (hζ : ζ ∈ Ω ∨ ‖ζ‖ ≤ 1) :
    J3 (starRingEnd ℂ ζ) = starRingEnd ℂ (J3 ζ) := by
  unfold J3
  rw [← map_pow]
  have hξ : ζ ^ 3 ∈ slitSet ∨ ‖ζ ^ 3‖ ≤ 1 := by
    rcases hζ with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg ζ) h)
  refine eulerInt_conj hξ ?_
  rcases hξ with h | h
  · exact eulerIntegrand_integrable_of_slitSet (by norm_num) (by norm_num) h
  · exact eulerIntegrand_integrable_of_norm_le_one (by norm_num) (by norm_num) (by norm_num) h

lemma u6_conj {ζ : ℂ} (hζ : ζ ∈ Ω ∨ ‖ζ‖ ≤ 1) :
    u6 (starRingEnd ℂ ζ) = starRingEnd ℂ (u6 ζ) := by
  unfold u6
  rw [I1_conj hζ, I0_conj hζ]
  simp [Complex.conj_ofReal]

lemma u3_conj {ζ : ℂ} (hζ : ζ ∈ Ω ∨ ‖ζ‖ ≤ 1) :
    u3 (starRingEnd ℂ ζ) = starRingEnd ℂ (u3 ζ) := by
  unfold u3 w3
  rw [J3_conj hζ]
  simp only [map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal]

lemma u6_continuousOn_closedBall : ContinuousOn u6 (closedBall 0 1) := by
  have hpow : MapsTo (fun ζ : ℂ => ζ ^ 3) (closedBall 0 1) (closedBall 0 1) := fun ζ hζ => by
    have h1 : ‖ζ‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hζ
    simpa [Metric.mem_closedBall, dist_zero_right, norm_pow] using pow_le_one₀ (norm_nonneg ζ) h1
  have hI0 : ContinuousOn I0 (closedBall 0 1) :=
    (eulerInt_continuousOn_closedBall (by norm_num) (by norm_num) (by norm_num)).comp
      (continuous_pow 3).continuousOn hpow
  have hI1 : ContinuousOn I1 (closedBall 0 1) :=
    (eulerInt_continuousOn_closedBall (by norm_num) (by norm_num) (by norm_num)).comp
      (continuous_pow 3).continuousOn hpow
  unfold u6
  exact ((continuousOn_const.mul continuousOn_id).mul hI1).div hI0 fun ζ hζ =>
    I0_ne_zero_of_norm_le_one (by simpa [Metric.mem_closedBall, dist_zero_right] using hζ)

lemma u3_continuousOn_closedBall : ContinuousOn u3 (closedBall 0 1) := by
  have hpow : MapsTo (fun ζ : ℂ => ζ ^ 3) (closedBall 0 1) (closedBall 0 1) := fun ζ hζ => by
    have h1 : ‖ζ‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hζ
    simpa [Metric.mem_closedBall, dist_zero_right, norm_pow] using pow_le_one₀ (norm_nonneg ζ) h1
  have hJ3 : ContinuousOn J3 (closedBall 0 1) :=
    (eulerInt_continuousOn_closedBall (by norm_num) (by norm_num) (by norm_num)).comp
      (continuous_pow 3).continuousOn hpow
  unfold u3 w3
  exact continuousOn_const.mul ((continuousOn_const.mul continuousOn_id).mul hJ3)

lemma u6_eq_zero_iff {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) : u6 ζ = 0 ↔ ζ = 0 := by
  unfold u6
  have hR : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr R_ne_zero
  have hI0 := I0_ne_zero_of_norm_le_one hζ
  have hI1 := I1_ne_zero_of_norm_le_one hζ
  simp [hR, hI0, hI1]

lemma u3_eq_zero_iff {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) : u3 ζ = 0 ↔ ζ = 0 := by
  unfold u3 w3
  have hR := R_ne_zero
  have hw := w6_1_pos.ne'
  have hJ3 := J3_ne_zero_of_norm_le_one hζ
  simp [hR, hw, hJ3]

lemma I0_differentiableOn_Ω : DifferentiableOn ℂ I0 Ω :=
  (eulerInt_differentiableOn (by norm_num) (by norm_num)).comp
    (differentiable_pow 3).differentiableOn fun _ h => h

lemma I1_differentiableOn_Ω : DifferentiableOn ℂ I1 Ω :=
  (eulerInt_differentiableOn (by norm_num) (by norm_num)).comp
    (differentiable_pow 3).differentiableOn fun _ h => h

lemma J3_differentiableOn_Ω : DifferentiableOn ℂ J3 Ω :=
  (eulerInt_differentiableOn (by norm_num) (by norm_num)).comp
    (differentiable_pow 3).differentiableOn fun _ h => h

lemma deriv_u6_zero : deriv u6 0 = ((R / w6_1 : ℝ) : ℂ) := by
  have hI0 : DifferentiableAt ℂ I0 0 := I0_differentiableOn_Ω.differentiableAt (isOpen_Ω.mem_nhds zero_mem_Ω)
  have hI1 : DifferentiableAt ℂ I1 0 := I1_differentiableOn_Ω.differentiableAt (isOpen_Ω.mem_nhds zero_mem_Ω)
  have hI0_ne : I0 0 ≠ 0 := I0_ne_zero_of_norm_le_one (by simp)
  have hq : DifferentiableAt ℂ (fun ζ => (R : ℂ) * (I1 ζ / I0 ζ)) 0 :=
    (hI1.div hI0 hI0_ne).const_mul (R : ℂ)
  have hu6_eq : u6 = fun ζ => ζ * ((R : ℂ) * (I1 ζ / I0 ζ)) := by
    ext ζ; unfold u6; ring
  have hd : HasDerivAt u6 (1 * ((R : ℂ) * (I1 0 / I0 0)) + 0 * deriv (fun ζ => (R : ℂ) * (I1 ζ / I0 ζ)) 0) 0 := by
    rw [hu6_eq]
    exact (hasDerivAt_id (0 : ℂ)).mul hq.hasDerivAt
  rw [hd.deriv, one_mul, zero_mul, add_zero]
  have hdiv : I1 0 / I0 0 = (w6_1 : ℂ)⁻¹ := by
    rw [← inv_div, I0_zero_div_I1_zero]
  rw [hdiv, Complex.ofReal_div, div_eq_mul_inv]

lemma deriv_u3_zero : deriv u3 0 = ((R / w6_1 : ℝ) : ℂ) := by
  have hJ3 : DifferentiableAt ℂ J3 0 := J3_differentiableOn_Ω.differentiableAt (isOpen_Ω.mem_nhds zero_mem_Ω)
  have hq : DifferentiableAt ℂ (fun ζ => ((R / w6_1 : ℝ) : ℂ) * ((1 / 3 : ℂ) * J3 ζ)) 0 :=
    (hJ3.const_mul (1 / 3 : ℂ)).const_mul _
  have hu3_eq : u3 = fun ζ => ζ * (((R / w6_1 : ℝ) : ℂ) * ((1 / 3 : ℂ) * J3 ζ)) := by
    ext ζ; unfold u3 w3; ring
  have hd : HasDerivAt u3 (1 * (((R / w6_1 : ℝ) : ℂ) * ((1 / 3 : ℂ) * J3 0)) +
      0 * deriv (fun ζ => ((R / w6_1 : ℝ) : ℂ) * ((1 / 3 : ℂ) * J3 ζ)) 0) 0 := by
    rw [hu3_eq]
    exact (hasDerivAt_id (0 : ℂ)).mul hq.hasDerivAt
  rw [hd.deriv, J3_zero]
  ring

/-- Crucial bound: `‖u6 ζ‖ < 1` everywhere on `closedBall 0 1`! -/
lemma norm_u6_lt_one {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) : ‖u6 ζ‖ < 1 := by
  have hξ : ‖ζ ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg ζ) hζ
  -- Step 1: `‖I1 ζ‖ ≤ ∫ t in 0..1, t^(-7/12) * (1 - t)^(-3/4) * ‖1 - ζ^3 * t‖^(-1/12)`!
  have hI1_le : ‖I1 ζ‖ ≤ ∫ t : ℝ in (0 : ℝ)..1,
      t ^ ((5 / 12 : ℝ) - 1) * (1 - t) ^ ((2 / 3 : ℝ) - (5 / 12 : ℝ) - 1) *
        ‖1 - ζ ^ 3 * (t : ℂ)‖ ^ (-(1 / 12 : ℝ)) := by
    unfold I1 eulerInt
    have hnorm_le := intervalIntegral.norm_integral_le_integral_norm (μ := volume) zero_le_one
      (f := eulerIntegrand (3 / 4) (5 / 12) (4 / 3) (ζ ^ 3))
    refine hnorm_le.trans ?_
    have hint1 := (eulerIntegrand_integrable_of_norm_le_one (a := 3 / 4) (b := 5 / 12) (c := 4 / 3)
      (by norm_num) (by norm_num) (by norm_num) hξ).norm
    have hint0 := (eulerIntegrand_integrable_of_norm_le_one (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
      (by norm_num) (by norm_num) (by norm_num) hξ).norm
    have hint0' : IntervalIntegrable
        (fun t : ℝ => t ^ ((5 / 12 : ℝ) - 1) * (1 - t) ^ ((2 / 3 : ℝ) - (5 / 12 : ℝ) - 1) *
          ‖1 - ζ ^ 3 * (t : ℂ)‖ ^ (-(1 / 12 : ℝ))) volume 0 1 := by
      refine hint0.congr_ae ?_
      change ∀ᵐ t ∂(volume.restrict (uIoc 0 1)), _
      rw [ae_restrict_iff' measurableSet_uIoc]
      have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by rw [ae_iff]; simp
      filter_upwards [hne1] with t htne1 ht
      rw [uIoc_of_le zero_le_one] at ht
      have ht1 : t < 1 := lt_of_le_of_ne ht.2 htne1
      have hξt_ne : 1 - ζ ^ 3 * (t : ℂ) ≠ 0 := by
        have hre := one_sub_mul_re_pos_of_norm_le_one hξ ht.1.le ht1
        intro h; rw [h, zero_re] at hre; linarith
      simp only [eulerIntegrand, norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1,
        show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), norm_cpow_ofReal_exp hξt_ne]
      simp
    refine intervalIntegral.integral_mono_ae_restrict zero_le_one hint1 hint0' ?_
    change ∀ᵐ t ∂(volume.restrict (Icc 0 1)), _
    rw [ae_restrict_iff' measurableSet_Icc]
    have hne01 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 ∧ t ≠ 1 := by
      have h0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by rw [ae_iff]; simp
      have h1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by rw [ae_iff]; simp
      exact h0.and h1
    filter_upwards [hne01] with t ⟨htne0, htne1⟩ ht
    have ht0 : 0 < t := lt_of_le_of_ne ht.1 htne0.symm
    have ht1 : t < 1 := lt_of_le_of_ne ht.2 htne1
    have h1t : 0 < 1 - t := by linarith
    have hξt_ne : 1 - ζ ^ 3 * (t : ℂ) ≠ 0 := by
      have hre := one_sub_mul_re_pos_of_norm_le_one hξ ht.1 ht1
      intro h; rw [h, zero_re] at hre; linarith
    have hξt_pos : 0 < ‖1 - ζ ^ 3 * (t : ℂ)‖ := norm_pos_iff.mpr hξt_ne
    simp only [eulerIntegrand, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0,
      show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos h1t, norm_cpow_ofReal_exp hξt_ne]
    simp only [ofReal_re]
    have hsplit : ‖1 - ζ ^ 3 * (t : ℂ)‖ ^ (-(3 / 4 : ℝ)) =
        ‖1 - ζ ^ 3 * (t : ℂ)‖ ^ (-(2 / 3 : ℝ)) * ‖1 - ζ ^ 3 * (t : ℂ)‖ ^ (-(1 / 12 : ℝ)) := by
      rw [← Real.rpow_add hξt_pos]; congr 1; norm_num
    have h1t_split : (1 - t) ^ ((2 / 3 : ℝ) - (5 / 12 : ℝ) - 1) =
        (1 - t) ^ ((4 / 3 : ℝ) - (5 / 12 : ℝ) - 1) * (1 - t) ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add h1t]; congr 1; norm_num
    have hle_pow : ‖1 - ζ ^ 3 * (t : ℂ)‖ ^ (-(2 / 3 : ℝ)) ≤ (1 - t) ^ (-(2 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos h1t (one_sub_mul_norm_ge hξ ht.1) (by norm_num)
    rw [hsplit, h1t_split]
    have hnn1 : 0 ≤ t ^ ((5 / 12 : ℝ) - 1) := Real.rpow_nonneg ht0.le _
    have hnn2 : 0 ≤ (1 - t) ^ ((4 / 3 : ℝ) - (5 / 12 : ℝ) - 1) := Real.rpow_nonneg h1t.le _
    have hnn3 : 0 ≤ ‖1 - ζ ^ 3 * (t : ℂ)‖ ^ (-(1 / 12 : ℝ)) := Real.rpow_nonneg hξt_pos.le _
    calc t ^ ((5 / 12 : ℝ) - 1) * (1 - t) ^ ((4 / 3 : ℝ) - (5 / 12 : ℝ) - 1) *
          (‖1 - ζ ^ 3 * (t : ℂ)‖ ^ (-(2 / 3 : ℝ)) * ‖1 - ζ ^ 3 * (t : ℂ)‖ ^ (-(1 / 12 : ℝ)))
        = (t ^ ((5 / 12 : ℝ) - 1) * (1 - t) ^ ((4 / 3 : ℝ) - (5 / 12 : ℝ) - 1) *
            ‖1 - ζ ^ 3 * (t : ℂ)‖ ^ (-(1 / 12 : ℝ))) * ‖1 - ζ ^ 3 * (t : ℂ)‖ ^ (-(2 / 3 : ℝ)) := by ring
      _ ≤ (t ^ ((5 / 12 : ℝ) - 1) * (1 - t) ^ ((4 / 3 : ℝ) - (5 / 12 : ℝ) - 1) *
            ‖1 - ζ ^ 3 * (t : ℂ)‖ ^ (-(1 / 12 : ℝ))) * (1 - t) ^ (-(2 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hle_pow (mul_nonneg (mul_nonneg hnn1 hnn2) hnn3)
      _ = t ^ ((5 / 12 : ℝ) - 1) * ((1 - t) ^ ((4 / 3 : ℝ) - (5 / 12 : ℝ) - 1) *
            (1 - t) ^ (-(2 / 3 : ℝ))) * ‖1 - ζ ^ 3 * (t : ℂ)‖ ^ (-(1 / 12 : ℝ)) := by ring
  -- Step 2: `cos(π/24) * RHS ≤ (I0 ζ).re ≤ ‖I0 ζ‖`!
  have hI0_ge := eulerInt_re_ge (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hξ
  have hcos_ge : Real.sqrt 3 / 2 ≤ Real.cos ((1 / 12 : ℝ) * (Real.pi / 2)) := by
    rw [← Real.cos_pi_div_six]
    exact Real.strictAntiOn_cos.antitoneOn
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      (by linarith [Real.pi_pos])
  have hI0_norm_ge : (Real.sqrt 3 / 2) * ‖I1 ζ‖ ≤ ‖I0 ζ‖ := by
    have h1 : Real.cos ((1 / 12 : ℝ) * (Real.pi / 2)) * ‖I1 ζ‖ ≤ (I0 ζ).re := by
      have hcos_pos : 0 ≤ Real.cos ((1 / 12 : ℝ) * (Real.pi / 2)) := by
        linarith [sqrt3_pos]
      exact (mul_le_mul_of_nonneg_left hI1_le hcos_pos).trans hI0_ge
    have h2 : (I0 ζ).re ≤ ‖I0 ζ‖ := Complex.re_le_norm (I0 ζ)
    have h3 : (Real.sqrt 3 / 2) * ‖I1 ζ‖ ≤ Real.cos ((1 / 12 : ℝ) * (Real.pi / 2)) * ‖I1 ζ‖ :=
      mul_le_mul_of_nonneg_right hcos_ge (norm_nonneg _)
    linarith
  -- Step 3: `‖u6 ζ‖ = R * ‖ζ‖ * ‖I1 ζ‖ / ‖I0 ζ‖ ≤ R / (√3 / 2) < 1`!
  unfold u6
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg R_pos.le]
  have hI0_pos : 0 < ‖I0 ζ‖ := norm_pos_iff.mpr (I0_ne_zero_of_norm_le_one hζ)
  rw [div_lt_one hI0_pos]
  have hR_lt : R < Real.sqrt 3 / 2 := by
    have hsq : R ^ 2 < (Real.sqrt 3 / 2) ^ 2 := by
      rw [R_sq]
      have h3 : Real.sqrt 3 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      nlinarith [sq_sqrt3]
    nlinarith [R_pos, sqrt3_pos]
  have hI1_pos : 0 < ‖I1 ζ‖ := norm_pos_iff.mpr (I1_ne_zero_of_norm_le_one hζ)
  have hstep1 : R * ‖ζ‖ * ‖I1 ζ‖ ≤ R * ‖I1 ζ‖ := by
    have : R * ‖ζ‖ ≤ R := mul_le_of_le_one_right R_pos.le hζ
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hstep2 : R * ‖I1 ζ‖ < (Real.sqrt 3 / 2) * ‖I1 ζ‖ :=
    mul_lt_mul_of_pos_right hR_lt hI1_pos
  linarith

end

end BlochAG


/- ==================== Bloch_Part2B.lean ==================== -/
/-
# Ahlfors-Grunsky Proof — Part 2B: ODE, Wronskian, Reflection Laws, and Boundary Mapping
-/

namespace BlochAG

open Complex Metric Set Filter Topology Real MeasureTheory intervalIntegral

noncomputable section

/- ## 1. Constant Function on Open Preconnected Set & Antiholomorphic Helpers -/

lemma eq_const_of_deriv_eq_zero {f : ℂ → ℂ} {S : Set ℂ} (hSo : IsOpen S) (hSc : IsPreconnected S)
    (hf : DifferentiableOn ℂ f S) (hderiv : ∀ z ∈ S, deriv f z = 0) {z₀ z : ℂ}
    (hz₀ : z₀ ∈ S) (hz : z ∈ S) : f z = f z₀ := by
  have hloc : IsLocallyConstant (fun x : S => f x) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro ⟨x, hx⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hSo x hx
    have hconst : ∀ y ∈ ball x r, f y = f x := by
      intro y hy
      have hconv := convex_ball x r
      have hfd : ∀ w ∈ ball x r, fderivWithin ℂ f (ball x r) w = 0 := by
        intro w hw
        have hwS : w ∈ S := hball hw
        rw [fderivWithin_of_isOpen isOpen_ball hw]
        have hd : HasDerivAt f 0 w := by
          rw [← hderiv w hwS]
          exact (hf.differentiableAt (hSo.mem_nhds hwS)).hasDerivAt
        simpa using hd.hasFDerivAt.fderiv
      exact hconv.is_const_of_fderivWithin_eq_zero (hf.mono hball) hfd hy (mem_ball_self hr)
    have hnhds : Subtype.val ⁻¹' ball x r ∈ 𝓝 (⟨x, hx⟩ : S) :=
      continuous_subtype_val.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hnhds] with y hy
    exact hconst y.1 hy
  have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hSc
  exact hloc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ ⟨z, hz⟩) (mem_univ ⟨z₀, hz₀⟩)

lemma hasDerivAt_conj_comp_conj {f : ℂ → ℂ} {f' z : ℂ}
    (hf : HasDerivAt f f' (starRingEnd ℂ z)) :
    HasDerivAt (fun w : ℂ => starRingEnd ℂ (f (starRingEnd ℂ w))) (starRingEnd ℂ f') z := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hf ⊢
  have hconj_t : Tendsto (fun t : ℂ => starRingEnd ℂ t) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (Complex.continuous_conj.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (map_ne_zero _).mpr ht
  have h1 := (Complex.continuous_conj.continuousAt.tendsto.comp (hf.comp hconj_t))
  refine h1.congr fun t => ?_
  simp only [Function.comp_apply, smul_eq_mul, map_mul, map_inv₀, map_sub, map_add,
    RingHomCompTriple.comp_apply, RingHom.id_apply]

lemma hasDerivAt_inv_conj {f : ℂ → ℂ} {f' z : ℂ} (hz : z ≠ 0)
    (hf : HasDerivAt f f' (1 / starRingEnd ℂ z)) :
    HasDerivAt (fun w : ℂ => starRingEnd ℂ (f (1 / starRingEnd ℂ w)))
      (-(starRingEnd ℂ f') / z ^ 2) z := by
  have h1 : HasDerivAt (fun w : ℂ => starRingEnd ℂ (f (starRingEnd ℂ w)))
      (starRingEnd ℂ f') (z⁻¹) := by
    refine hasDerivAt_conj_comp_conj ?_
    simpa [one_div, map_inv₀] using hf
  have hinv : HasDerivAt (fun w : ℂ => w⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz
  have hcomp := h1.comp z hinv
  refine (hcomp.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with w
    simp [one_div, map_inv₀]
  · ring

/- ## 2. The Second-Order Linear ODE on `Ω` for `y0` and `y1` -/

def y0 (ζ : ℂ) : ℂ := (1 - ζ ^ 3) ^ ((5 / 12 : ℝ) : ℂ) * I0 ζ
def y1 (ζ : ℂ) : ℂ := (1 - ζ ^ 3) ^ ((5 / 12 : ℝ) : ℂ) * ζ * I1 ζ

lemma one_sub_cube_mem_slitPlane {ζ : ℂ} (hζ : ζ ∈ Ω) :
    1 - ζ ^ 3 ∈ Complex.slitPlane := by
  simpa using one_sub_mul_mem_slitPlane hζ zero_le_one le_rfl

lemma one_sub_cube_ne_zero {ζ : ℂ} (hζ : ζ ∈ Ω) : 1 - ζ ^ 3 ≠ 0 :=
  Complex.slitPlane_ne_zero (one_sub_cube_mem_slitPlane hζ)

lemma hasDerivAt_one_sub_cube_cpow {α : ℝ} {ζ : ℂ} (hζ : ζ ∈ Ω) :
    HasDerivAt (fun z : ℂ => (1 - z ^ 3) ^ (α : ℂ))
      (-(3 : ℂ) * (α : ℂ) * ζ ^ 2 * (1 - ζ ^ 3) ^ (((α - 1 : ℝ) : ℂ))) ζ := by
  have hinner : HasDerivAt (fun z : ℂ => (1 : ℂ) - z ^ 3) (-(3 * ζ ^ 2)) ζ := by
    have hp := hasDerivAt_pow 3 ζ
    simpa [Nat.cast_ofNat] using hp.const_sub (1 : ℂ)
  have hcp := hinner.cpow_const (c := (α : ℂ)) (one_sub_cube_mem_slitPlane hζ)
  refine hcp.congr_deriv ?_
  rw [show (α : ℂ) - 1 = ((α - 1 : ℝ) : ℂ) by push_cast; rfl]
  ring

lemma hasDerivAt_comp_cube {f : ℂ → ℂ} {f' ζ : ℂ} (hf : HasDerivAt f f' (ζ ^ 3)) :
    HasDerivAt (fun z : ℂ => f (z ^ 3)) (3 * ζ ^ 2 * f') ζ := by
  have hp : HasDerivAt (fun z : ℂ => z ^ 3) (3 * ζ ^ 2) ζ := by
    simpa [Nat.cast_ofNat] using hasDerivAt_pow 3 ζ
  simpa only [Function.comp_def, mul_comm] using hf.comp ζ hp

lemma hasDerivAt_euler_comp_cube {a b c : ℝ} (hb : 0 < b) (hcb : 0 < c - b)
    {ζ : ℂ} (hζ : ζ ∈ Ω) :
    HasDerivAt (fun z : ℂ => eulerInt a b c (z ^ 3))
      (3 * ζ ^ 2 * deriv (eulerInt a b c) (ζ ^ 3)) ζ := by
  have hd := eulerInt_hasDerivAt (a := a) hb hcb hζ
  rw [← hd.deriv] at hd
  exact hasDerivAt_comp_cube hd

lemma hasDerivAt_deriv_euler_comp_cube {a b c : ℝ} (hb : 0 < b) (hcb : 0 < c - b)
    {ζ : ℂ} (hζ : ζ ∈ Ω) :
    HasDerivAt (fun z : ℂ => deriv (eulerInt a b c) (z ^ 3))
      (3 * ζ ^ 2 * deriv (deriv (eulerInt a b c)) (ζ ^ 3)) ζ := by
  have hd := eulerInt_hasDerivAt_deriv (a := a) hb hcb hζ
  rw [← hd.deriv] at hd
  exact hasDerivAt_comp_cube hd

lemma y0_hasDerivAt {ζ : ℂ} (hζ : ζ ∈ Ω) :
    HasDerivAt y0
      ((-(5 / 4 : ℂ) * ζ ^ 2 * (1 - ζ ^ 3) ^ ((-(7 / 12) : ℝ) : ℂ)) * I0 ζ +
        (1 - ζ ^ 3) ^ ((5 / 12 : ℝ) : ℂ) *
          (3 * ζ ^ 2 * deriv (eulerInt (1 / 12) (5 / 12) (2 / 3)) (ζ ^ 3))) ζ := by
  have h1 := hasDerivAt_one_sub_cube_cpow (α := 5 / 12) hζ
  have h2 := hasDerivAt_euler_comp_cube (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
    (by norm_num) (by norm_num) hζ
  refine (h1.mul h2).congr_deriv ?_
  have heq : ((5 / 12 - 1 : ℝ) : ℂ) = ((-(7 / 12) : ℝ) : ℂ) := by norm_num
  rw [heq]; unfold I0; push_cast; ring

lemma y0_differentiableOn_Ω : DifferentiableOn ℂ y0 Ω := fun _ hζ =>
  (y0_hasDerivAt hζ).differentiableAt.differentiableWithinAt

lemma y0_ode {ζ : ℂ} (hζ : ζ ∈ Ω) :
    HasDerivAt (deriv y0) (-(35 / 16 : ℂ) * ζ / (1 - ζ ^ 3) ^ 2 * y0 ζ) ζ := by
  have heq : deriv y0 =ᶠ[𝓝 ζ] fun z =>
      (-(5 / 4 : ℂ) * z ^ 2 * (1 - z ^ 3) ^ ((-(7 / 12) : ℝ) : ℂ)) * I0 z +
        (1 - z ^ 3) ^ ((5 / 12 : ℝ) : ℂ) *
          (3 * z ^ 2 * deriv (eulerInt (1 / 12) (5 / 12) (2 / 3)) (z ^ 3)) := by
    filter_upwards [isOpen_Ω.mem_nhds hζ] with z hz
    exact (y0_hasDerivAt hz).deriv
  have hpow2 : HasDerivAt (fun z : ℂ => z ^ 2) (2 * ζ) ζ := by
    simpa [Nat.cast_ofNat] using hasDerivAt_pow 2 ζ
  have hp1 := hasDerivAt_one_sub_cube_cpow (α := -(7 / 12)) hζ
  have hp2 := hasDerivAt_one_sub_cube_cpow (α := 5 / 12) hζ
  have hI0 := hasDerivAt_euler_comp_cube (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
    (by norm_num) (by norm_num) hζ
  have hI0' := hasDerivAt_deriv_euler_comp_cube (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
    (by norm_num) (by norm_num) hζ
  have hterm1 := ((hpow2.const_mul (-(5 / 4 : ℂ))).mul hp1).mul hI0
  have hterm2 := hp2.mul ((hpow2.const_mul (3 : ℂ)).mul hI0')
  have hsum := hterm1.add hterm2
  refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
  have h1z : 1 - ζ ^ 3 ≠ 0 := one_sub_cube_ne_zero hζ
  set P : ℂ := (1 - ζ ^ 3) ^ ((5 / 12 : ℝ) : ℂ)
  have hP1 : (1 - ζ ^ 3) ^ ((-(7 / 12) : ℝ) : ℂ) = P / (1 - ζ ^ 3) := by
    rw [eq_div_iff h1z]; simp only [P]
    rw [show ((5 / 12 : ℝ) : ℂ) = ((-(7 / 12) : ℝ) : ℂ) + 1 by norm_num,
      Complex.cpow_add _ _ h1z, Complex.cpow_one]
  have hP2 : (1 - ζ ^ 3) ^ ((-(7 / 12) - 1 : ℝ) : ℂ) = P / (1 - ζ ^ 3) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 h1z)]; simp only [P]
    rw [show ((5 / 12 : ℝ) : ℂ) = ((-(7 / 12) - 1 : ℝ) : ℂ) + 2 by norm_num,
      Complex.cpow_add _ _ h1z, Complex.cpow_two]
  have hP3 : (1 - ζ ^ 3) ^ ((5 / 12 - 1 : ℝ) : ℂ) = P / (1 - ζ ^ 3) := by
    rw [show ((5 / 12 - 1 : ℝ) : ℂ) = ((-(7 / 12) : ℝ) : ℂ) by norm_num]; exact hP1
  have hode := eulerInt_hypergeom_ode (a := 1 / 12) (b := 5 / 12) (c := 2 / 3)
    (by norm_num) (by norm_num) hζ
  unfold y0 I0
  simp only [Pi.mul_apply]
  rw [show (1 - ζ ^ 3) ^ ((5 / 12 : ℝ) : ℂ) = P from rfl, hP1, hP2, hP3]
  field_simp [h1z]
  push_cast at hode ⊢
  linear_combination (576 * ζ * P * (1 - ζ ^ 3)) * hode

lemma y1_hasDerivAt {ζ : ℂ} (hζ : ζ ∈ Ω) :
    HasDerivAt y1
      (((1 - ζ ^ 3) ^ ((5 / 12 : ℝ) : ℂ) - (5 / 4 : ℂ) * ζ ^ 3 * (1 - ζ ^ 3) ^ ((-(7 / 12) : ℝ) : ℂ)) * I1 ζ +
        (1 - ζ ^ 3) ^ ((5 / 12 : ℝ) : ℂ) *
          (3 * ζ ^ 3 * deriv (eulerInt (3 / 4) (5 / 12) (4 / 3)) (ζ ^ 3))) ζ := by
  have h1 := hasDerivAt_one_sub_cube_cpow (α := 5 / 12) hζ
  have h2 := hasDerivAt_euler_comp_cube (a := 3 / 4) (b := 5 / 12) (c := 4 / 3)
    (by norm_num) (by norm_num) hζ
  have hprod := (h1.mul (hasDerivAt_id ζ)).mul h2
  refine hprod.congr_deriv ?_
  have heq : ((5 / 12 - 1 : ℝ) : ℂ) = ((-(7 / 12) : ℝ) : ℂ) := by norm_num
  rw [heq]; unfold I1; simp only [Pi.mul_apply, id_eq]; push_cast; ring

lemma y1_differentiableOn_Ω : DifferentiableOn ℂ y1 Ω := fun _ hζ =>
  (y1_hasDerivAt hζ).differentiableAt.differentiableWithinAt

lemma y1_ode {ζ : ℂ} (hζ : ζ ∈ Ω) :
    HasDerivAt (deriv y1) (-(35 / 16 : ℂ) * ζ / (1 - ζ ^ 3) ^ 2 * y1 ζ) ζ := by
  have heq : deriv y1 =ᶠ[𝓝 ζ] fun z =>
      ((1 - z ^ 3) ^ ((5 / 12 : ℝ) : ℂ) - (5 / 4 : ℂ) * z ^ 3 * (1 - z ^ 3) ^ ((-(7 / 12) : ℝ) : ℂ)) * I1 z +
        (1 - z ^ 3) ^ ((5 / 12 : ℝ) : ℂ) *
          (3 * z ^ 3 * deriv (eulerInt (3 / 4) (5 / 12) (4 / 3)) (z ^ 3)) := by
    filter_upwards [isOpen_Ω.mem_nhds hζ] with z hz
    exact (y1_hasDerivAt hz).deriv
  have hpow3 : HasDerivAt (fun z : ℂ => z ^ 3) (3 * ζ ^ 2) ζ := by
    simpa [Nat.cast_ofNat] using hasDerivAt_pow 3 ζ
  have hp1 := hasDerivAt_one_sub_cube_cpow (α := -(7 / 12)) hζ
  have hp2 := hasDerivAt_one_sub_cube_cpow (α := 5 / 12) hζ
  have hI1 := hasDerivAt_euler_comp_cube (a := 3 / 4) (b := 5 / 12) (c := 4 / 3)
    (by norm_num) (by norm_num) hζ
  have hI1' := hasDerivAt_deriv_euler_comp_cube (a := 3 / 4) (b := 5 / 12) (c := 4 / 3)
    (by norm_num) (by norm_num) hζ
  have hterm1 := (hp2.sub ((hpow3.const_mul (5 / 4 : ℂ)).mul hp1)).mul hI1
  have hterm2 := hp2.mul ((hpow3.const_mul (3 : ℂ)).mul hI1')
  have hsum := hterm1.add hterm2
  refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
  have h1z : 1 - ζ ^ 3 ≠ 0 := one_sub_cube_ne_zero hζ
  set P : ℂ := (1 - ζ ^ 3) ^ ((5 / 12 : ℝ) : ℂ)
  have hP1 : (1 - ζ ^ 3) ^ ((-(7 / 12) : ℝ) : ℂ) = P / (1 - ζ ^ 3) := by
    rw [eq_div_iff h1z]; simp only [P]
    rw [show ((5 / 12 : ℝ) : ℂ) = ((-(7 / 12) : ℝ) : ℂ) + 1 by norm_num,
      Complex.cpow_add _ _ h1z, Complex.cpow_one]
  have hP2 : (1 - ζ ^ 3) ^ ((-(7 / 12) - 1 : ℝ) : ℂ) = P / (1 - ζ ^ 3) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 h1z)]; simp only [P]
    rw [show ((5 / 12 : ℝ) : ℂ) = ((-(7 / 12) - 1 : ℝ) : ℂ) + 2 by norm_num,
      Complex.cpow_add _ _ h1z, Complex.cpow_two]
  have hP3 : (1 - ζ ^ 3) ^ ((5 / 12 - 1 : ℝ) : ℂ) = P / (1 - ζ ^ 3) := by
    rw [show ((5 / 12 - 1 : ℝ) : ℂ) = ((-(7 / 12) : ℝ) : ℂ) by norm_num]; exact hP1
  have hode := eulerInt_hypergeom_ode (a := 3 / 4) (b := 5 / 12) (c := 4 / 3)
    (by norm_num) (by norm_num) hζ
  unfold y1 I1
  simp only [Pi.mul_apply, Pi.sub_apply]
  rw [show (1 - ζ ^ 3) ^ ((5 / 12 : ℝ) : ℂ) = P from rfl, hP1, hP2, hP3]
  field_simp [h1z]
  push_cast at hode ⊢
  linear_combination (576 * ζ ^ 2 * P * (1 - ζ ^ 3)) * hode

/- ## 3. Wronskian Constancy and Nonvanishing Derivative of `u6` -/

def wronskian (f g : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  f ζ * deriv g ζ - deriv f ζ * g ζ

lemma wronskian_const_of_ode {f g : ℂ → ℂ} {S : Set ℂ} (hSo : IsOpen S) (hSc : IsPreconnected S)
    (hf : DifferentiableOn ℂ f S) (hg : DifferentiableOn ℂ g S)
    (hf2 : ∀ z ∈ S, HasDerivAt (deriv f) (-(35 / 16 : ℂ) * z / (1 - z ^ 3) ^ 2 * f z) z)
    (hg2 : ∀ z ∈ S, HasDerivAt (deriv g) (-(35 / 16 : ℂ) * z / (1 - z ^ 3) ^ 2 * g z) z)
    {z₀ z : ℂ} (hz₀ : z₀ ∈ S) (hz : z ∈ S) :
    wronskian f g z = wronskian f g z₀ := by
  have hdiff : ∀ w ∈ S, HasDerivAt (wronskian f g) 0 w := by
    intro w hw
    have hdf := (hf.differentiableAt (hSo.mem_nhds hw)).hasDerivAt
    have hdg := (hg.differentiableAt (hSo.mem_nhds hw)).hasDerivAt
    refine ((hdf.mul (hg2 w hw)).sub ((hf2 w hw).mul hdg)).congr_deriv ?_
    ring
  exact eq_const_of_deriv_eq_zero hSo hSc
    (fun w hw => (hdiff w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hdiff w hw).deriv) hz₀ hz

lemma wronskian_y0_y1 {ζ : ℂ} (hζ : ζ ∈ Ω) :
    wronskian y0 y1 ζ = I0 0 * I1 0 := by
  rw [wronskian_const_of_ode isOpen_Ω isPreconnected_Ω y0_differentiableOn_Ω y1_differentiableOn_Ω
    (fun _ hz => y0_ode hz) (fun _ hz => y1_ode hz) zero_mem_Ω hζ]
  unfold wronskian
  have hy00 : y0 0 = I0 0 := by simp [y0]
  have hy10 : y1 0 = 0 := by simp [y1]
  have hdy0 : deriv y0 0 = 0 := by
    rw [(y0_hasDerivAt zero_mem_Ω).deriv]; simp
  have hdy1 : deriv y1 0 = I1 0 := by
    rw [(y1_hasDerivAt zero_mem_Ω).deriv]; simp
  rw [hy00, hy10, hdy0, hdy1]; ring

lemma wronskian_y0_y1_ne_zero {ζ : ℂ} (hζ : ζ ∈ Ω) :
    wronskian y0 y1 ζ ≠ 0 := by
  rw [wronskian_y0_y1 hζ]
  exact mul_ne_zero (I0_ne_zero_of_norm_le_one (by simp)) (I1_ne_zero_of_norm_le_one (by simp))

lemma u6_eq_R_mul_y1_div_y0 {ζ : ℂ} (hζ : ζ ∈ Ω) :
    u6 ζ = (R : ℂ) * (y1 ζ / y0 ζ) := by
  have hP : (1 - ζ ^ 3) ^ ((5 / 12 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (one_sub_cube_ne_zero hζ)]
    exact Complex.exp_ne_zero _
  unfold u6 y0 y1
  field_simp [hP]

lemma u6_hasDerivAt_of_I0_ne_zero {ζ : ℂ} (hζ : ζ ∈ Ω) (hI0 : I0 ζ ≠ 0) :
    HasDerivAt u6 ((R : ℂ) * (I0 0 * I1 0) / y0 ζ ^ 2) ζ := by
  have hy0_ne : y0 ζ ≠ 0 := by
    unfold y0
    refine mul_ne_zero ?_ hI0
    rw [Complex.cpow_def_of_ne_zero (one_sub_cube_ne_zero hζ)]
    exact Complex.exp_ne_zero _
  have h1 := (y1_hasDerivAt hζ)
  have h0 := (y0_hasDerivAt hζ)
  have hq := (h1.div h0 hy0_ne).const_mul (R : ℂ)
  have heq : u6 =ᶠ[𝓝 ζ] fun z => (R : ℂ) * (y1 z / y0 z) := by
    filter_upwards [isOpen_Ω.mem_nhds hζ] with z hz
    exact u6_eq_R_mul_y1_div_y0 hz
  refine (hq.congr_of_eventuallyEq heq).congr_deriv ?_
  have hw := wronskian_y0_y1 hζ
  rw [← h1.deriv, ← h0.deriv]
  unfold wronskian at hw
  have hnum : deriv y1 ζ * y0 ζ - y1 ζ * deriv y0 ζ = I0 0 * I1 0 := by
    linear_combination hw
  rw [hnum]; ring

lemma u6_deriv_ne_zero_of_I0_ne_zero {ζ : ℂ} (hζ : ζ ∈ Ω) (hI0 : I0 ζ ≠ 0) :
    deriv u6 ζ ≠ 0 := by
  rw [(u6_hasDerivAt_of_I0_ne_zero hζ hI0).deriv]
  have hy0_ne : y0 ζ ≠ 0 := by
    unfold y0
    refine mul_ne_zero ?_ hI0
    rw [Complex.cpow_def_of_ne_zero (one_sub_cube_ne_zero hζ)]
    exact Complex.exp_ne_zero _
  exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr R_ne_zero)
    (mul_ne_zero (I0_ne_zero_of_norm_le_one (by simp)) (I1_ne_zero_of_norm_le_one (by simp))))
    (pow_ne_zero 2 hy0_ne)

lemma u6_differentiableOn_ball : DifferentiableOn ℂ u6 (ball 0 1) := fun ζ hζ => by
  have h1 : ‖ζ‖ ≤ 1 := (le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hζ))
  exact (u6_hasDerivAt_of_I0_ne_zero (ball_subset_Ω hζ)
    (I0_ne_zero_of_norm_le_one h1)).differentiableAt.differentiableWithinAt

/- ## 4. Open Sector `Ω0` and the Reflection Law for `u6` -/

/-- Open sector `{0 < arg ζ < 2π/3}`. -/
def Ω0 : Set ℂ := {ζ : ℂ | 0 < ζ.im ∧ (ω ^ 2 * ζ).im < 0}

lemma isOpen_Ω0 : IsOpen Ω0 :=
  (isOpen_Ioi.preimage Complex.continuous_im).inter
    (isOpen_Iio.preimage (Complex.continuous_im.comp (continuous_const.mul continuous_id)))

lemma convex_Ω0 : Convex ℝ Ω0 := by
  intro x hx y hy a b ha hb hab
  have hpos : 0 < a ∨ 0 < b := by
    by_contra h; push Not at h; linarith
  refine ⟨?_, ?_⟩
  · simp only [add_im, Complex.real_smul, Complex.im_ofReal_mul]
    rcases hpos with ha' | hb'
    · nlinarith [hx.1, hy.1]
    · nlinarith [hx.1, hy.1]
  · simp only [mul_add, add_im, Complex.real_smul, mul_left_comm (ω ^ 2), Complex.im_ofReal_mul]
    rcases hpos with ha' | hb'
    · nlinarith [hx.2, hy.2]
    · nlinarith [hx.2, hy.2]

lemma isPreconnected_Ω0 : IsPreconnected Ω0 := convex_Ω0.isPreconnected

lemma Ω0_ne_zero {ζ : ℂ} (hζ : ζ ∈ Ω0) : ζ ≠ 0 := by
  intro h; have := hζ.1; rw [h, zero_im] at this; linarith

lemma exp_I_mem_Ω0 {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * Real.pi / 3) :
    Complex.exp ((θ : ℂ) * I) ∈ Ω0 := by
  refine ⟨?_, ?_⟩
  · rw [Complex.exp_mul_I, add_im, Complex.cos_ofReal_im, mul_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, I_re, I_im]
    simp only [mul_one, mul_zero, add_zero, zero_add]
    exact Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  · have hω2 : ω ^ 2 = Complex.exp (((-(2 * Real.pi / 3) : ℝ) : ℂ) * I) := by
      rw [← star_ω, ω_eq_exp, ← Complex.exp_conj]
      congr 1; simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, ofReal_neg]; ring
    rw [hω2, ← Complex.exp_add, show (((-(2 * Real.pi / 3) : ℝ) : ℂ) * I + (θ : ℂ) * I) =
        ((θ - 2 * Real.pi / 3 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    simp only [add_im, Complex.cos_ofReal_im, mul_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      I_re, I_im, mul_one, mul_zero, add_zero, zero_add]
    have hneg : 0 < Real.sin (2 * Real.pi / 3 - θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    rw [show θ - 2 * Real.pi / 3 = -(2 * Real.pi / 3 - θ) by ring, Real.sin_neg]
    linarith

lemma Ω0_subset_Ω : Ω0 ⊆ Ω := by
  intro ζ hζ ⟨hre, him⟩
  have hne : ζ ≠ 0 := Ω0_ne_zero hζ
  have harg_pos : 0 < Complex.arg ζ := by
    by_contra hle; push Not at hle
    have hsin_le : Real.sin (Complex.arg ζ) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le hle (Complex.neg_pi_lt_arg ζ).le
    have hsin_eq := Complex.sin_arg ζ
    have hnorm : 0 < ‖ζ‖ := norm_pos_iff.mpr hne
    have : 0 < ζ.im / ‖ζ‖ := div_pos hζ.1 hnorm
    linarith
  have harg_lt : Complex.arg ζ < 2 * Real.pi / 3 := by
    have him2 : -(1 / 2 : ℝ) * ζ.im - (Real.sqrt 3 / 2) * ζ.re < 0 := by
      have h := hζ.2
      rw [ω_sq, mul_im] at h
      linarith
    have hcos23 : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
      rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
        Real.cos_pi_div_three]
    have hsin23 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
      rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
        Real.sin_pi_div_three]
    have htrig : Real.sin (Complex.arg ζ - 2 * Real.pi / 3) < 0 := by
      rw [Real.sin_sub, hcos23, hsin23, Complex.cos_arg hne, Complex.sin_arg ζ]
      have hnorm : 0 < ‖ζ‖ := norm_pos_iff.mpr hne
      have hdiv : ζ.im / ‖ζ‖ * -(1 / 2) - ζ.re / ‖ζ‖ * (Real.sqrt 3 / 2) =
          (-(1 / 2) * ζ.im - (Real.sqrt 3 / 2) * ζ.re) / ‖ζ‖ := by ring
      rw [hdiv]
      exact div_neg_of_neg_of_pos him2 hnorm
    by_contra hge
    push Not at hge
    have hlt_pi : Complex.arg ζ < Real.pi := by
      have hle := Complex.arg_le_pi ζ
      rcases eq_or_lt_of_le hle with heq | hlt
      · have := Complex.arg_eq_pi_iff.mp heq
        linarith [hζ.1, this.2]
      · exact hlt
    have hsin_nn : 0 ≤ Real.sin (Complex.arg ζ - 2 * Real.pi / 3) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
    linarith
  have hpolar : ζ = (‖ζ‖ : ℂ) * Complex.exp ((Complex.arg ζ : ℂ) * I) :=
    (Complex.norm_mul_exp_arg_mul_I ζ).symm
  have hcube : ζ ^ 3 = ((‖ζ‖ ^ 3 : ℝ) : ℂ) * Complex.exp (((3 * Complex.arg ζ : ℝ) : ℂ) * I) := by
    conv_lhs => rw [hpolar]
    rw [mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul]
    congr 2; push_cast; ring
  rw [hcube, Complex.exp_mul_I] at hre him
  simp only [add_re, add_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im, mul_re, mul_im,
    Complex.sin_ofReal_re, Complex.sin_ofReal_im, I_re, I_im, ofReal_re, ofReal_im,
    mul_zero, zero_mul, mul_one, sub_self, sub_zero, add_zero, zero_add] at hre him
  have hn3 : 0 < ‖ζ‖ ^ 3 := pow_pos (norm_pos_iff.mpr hne) 3
  have hsin0 : Real.sin (3 * Complex.arg ζ) = 0 := (mul_eq_zero.mp him).resolve_left hn3.ne'
  have h3arg_eq_pi : 3 * Complex.arg ζ = Real.pi := by
    by_contra hne_pi
    rcases lt_or_gt_of_ne hne_pi with hlt | hgt
    · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) hlt).ne' hsin0
    · have hneg : Real.sin (3 * Complex.arg ζ) < 0 := by
        rw [show 3 * Complex.arg ζ = (3 * Complex.arg ζ - Real.pi) + Real.pi by ring, Real.sin_add_pi]
        have := Real.sin_pos_of_pos_of_lt_pi (x := 3 * Complex.arg ζ - Real.pi) (by linarith) (by linarith)
        linarith
      exact hneg.ne hsin0
  rw [h3arg_eq_pi, Real.cos_pi] at hre
  nlinarith

lemma Ω0_inv_conj {ζ : ℂ} (hζ : ζ ∈ Ω0) : 1 / starRingEnd ℂ ζ ∈ Ω0 := by
  have hne : ζ ≠ 0 := Ω0_ne_zero hζ
  have heq : 1 / starRingEnd ℂ ζ = (((‖ζ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ζ := by
    have hmul : ζ * starRingEnd ℂ ζ = ((‖ζ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, ← Complex.sq_norm]
    have hns : ((‖ζ‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
    have hcne : starRingEnd ℂ ζ ≠ 0 := (map_ne_zero _).mpr hne
    rw [div_eq_iff hcne, mul_assoc, hmul, Complex.ofReal_inv, inv_mul_cancel₀ hns]
  rw [heq]
  have hpos : 0 < (‖ζ‖ ^ 2)⁻¹ := inv_pos.mpr (pow_pos (norm_pos_iff.mpr hne) 2)
  refine ⟨?_, ?_⟩
  · rw [Complex.im_ofReal_mul]; exact mul_pos hpos hζ.1
  · rw [mul_left_comm, Complex.im_ofReal_mul]; exact mul_neg_of_pos_of_neg hpos hζ.2

lemma Ω0_symm {ζ : ℂ} (hζ : ζ ∈ Ω0) : ω * starRingEnd ℂ ζ ∈ Ω0 := by
  refine ⟨?_, ?_⟩
  · have h : starRingEnd ℂ (ω * starRingEnd ℂ ζ) = ω ^ 2 * ζ := by
      simp [star_ω]
    have him := congrArg Complex.im h
    simp only [conj_im] at him
    linarith [hζ.2]
  · have h : ω ^ 2 * (ω * starRingEnd ℂ ζ) = starRingEnd ℂ ζ := by
      calc ω ^ 2 * (ω * starRingEnd ℂ ζ) = ω ^ 3 * starRingEnd ℂ ζ := by ring
        _ = starRingEnd ℂ ζ := by rw [ω_cube, one_mul]
    rw [h, conj_im]
    linarith [hζ.1]

/-- Inverted solutions `ỹ_j(ζ) = ζ * conj (y_j (1 / conj ζ))` on `Ω0`. -/
def y0Tilde (ζ : ℂ) : ℂ := ζ * starRingEnd ℂ (y0 (1 / starRingEnd ℂ ζ))
def y1Tilde (ζ : ℂ) : ℂ := ζ * starRingEnd ℂ (y1 (1 / starRingEnd ℂ ζ))

lemma tilde_ode {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω0)
    (hf2 : ∀ z ∈ Ω0, HasDerivAt (deriv f) (-(35 / 16 : ℂ) * z / (1 - z ^ 3) ^ 2 * f z) z) :
    DifferentiableOn ℂ (fun ζ => ζ * starRingEnd ℂ (f (1 / starRingEnd ℂ ζ))) Ω0 ∧
    ∀ ζ ∈ Ω0, HasDerivAt (deriv (fun w => w * starRingEnd ℂ (f (1 / starRingEnd ℂ w))))
      (-(35 / 16 : ℂ) * ζ / (1 - ζ ^ 3) ^ 2 * (ζ * starRingEnd ℂ (f (1 / starRingEnd ℂ ζ)))) ζ := by
  have hd1 : ∀ ζ ∈ Ω0,
      HasDerivAt (fun w => w * starRingEnd ℂ (f (1 / starRingEnd ℂ w)))
        (starRingEnd ℂ (f (1 / starRingEnd ℂ ζ)) -
          starRingEnd ℂ (deriv f (1 / starRingEnd ℂ ζ)) / ζ) ζ := by
    intro ζ hζ
    have hne : ζ ≠ 0 := Ω0_ne_zero hζ
    have hζ' : 1 / starRingEnd ℂ ζ ∈ Ω0 := Ω0_inv_conj hζ
    have hdf := (hf.differentiableAt (isOpen_Ω0.mem_nhds hζ')).hasDerivAt
    have hg := hasDerivAt_inv_conj hne hdf
    refine ((hasDerivAt_id ζ).mul hg).congr_deriv ?_
    simp only [id_eq]; field_simp [hne]; ring
  refine ⟨fun ζ hζ => (hd1 ζ hζ).differentiableAt.differentiableWithinAt, fun ζ hζ => ?_⟩
  have hne : ζ ≠ 0 := Ω0_ne_zero hζ
  have hζ' : 1 / starRingEnd ℂ ζ ∈ Ω0 := Ω0_inv_conj hζ
  have heq : deriv (fun w => w * starRingEnd ℂ (f (1 / starRingEnd ℂ w))) =ᶠ[𝓝 ζ]
      fun w => starRingEnd ℂ (f (1 / starRingEnd ℂ w)) -
        starRingEnd ℂ (deriv f (1 / starRingEnd ℂ w)) / w := by
    filter_upwards [isOpen_Ω0.mem_nhds hζ] with w hw
    exact (hd1 w hw).deriv
  have hdf := (hf.differentiableAt (isOpen_Ω0.mem_nhds hζ')).hasDerivAt
  have hg1 := hasDerivAt_inv_conj hne hdf
  have hg2 := hasDerivAt_inv_conj hne (hf2 _ hζ')
  have hquot := hg2.div (hasDerivAt_id ζ) hne
  have hsub := hg1.sub hquot
  refine (hsub.congr_of_eventuallyEq heq).congr_deriv ?_
  have h1z : 1 - ζ ^ 3 ≠ 0 := one_sub_cube_ne_zero (Ω0_subset_Ω hζ)
  have h1z_neg : ζ ^ 3 - 1 ≠ 0 := by intro h; apply h1z; linear_combination -h
  simp only [id_eq, map_mul, map_div₀, map_neg, map_sub, map_pow, map_one, map_ofNat,
    RingHomCompTriple.comp_apply, RingHom.id_apply]
  have h1z_inv : 1 - (1 / ζ) ^ 3 = (ζ ^ 3 - 1) / ζ ^ 3 := by field_simp [hne]
  rw [h1z_inv]
  field_simp [hne, h1z, h1z_neg]
  ring

lemma y0Tilde_ode :
    DifferentiableOn ℂ y0Tilde Ω0 ∧
    ∀ ζ ∈ Ω0, HasDerivAt (deriv y0Tilde) (-(35 / 16 : ℂ) * ζ / (1 - ζ ^ 3) ^ 2 * y0Tilde ζ) ζ :=
  tilde_ode (y0_differentiableOn_Ω.mono Ω0_subset_Ω) (fun _ hz => y0_ode (Ω0_subset_Ω hz))

lemma y1Tilde_ode :
    DifferentiableOn ℂ y1Tilde Ω0 ∧
    ∀ ζ ∈ Ω0, HasDerivAt (deriv y1Tilde) (-(35 / 16 : ℂ) * ζ / (1 - ζ ^ 3) ^ 2 * y1Tilde ζ) ζ :=
  tilde_ode (y1_differentiableOn_Ω.mono Ω0_subset_Ω) (fun _ hz => y1_ode (Ω0_subset_Ω hz))

lemma y0_symm {ζ : ℂ} (hζ : ζ ∈ Ω0) :
    y0 (ω * starRingEnd ℂ ζ) = starRingEnd ℂ (y0 ζ) := by
  have hcube : (ω * starRingEnd ℂ ζ) ^ 3 = starRingEnd ℂ (ζ ^ 3) := by
    rw [mul_pow, ω_cube, one_mul, map_pow]
  have harg : (1 - ζ ^ 3).arg ≠ Real.pi := by
    have hs := one_sub_cube_mem_slitPlane (Ω0_subset_Ω hζ)
    rw [Complex.mem_slitPlane_iff] at hs
    intro hpi
    have := Complex.arg_eq_pi_iff.mp hpi
    rcases hs with h | h
    · linarith [this.1]
    · exact h this.2
  unfold y0
  have hI0 : I0 (ω * starRingEnd ℂ ζ) = starRingEnd ℂ (I0 ζ) := by
    unfold I0
    rw [hcube]
    exact eulerInt_conj (Or.inl (Ω0_subset_Ω hζ))
      (eulerIntegrand_integrable_of_slitSet (by norm_num) (by norm_num) (Ω0_subset_Ω hζ))
  rw [hcube, hI0, map_mul]
  congr 1
  have hcp := Complex.conj_cpow (1 - ζ ^ 3) ((5 / 12 : ℝ) : ℂ) harg
  rw [Complex.conj_ofReal] at hcp
  simpa using hcp

lemma y1_symm {ζ : ℂ} (hζ : ζ ∈ Ω0) :
    y1 (ω * starRingEnd ℂ ζ) = ω * starRingEnd ℂ (y1 ζ) := by
  have hcube : (ω * starRingEnd ℂ ζ) ^ 3 = starRingEnd ℂ (ζ ^ 3) := by
    rw [mul_pow, ω_cube, one_mul, map_pow]
  have harg : (1 - ζ ^ 3).arg ≠ Real.pi := by
    have hs := one_sub_cube_mem_slitPlane (Ω0_subset_Ω hζ)
    rw [Complex.mem_slitPlane_iff] at hs
    intro hpi
    have := Complex.arg_eq_pi_iff.mp hpi
    rcases hs with h | h
    · linarith [this.1]
    · exact h this.2
  unfold y1
  have hI1 : I1 (ω * starRingEnd ℂ ζ) = starRingEnd ℂ (I1 ζ) := by
    unfold I1
    rw [hcube]
    exact eulerInt_conj (Or.inl (Ω0_subset_Ω hζ))
      (eulerIntegrand_integrable_of_slitSet (by norm_num) (by norm_num) (Ω0_subset_Ω hζ))
  rw [hcube, hI1]
  have hcp := Complex.conj_cpow (1 - ζ ^ 3) ((5 / 12 : ℝ) : ℂ) harg
  rw [Complex.conj_ofReal] at hcp
  have hcp' : (1 - starRingEnd ℂ (ζ ^ 3)) ^ ((5 / 12 : ℝ) : ℂ) =
      starRingEnd ℂ ((1 - ζ ^ 3) ^ ((5 / 12 : ℝ) : ℂ)) := by
    simpa using hcp
  rw [hcp']
  simp only [map_mul]
  ring

lemma y0Tilde_symm {ζ : ℂ} (hζ : ζ ∈ Ω0) :
    y0Tilde (ω * starRingEnd ℂ ζ) = ω * starRingEnd ℂ (y0Tilde ζ) := by
  unfold y0Tilde
  have hinv : 1 / starRingEnd ℂ (ω * starRingEnd ℂ ζ) = ω * starRingEnd ℂ (1 / starRingEnd ℂ ζ) := by
    have h1 : ω * ω ^ 2 = 1 := by linear_combination ω_cube
    have hne : ζ ≠ 0 := Ω0_ne_zero hζ
    simp only [map_mul, star_ω, map_div₀, map_one, RingHomCompTriple.comp_apply, RingHom.id_apply]
    field_simp [hne, ω_ne_zero]
    linear_combination -ω_cube
  rw [hinv, y0_symm (Ω0_inv_conj hζ)]
  simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

lemma y1Tilde_symm {ζ : ℂ} (hζ : ζ ∈ Ω0) :
    y1Tilde (ω * starRingEnd ℂ ζ) = starRingEnd ℂ (y1Tilde ζ) := by
  unfold y1Tilde
  have hinv : 1 / starRingEnd ℂ (ω * starRingEnd ℂ ζ) = ω * starRingEnd ℂ (1 / starRingEnd ℂ ζ) := by
    have hne : ζ ≠ 0 := Ω0_ne_zero hζ
    simp only [map_mul, star_ω, map_div₀, map_one, RingHomCompTriple.comp_apply, RingHom.id_apply]
    field_simp [hne, ω_ne_zero]
    linear_combination -ω_cube
  rw [hinv, y1_symm (Ω0_inv_conj hζ)]
  simp only [map_mul, star_ω, RingHomCompTriple.comp_apply, RingHom.id_apply]
  linear_combination starRingEnd ℂ ζ * y1 (1 / starRingEnd ℂ ζ) * ω_cube

lemma cpow_one_sub_exp_ratio {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * Real.pi / 3) :
    starRingEnd ℂ ((1 - Complex.exp ((θ : ℂ) * I) ^ 3) ^ ((5 / 12 : ℝ) : ℂ)) /
        (1 - Complex.exp ((θ : ℂ) * I) ^ 3) ^ ((5 / 12 : ℝ) : ℂ) =
      Complex.exp ((((5 * Real.pi / 12 - 5 * θ / 4 : ℝ) : ℂ)) * I) := by
  -- Factor `1 - e^(3iθ) = (2 * sin (3θ/2)) * e^(i(3θ/2 - π/2))`!
  have hsin : 0 < 2 * Real.sin (3 * θ / 2) := by
    have := Real.sin_pos_of_pos_of_lt_pi (x := 3 * θ / 2) (by linarith) (by linarith)
    linarith
  have hfac : 1 - Complex.exp ((θ : ℂ) * I) ^ 3 =
      ((2 * Real.sin (3 * θ / 2) : ℝ) : ℂ) *
        Complex.exp ((((3 * θ / 2 - Real.pi / 2 : ℝ) : ℂ)) * I) := by
    rw [← Complex.exp_nat_mul]
    rw [show (3 : ℕ) * ((θ : ℂ) * I) = ((3 * θ : ℝ) : ℂ) * I by push_cast; ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    apply Complex.ext
    · simp only [sub_re, one_re, add_re, Complex.cos_ofReal_re, mul_re, Complex.sin_ofReal_re,
        Complex.sin_ofReal_im, I_re, I_im, ofReal_re, ofReal_im, mul_zero, mul_one,
        add_zero, sub_self]
      rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, zero_add, mul_one]
      have hdouble := Real.cos_two_mul (3 * θ / 2)
      rw [show 2 * (3 * θ / 2) = 3 * θ by ring] at hdouble
      have hsq := Real.sin_sq_add_cos_sq (3 * θ / 2)
      nlinarith
    · simp only [sub_im, one_im, add_im, Complex.cos_ofReal_im, mul_im, Complex.sin_ofReal_re,
        Complex.sin_ofReal_im, I_re, I_im, ofReal_re, ofReal_im, mul_zero, mul_one, zero_add,
        add_zero, zero_sub]
      rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, zero_sub, mul_one]
      have hdouble := Real.sin_two_mul (3 * θ / 2)
      rw [show 2 * (3 * θ / 2) = 3 * θ by ring] at hdouble
      nlinarith
  have harg_eq : Complex.arg (1 - Complex.exp ((θ : ℂ) * I) ^ 3) = 3 * θ / 2 - Real.pi / 2 := by
    rw [hfac, Complex.arg_real_mul _ hsin, Complex.arg_exp_mul_I]
    rw [toIocMod_eq_self]
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hne : 1 - Complex.exp ((θ : ℂ) * I) ^ 3 ≠ 0 :=
    one_sub_cube_ne_zero (Ω0_subset_Ω (exp_I_mem_Ω0 h0 h1))
  have hnorm : ‖1 - Complex.exp ((θ : ℂ) * I) ^ 3‖ = 2 * Real.sin (3 * θ / 2) := by
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsin.le, Complex.norm_exp_ofReal_mul_I,
      mul_one]
  have hcpow : (1 - Complex.exp ((θ : ℂ) * I) ^ 3) ^ ((5 / 12 : ℝ) : ℂ) =
      (((2 * Real.sin (3 * θ / 2)) ^ (5 / 12 : ℝ) : ℝ) : ℂ) *
        Complex.exp ((((5 / 12 * (3 * θ / 2 - Real.pi / 2) : ℝ) : ℂ)) * I) := by
    rw [Complex.cpow_def_of_ne_zero hne, Complex.log, hnorm, harg_eq, add_mul, Complex.exp_add]
    congr 1
    · rw [Real.rpow_def_of_pos hsin, Complex.ofReal_exp]
      congr 1; push_cast; ring
    · congr 1; push_cast; ring
  rw [hcpow, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have hrpos : (((2 * Real.sin (3 * θ / 2)) ^ (5 / 12 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hsin _).ne'
  rw [mul_div_mul_left _ _ hrpos, ← Complex.exp_sub]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-- Exact Möbius reflection law for `u6` on `Ω0`! -/
lemma u6_reflection_law {ζ : ℂ} (hζ : ζ ∈ Ω0) (hI0 : I0 ζ ≠ 0) (hI0' : I0 (1 / starRingEnd ℂ ζ) ≠ 0) :
    u6 (1 / starRingEnd ℂ ζ) = hypRefl 0 (u6 ζ) := by
  -- Step 1: Express `y1Tilde` and `y0Tilde` as constant linear combinations of `y1, y0` on `Ω0`.
  have hζ₀ : Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I) ∈ Ω0 :=
    exp_I_mem_Ω0 (by positivity) (by linarith [Real.pi_pos])
  set W0 : ℂ := I0 0 * I1 0
  have hW0 : W0 ≠ 0 := mul_ne_zero (I0_ne_zero_of_norm_le_one (by simp)) (I1_ne_zero_of_norm_le_one (by simp))
  set a : ℂ := wronskian y0 y1Tilde (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I)) / W0
  set b : ℂ := wronskian y1Tilde y1 (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I)) / W0
  set c : ℂ := wronskian y0 y0Tilde (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I)) / W0
  set d : ℂ := wronskian y0Tilde y1 (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I)) / W0
  have hlin1 : ∀ z ∈ Ω0, y1Tilde z = a * y1 z + b * y0 z := by
    intro z hz
    have hw1 : wronskian y0 y1Tilde z = a * W0 := by
      rw [div_mul_cancel₀ _ hW0]
      exact wronskian_const_of_ode isOpen_Ω0 isPreconnected_Ω0
        (y0_differentiableOn_Ω.mono Ω0_subset_Ω) y1Tilde_ode.1
        (fun _ hw => y0_ode (Ω0_subset_Ω hw)) y1Tilde_ode.2 hζ₀ hz
    have hw2 : wronskian y1Tilde y1 z = b * W0 := by
      rw [div_mul_cancel₀ _ hW0]
      exact wronskian_const_of_ode isOpen_Ω0 isPreconnected_Ω0
        y1Tilde_ode.1 (y1_differentiableOn_Ω.mono Ω0_subset_Ω)
        y1Tilde_ode.2 (fun _ hw => y1_ode (Ω0_subset_Ω hw)) hζ₀ hz
    have hw0 : wronskian y0 y1 z = W0 := wronskian_y0_y1 (Ω0_subset_Ω hz)
    have hcramer : wronskian y0 y1 z * y1Tilde z =
        wronskian y0 y1Tilde z * y1 z + wronskian y1Tilde y1 z * y0 z := by
      unfold wronskian; ring
    rw [hw0, hw1, hw2] at hcramer
    exact mul_left_cancel₀ hW0 (by linear_combination hcramer)
  have hlin0 : ∀ z ∈ Ω0, y0Tilde z = c * y1 z + d * y0 z := by
    intro z hz
    have hw1 : wronskian y0 y0Tilde z = c * W0 := by
      rw [div_mul_cancel₀ _ hW0]
      exact wronskian_const_of_ode isOpen_Ω0 isPreconnected_Ω0
        (y0_differentiableOn_Ω.mono Ω0_subset_Ω) y0Tilde_ode.1
        (fun _ hw => y0_ode (Ω0_subset_Ω hw)) y0Tilde_ode.2 hζ₀ hz
    have hw2 : wronskian y0Tilde y1 z = d * W0 := by
      rw [div_mul_cancel₀ _ hW0]
      exact wronskian_const_of_ode isOpen_Ω0 isPreconnected_Ω0
        y0Tilde_ode.1 (y1_differentiableOn_Ω.mono Ω0_subset_Ω)
        y0Tilde_ode.2 (fun _ hw => y1_ode (Ω0_subset_Ω hw)) hζ₀ hz
    have hw0 : wronskian y0 y1 z = W0 := wronskian_y0_y1 (Ω0_subset_Ω hz)
    have hcramer : wronskian y0 y1 z * y0Tilde z =
        wronskian y0 y0Tilde z * y1 z + wronskian y0Tilde y1 z * y0 z := by
      unfold wronskian; ring
    rw [hw0, hw1, hw2] at hcramer
    exact mul_left_cancel₀ hW0 (by linear_combination hcramer)
  -- Step 2: Linear independence of `y1, y0` on `Ω0`!
  have hli : ∀ α β : ℂ, (∀ z ∈ Ω0, α * y1 z + β * y0 z = 0) → α = 0 ∧ β = 0 := by
    intro α β hall
    have hderiv0 : α * deriv y1 (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I)) +
        β * deriv y0 (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I)) = 0 := by
      have hd1 := (y1_hasDerivAt (Ω0_subset_Ω hζ₀)).const_mul α
      have hd0 := (y0_hasDerivAt (Ω0_subset_Ω hζ₀)).const_mul β
      have hsum := hd1.add hd0
      have hzero : HasDerivAt (fun z => α * y1 z + β * y0 z) 0 (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I)) :=
        (hasDerivAt_const _ 0).congr_of_eventuallyEq
          (Filter.eventually_of_mem (isOpen_Ω0.mem_nhds hζ₀) hall)
      have heq := hsum.unique hzero
      rw [(y1_hasDerivAt (Ω0_subset_Ω hζ₀)).deriv, (y0_hasDerivAt (Ω0_subset_Ω hζ₀)).deriv]
      exact heq
    have hval0 := hall _ hζ₀
    have hw0 := wronskian_y0_y1_ne_zero (Ω0_subset_Ω hζ₀)
    unfold wronskian at hw0
    constructor
    · exact (mul_eq_zero.mp (show α * (y0 _ * deriv y1 _ - deriv y0 _ * y1 _) = 0 by
        linear_combination y0 _ * hderiv0 - deriv y0 _ * hval0)).resolve_right hw0
    · exact (mul_eq_zero.mp (show β * (y0 _ * deriv y1 _ - deriv y0 _ * y1 _) = 0 by
        linear_combination deriv y1 _ * hval0 - y1 _ * hderiv0)).resolve_right hw0
  -- Step 3: Symmetry `z ↦ ω * conj z` determines phases of `a, b, c, d`!
  have hsym1 : starRingEnd ℂ a * ω ^ 2 = a ∧ starRingEnd ℂ b = b := by
    have h := hli (starRingEnd ℂ a * ω ^ 2 - a) (starRingEnd ℂ b - b) fun z hz => by
      have h1 := congrArg (starRingEnd ℂ) (hlin1 (ω * starRingEnd ℂ z) (Ω0_symm hz))
      rw [y1Tilde_symm hz, y1_symm hz, y0_symm hz] at h1
      simp only [map_add, map_mul, star_ω, RingHomCompTriple.comp_apply, RingHom.id_apply] at h1
      have h2 := hlin1 z hz
      linear_combination h1.symm - h2.symm
    exact ⟨sub_eq_zero.mp h.1, sub_eq_zero.mp h.2⟩
  have hsym0 : starRingEnd ℂ c = c ∧ ω * starRingEnd ℂ d = d := by
    have h := hli (starRingEnd ℂ c - c) (ω * starRingEnd ℂ d - d) fun z hz => by
      have h1 := congrArg (starRingEnd ℂ) (hlin0 (ω * starRingEnd ℂ z) (Ω0_symm hz))
      rw [y0Tilde_symm hz, y1_symm hz, y0_symm hz] at h1
      simp only [map_add, map_mul, star_ω, RingHomCompTriple.comp_apply, RingHom.id_apply] at h1
      have h1' := congrArg (fun x => ω * x) h1
      have h2 := hlin0 z hz
      linear_combination (y0Tilde z - starRingEnd ℂ c * y1 z) * ω_cube + h1'.symm - h2.symm
    exact ⟨sub_eq_zero.mp h.1, sub_eq_zero.mp h.2⟩
  -- Step 4: Limit `θ → 0⁺` along `z = exp (θ * I)` gives `a + b = e^(5πi/12)` and `c + d = e^(5πi/12)`!
  have hlim_exp : Tendsto (fun θ : ℝ => Complex.exp ((θ : ℂ) * I)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * I)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim_I0 : Tendsto (fun θ : ℝ => I0 (Complex.exp ((θ : ℂ) * I))) (𝓝[>] (0 : ℝ)) (𝓝 (I0 1)) := by
    have hpow : MapsTo (fun ζ : ℂ => ζ ^ 3) (closedBall 0 1) (closedBall 0 1) := fun x hx => by
      have h1 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
      simpa [Metric.mem_closedBall, dist_zero_right, norm_pow] using pow_le_one₀ (norm_nonneg x) h1
    have hI0_cont : ContinuousOn I0 (closedBall 0 1) :=
      (eulerInt_continuousOn_closedBall (by norm_num) (by norm_num) (by norm_num)).comp
        (continuous_pow 3).continuousOn hpow
    have hmem : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), Complex.exp ((θ : ℂ) * I) ∈ closedBall (0 : ℂ) 1 :=
      Eventually.of_forall fun θ => by simp [Metric.mem_closedBall, dist_zero_right]
    have ht1 : Tendsto (fun θ : ℝ => Complex.exp ((θ : ℂ) * I)) (𝓝[>] (0 : ℝ)) (𝓝[closedBall 0 1] 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlim_exp hmem
    exact (hI0_cont 1 (by simp [Metric.mem_closedBall])).tendsto.comp ht1
  have hlim_I1 : Tendsto (fun θ : ℝ => I1 (Complex.exp ((θ : ℂ) * I))) (𝓝[>] (0 : ℝ)) (𝓝 (I1 1)) := by
    have hpow : MapsTo (fun ζ : ℂ => ζ ^ 3) (closedBall 0 1) (closedBall 0 1) := fun x hx => by
      have h1 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
      simpa [Metric.mem_closedBall, dist_zero_right, norm_pow] using pow_le_one₀ (norm_nonneg x) h1
    have hI1_cont : ContinuousOn I1 (closedBall 0 1) :=
      (eulerInt_continuousOn_closedBall (by norm_num) (by norm_num) (by norm_num)).comp
        (continuous_pow 3).continuousOn hpow
    have hmem : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ), Complex.exp ((θ : ℂ) * I) ∈ closedBall (0 : ℂ) 1 :=
      Eventually.of_forall fun θ => by simp [Metric.mem_closedBall, dist_zero_right]
    have ht1 : Tendsto (fun θ : ℝ => Complex.exp ((θ : ℂ) * I)) (𝓝[>] (0 : ℝ)) (𝓝[closedBall 0 1] 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlim_exp hmem
    exact (hI1_cont 1 (by simp [Metric.mem_closedBall])).tendsto.comp ht1
  have hI0_1_ne : I0 1 ≠ 0 := I0_ne_zero_of_norm_le_one (by simp)
  have hI0_1_conj : starRingEnd ℂ (I0 1) = I0 1 := by
    simpa using (I0_conj (ζ := 1) (Or.inr (by simp))).symm
  have hI1_1_conj : starRingEnd ℂ (I1 1) = I1 1 := by
    simpa using (I1_conj (ζ := 1) (Or.inr (by simp))).symm
  have hphase_lim : Tendsto (fun θ : ℝ =>
      Complex.exp ((((5 * Real.pi / 12 - 5 * θ / 4 : ℝ) : ℂ)) * I))
      (𝓝[>] (0 : ℝ)) (𝓝 (Complex.exp ((((5 * Real.pi / 12 : ℝ) : ℂ)) * I))) := by
    have hc : Continuous (fun θ : ℝ => Complex.exp ((((5 * Real.pi / 12 - 5 * θ / 4 : ℝ) : ℂ)) * I)) := by
      fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hinv_exp : ∀ θ : ℝ, 1 / starRingEnd ℂ (Complex.exp ((θ : ℂ) * I)) = Complex.exp ((θ : ℂ) * I) := by
    intro θ
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, one_div,
      ← Complex.exp_neg, neg_neg]
  have hI1_1_ne : I1 1 ≠ 0 := by rwa [← I0_one_eq_I1_one]
  have hab : a + b = Complex.exp ((((5 * Real.pi / 12 : ℝ) : ℂ)) * I) := by
    have hL : Tendsto (fun θ : ℝ => y1Tilde (Complex.exp ((θ : ℂ) * I)) / y0 (Complex.exp ((θ : ℂ) * I)))
        (𝓝[>] (0 : ℝ)) (𝓝 (a + b)) := by
      have hratio : Tendsto (fun θ : ℝ =>
          a * (Complex.exp ((θ : ℂ) * I) * (I1 (Complex.exp ((θ : ℂ) * I)) / I0 (Complex.exp ((θ : ℂ) * I)))) + b)
          (𝓝[>] (0 : ℝ)) (𝓝 (a + b)) := by
        have h1 := ((hlim_exp.mul (hlim_I1.div hlim_I0 hI0_1_ne)).const_mul a).add (tendsto_const_nhds (x := b))
        simpa [I0_one_eq_I1_one, div_self hI1_1_ne] using h1
      refine hratio.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * Real.pi / 3 by positivity)] with θ hθ
      have hmem := exp_I_mem_Ω0 hθ.1 hθ.2
      have hPne : (1 - Complex.exp ((θ : ℂ) * I) ^ 3) ^ ((5 / 12 : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (one_sub_cube_ne_zero (Ω0_subset_Ω hmem))]
        exact Complex.exp_ne_zero _
      have hI0ne : I0 (Complex.exp ((θ : ℂ) * I)) ≠ 0 :=
        I0_ne_zero_of_norm_le_one (by simp)
      rw [hlin1 _ hmem]
      unfold y0 y1
      field_simp [hPne, hI0ne]
    have hR : Tendsto (fun θ : ℝ => y1Tilde (Complex.exp ((θ : ℂ) * I)) / y0 (Complex.exp ((θ : ℂ) * I)))
        (𝓝[>] (0 : ℝ)) (𝓝 (Complex.exp ((((5 * Real.pi / 12 : ℝ) : ℂ)) * I))) := by
      have hprod : Tendsto (fun θ : ℝ =>
          Complex.exp ((((5 * Real.pi / 12 - 5 * θ / 4 : ℝ) : ℂ)) * I) *
            (starRingEnd ℂ (I1 (Complex.exp ((θ : ℂ) * I))) / I0 (Complex.exp ((θ : ℂ) * I))))
          (𝓝[>] (0 : ℝ)) (𝓝 (Complex.exp ((((5 * Real.pi / 12 : ℝ) : ℂ)) * I))) := by
        have h1 := hphase_lim.mul ((Complex.continuous_conj.tendsto _ |>.comp hlim_I1).div hlim_I0 hI0_1_ne)
        simpa [hI1_1_conj, I0_one_eq_I1_one, div_self hI1_1_ne] using h1
      refine hprod.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * Real.pi / 3 by positivity)] with θ hθ
      have hmem := exp_I_mem_Ω0 hθ.1 hθ.2
      have hPne : (1 - Complex.exp ((θ : ℂ) * I) ^ 3) ^ ((5 / 12 : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (one_sub_cube_ne_zero (Ω0_subset_Ω hmem))]
        exact Complex.exp_ne_zero _
      have hI0ne : I0 (Complex.exp ((θ : ℂ) * I)) ≠ 0 :=
        I0_ne_zero_of_norm_le_one (by simp)
      unfold y1Tilde y1 y0
      rw [hinv_exp]
      simp only [map_mul]
      have hce : Complex.exp ((θ : ℂ) * I) * starRingEnd ℂ (Complex.exp ((θ : ℂ) * I)) = 1 := by
        rw [Complex.mul_conj, ← Complex.sq_norm, Complex.norm_exp_ofReal_mul_I]; norm_num
      rw [← cpow_one_sub_exp_ratio hθ.1 hθ.2]
      calc starRingEnd ℂ ((1 - Complex.exp ((θ : ℂ) * I) ^ 3) ^ ((5 / 12 : ℝ) : ℂ)) /
            (1 - Complex.exp ((θ : ℂ) * I) ^ 3) ^ ((5 / 12 : ℝ) : ℂ) *
            (starRingEnd ℂ (I1 (Complex.exp ((θ : ℂ) * I))) / I0 (Complex.exp ((θ : ℂ) * I)))
          = (Complex.exp ((θ : ℂ) * I) * starRingEnd ℂ (Complex.exp ((θ : ℂ) * I))) *
            (starRingEnd ℂ ((1 - Complex.exp ((θ : ℂ) * I) ^ 3) ^ ((5 / 12 : ℝ) : ℂ)) *
              starRingEnd ℂ (I1 (Complex.exp ((θ : ℂ) * I)))) /
            ((1 - Complex.exp ((θ : ℂ) * I) ^ 3) ^ ((5 / 12 : ℝ) : ℂ) * I0 (Complex.exp ((θ : ℂ) * I))) := by
              rw [hce, one_mul]; ring
        _ = Complex.exp ((θ : ℂ) * I) *
            (starRingEnd ℂ ((1 - Complex.exp ((θ : ℂ) * I) ^ 3) ^ ((5 / 12 : ℝ) : ℂ)) *
              starRingEnd ℂ (Complex.exp ((θ : ℂ) * I)) *
              starRingEnd ℂ (I1 (Complex.exp ((θ : ℂ) * I)))) /
            ((1 - Complex.exp ((θ : ℂ) * I) ^ 3) ^ ((5 / 12 : ℝ) : ℂ) * I0 (Complex.exp ((θ : ℂ) * I))) := by
              ring
    exact tendsto_nhds_unique hL hR
  have hcd : c + d = Complex.exp ((((5 * Real.pi / 12 : ℝ) : ℂ)) * I) := by
    have hL : Tendsto (fun θ : ℝ => y0Tilde (Complex.exp ((θ : ℂ) * I)) / y0 (Complex.exp ((θ : ℂ) * I)))
        (𝓝[>] (0 : ℝ)) (𝓝 (c + d)) := by
      have hratio : Tendsto (fun θ : ℝ =>
          c * (Complex.exp ((θ : ℂ) * I) * (I1 (Complex.exp ((θ : ℂ) * I)) / I0 (Complex.exp ((θ : ℂ) * I)))) + d)
          (𝓝[>] (0 : ℝ)) (𝓝 (c + d)) := by
        have h1 := ((hlim_exp.mul (hlim_I1.div hlim_I0 hI0_1_ne)).const_mul c).add (tendsto_const_nhds (x := d))
        simpa [I0_one_eq_I1_one, div_self hI1_1_ne] using h1
      refine hratio.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * Real.pi / 3 by positivity)] with θ hθ
      have hmem := exp_I_mem_Ω0 hθ.1 hθ.2
      have hPne : (1 - Complex.exp ((θ : ℂ) * I) ^ 3) ^ ((5 / 12 : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (one_sub_cube_ne_zero (Ω0_subset_Ω hmem))]
        exact Complex.exp_ne_zero _
      have hI0ne : I0 (Complex.exp ((θ : ℂ) * I)) ≠ 0 :=
        I0_ne_zero_of_norm_le_one (by simp)
      rw [hlin0 _ hmem]
      unfold y0 y1
      field_simp [hPne, hI0ne]
    have hR : Tendsto (fun θ : ℝ => y0Tilde (Complex.exp ((θ : ℂ) * I)) / y0 (Complex.exp ((θ : ℂ) * I)))
        (𝓝[>] (0 : ℝ)) (𝓝 (Complex.exp ((((5 * Real.pi / 12 : ℝ) : ℂ)) * I))) := by
      have hprod : Tendsto (fun θ : ℝ =>
          Complex.exp ((θ : ℂ) * I) *
            Complex.exp ((((5 * Real.pi / 12 - 5 * θ / 4 : ℝ) : ℂ)) * I) *
            (starRingEnd ℂ (I0 (Complex.exp ((θ : ℂ) * I))) / I0 (Complex.exp ((θ : ℂ) * I))))
          (𝓝[>] (0 : ℝ)) (𝓝 (Complex.exp ((((5 * Real.pi / 12 : ℝ) : ℂ)) * I))) := by
        have h1 := (hlim_exp.mul hphase_lim).mul
          ((Complex.continuous_conj.tendsto _ |>.comp hlim_I0).div hlim_I0 hI0_1_ne)
        simpa [hI0_1_conj, div_self hI0_1_ne] using h1
      refine hprod.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * Real.pi / 3 by positivity)] with θ hθ
      unfold y0Tilde y0
      rw [hinv_exp, map_mul, ← cpow_one_sub_exp_ratio hθ.1 hθ.2]
      ring
    exact tendsto_nhds_unique hL hR
  -- Step 5: Solve explicitly for `(a, b, c, d)` and match to `hypRefl 0`!
  have hcos5 : Real.cos (5 * Real.pi / 12) = Real.sqrt 2 * (Real.sqrt 3 - 1) / 4 := by
    rw [show 5 * Real.pi / 12 = Real.pi / 4 + Real.pi / 6 by ring, Real.cos_add,
      Real.cos_pi_div_four, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.sin_pi_div_six]
    ring
  have hsin5 : Real.sin (5 * Real.pi / 12) = Real.sqrt 2 * (Real.sqrt 3 + 1) / 4 := by
    rw [show 5 * Real.pi / 12 = Real.pi / 4 + Real.pi / 6 by ring, Real.sin_add,
      Real.sin_pi_div_four, Real.cos_pi_div_six, Real.cos_pi_div_four, Real.sin_pi_div_six]
    ring
  have hexp5_re : (Complex.exp ((((5 * Real.pi / 12 : ℝ) : ℂ)) * I)).re =
      Real.sqrt 2 * (Real.sqrt 3 - 1) / 4 := by
    rw [Complex.exp_mul_I]
    simp only [add_re, Complex.cos_ofReal_re, mul_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      I_re, I_im, mul_zero, mul_one, sub_self, add_zero, hcos5]
  have hexp5_im : (Complex.exp ((((5 * Real.pi / 12 : ℝ) : ℂ)) * I)).im =
      Real.sqrt 2 * (Real.sqrt 3 + 1) / 4 := by
    rw [Complex.exp_mul_I]
    simp only [add_im, Complex.cos_ofReal_im, mul_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      I_re, I_im, mul_zero, mul_one, zero_add, add_zero, hsin5]
  have hb_im : b.im = 0 := by
    have := congrArg Complex.im hsym1.2; simp only [conj_im] at this; linarith
  have hc_im : c.im = 0 := by
    have := congrArg Complex.im hsym0.1; simp only [conj_im] at this; linarith
  have ha_im : a.im = Real.sqrt 2 * (Real.sqrt 3 + 1) / 4 := by
    have := congrArg Complex.im hab; simp only [add_im, hb_im, add_zero] at this
    linarith [hexp5_im]
  have hd_im : d.im = Real.sqrt 2 * (Real.sqrt 3 + 1) / 4 := by
    have := congrArg Complex.im hcd; simp only [add_im, hc_im, zero_add] at this
    linarith [hexp5_im]
  have ha_re : a.re = -Real.sqrt 2 * (3 + Real.sqrt 3) / 12 := by
    have hre := congrArg Complex.re hsym1.1
    rw [ω_sq, mul_re, conj_re, conj_im] at hre
    have h1 : 3 * a.re = -Real.sqrt 3 * a.im := by linarith
    rw [ha_im] at h1
    linear_combination (h1 - (Real.sqrt 2 / 4) * sq_sqrt3) / 3
  have hd_re : d.re = Real.sqrt 2 * (3 + Real.sqrt 3) / 12 := by
    have hre := congrArg Complex.re hsym0.2
    rw [mul_re, ω_re, ω_im, conj_re, conj_im] at hre
    have h1 : 3 * d.re = Real.sqrt 3 * d.im := by linarith
    rw [hd_im] at h1
    linear_combination (h1 + (Real.sqrt 2 / 4) * sq_sqrt3) / 3
  have hb_re : b.re = Real.sqrt 2 * Real.sqrt 3 / 3 := by
    have hre := congrArg Complex.re hab
    rw [add_re, hexp5_re, ha_re] at hre; linarith
  have hc_re : c.re = Real.sqrt 2 * (Real.sqrt 3 - 3) / 6 := by
    have hre := congrArg Complex.re hcd
    rw [add_re, hexp5_re, hd_re] at hre; linarith
  have hid1 : b * (R : ℂ) ^ 2 = -c := by
    apply Complex.ext
    · simp only [mul_re, ofReal_re, ofReal_im, hb_re, hb_im, hc_re, neg_re, pow_two,
        mul_zero, sub_zero]
      rw [show R * R = R ^ 2 by ring, R_sq]
      linear_combination (Real.sqrt 2 / 6) * sq_sqrt3
    · simp only [mul_im, ofReal_re, ofReal_im, hb_im, hc_im, neg_im, pow_two, mul_zero, add_zero,
        zero_mul, neg_zero]
  have hid2 : starRingEnd ℂ a * (R : ℂ) = c * a0 := by
    apply Complex.ext
    · simp only [mul_re, conj_re, conj_im, ofReal_re, ofReal_im, ha_re, ha_im, hc_re, hc_im,
        a0_re, a0_im, mul_zero, sub_zero, zero_mul]
      linear_combination -(Real.sqrt 2 * R / 12) * sq_sqrt3
    · simp only [mul_im, conj_re, conj_im, ofReal_re, ofReal_im, ha_re, ha_im, hc_re, hc_im,
        a0_re, a0_im, mul_zero, add_zero, zero_mul]
      linear_combination ((Real.sqrt 2 * R - Real.sqrt 2 * Real.sqrt 3 * R) / 12) * sq_sqrt3
  have hid3 : starRingEnd ℂ d * (R : ℂ) = -c * starRingEnd ℂ a0 := by
    apply Complex.ext
    · simp only [mul_re, conj_re, conj_im, ofReal_re, ofReal_im, hd_re, hd_im, hc_re, hc_im,
        a0_re, a0_im, neg_re, neg_im, mul_zero, sub_zero, zero_mul, neg_zero]
      linear_combination (Real.sqrt 2 * R / 12) * sq_sqrt3
    · simp only [mul_im, conj_re, conj_im, ofReal_re, ofReal_im, hd_re, hd_im, hc_re, hc_im,
        a0_re, a0_im, neg_re, neg_im, mul_zero, add_zero, zero_mul, neg_zero]
      linear_combination ((Real.sqrt 2 * R - Real.sqrt 2 * Real.sqrt 3 * R) / 12) * sq_sqrt3
  have hc_ne : c ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    rw [hc_re, zero_re] at hre
    have hsq2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hlt : Real.sqrt 3 < 3 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    nlinarith
  -- Step 6: Evaluate `u6 (1 / conj ζ)` using `hlin1`, `hlin0`, and `hid1, hid2, hid3`!
  have hζ' : 1 / starRingEnd ℂ ζ ∈ Ω0 := Ω0_inv_conj hζ
  have hy0_ne : y0 ζ ≠ 0 := by
    unfold y0
    refine mul_ne_zero ?_ hI0
    rw [Complex.cpow_def_of_ne_zero (one_sub_cube_ne_zero (Ω0_subset_Ω hζ))]
    exact Complex.exp_ne_zero _
  have hy0'_ne : y0 (1 / starRingEnd ℂ ζ) ≠ 0 := by
    unfold y0
    refine mul_ne_zero ?_ hI0'
    rw [Complex.cpow_def_of_ne_zero (one_sub_cube_ne_zero (Ω0_subset_Ω hζ'))]
    exact Complex.exp_ne_zero _
  have hne : ζ ≠ 0 := Ω0_ne_zero hζ
  have h1 := hlin1 ζ hζ
  have h0 := hlin0 ζ hζ
  have hratio_tilde : starRingEnd ℂ (u6 (1 / starRingEnd ℂ ζ)) =
      (a * u6 ζ + b * (R : ℂ)) * (R : ℂ) / (c * u6 ζ + d * (R : ℂ)) := by
    rw [u6_eq_R_mul_y1_div_y0 (Ω0_subset_Ω hζ'), u6_eq_R_mul_y1_div_y0 (Ω0_subset_Ω hζ)]
    have hy0T_ne : y0Tilde ζ ≠ 0 := by
      unfold y0Tilde; exact mul_ne_zero hne ((map_ne_zero _).mpr hy0'_ne)
    have hcy_ne : c * y1 ζ + d * y0 ζ ≠ 0 := by rwa [← h0]
    have hden_ne : c * ((R : ℂ) * (y1 ζ / y0 ζ)) + d * (R : ℂ) ≠ 0 := by
      have hfactor : c * ((R : ℂ) * (y1 ζ / y0 ζ)) + d * (R : ℂ) =
          (R : ℂ) * y0Tilde ζ / y0 ζ := by
        rw [h0]; field_simp [hy0_ne]
      rw [hfactor]
      exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr R_ne_zero) hy0T_ne) hy0_ne
    rw [eq_div_iff hden_ne]
    simp only [map_mul, map_div₀, Complex.conj_ofReal]
    have hy0T : starRingEnd ℂ (y0 (1 / starRingEnd ℂ ζ)) = y0Tilde ζ / ζ := by
      unfold y0Tilde; field_simp [hne]
    have hy1T : starRingEnd ℂ (y1 (1 / starRingEnd ℂ ζ)) = y1Tilde ζ / ζ := by
      unfold y1Tilde; field_simp [hne]
    rw [hy0T, hy1T, h0, h1]
    have hcy_ne' : y1 ζ * c + y0 ζ * d ≠ 0 := by simpa [mul_comm] using hcy_ne
    field_simp [hne, hy0_ne, hcy_ne, hcy_ne']
  -- Take complex conjugates of `hratio_tilde`!
  have hconj := congrArg (starRingEnd ℂ) hratio_tilde
  simp only [map_div₀, map_mul, map_add, Complex.conj_ofReal,
    RingHomCompTriple.comp_apply, RingHom.id_apply] at hconj
  rw [hconj]
  unfold hypRefl sideCenter
  simp only [Fin.val_zero, pow_zero, one_mul]
  have hnum_eq : (starRingEnd ℂ a * starRingEnd ℂ (u6 ζ) + starRingEnd ℂ b * (R : ℂ)) * (R : ℂ) =
      c * (a0 * starRingEnd ℂ (u6 ζ) - 1) := by
    rw [hsym1.2]
    linear_combination starRingEnd ℂ (u6 ζ) * hid2 + hid1
  have hden_eq : starRingEnd ℂ c * starRingEnd ℂ (u6 ζ) + starRingEnd ℂ d * (R : ℂ) =
      c * (starRingEnd ℂ (u6 ζ) - starRingEnd ℂ a0) := by
    rw [hsym0.1]
    linear_combination hid3
  rw [hnum_eq, hden_eq, mul_div_mul_left _ _ hc_ne]

/- ## 5. Boundary Mapping of `u6` onto `frontier Δ1Open` -/

lemma u6_arc_on_circle {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * Real.pi / 3) :
    ‖u6 (Complex.exp ((θ : ℂ) * I)) - sideCenter 0‖ ^ 2 = ‖sideCenter 0‖ ^ 2 - 1 := by
  have hmem := exp_I_mem_Ω0 h0 h1
  have hnorm1 : ‖Complex.exp ((θ : ℂ) * I)‖ ≤ 1 := by simp
  have hinv : 1 / starRingEnd ℂ (Complex.exp ((θ : ℂ) * I)) = Complex.exp ((θ : ℂ) * I) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, one_div,
      ← Complex.exp_neg, neg_neg]
  have hrefl := u6_reflection_law hmem (I0_ne_zero_of_norm_le_one hnorm1)
    (by rw [hinv]; exact I0_ne_zero_of_norm_le_one hnorm1)
  rw [hinv] at hrefl
  exact (hypRefl_fixed_iff 0 (norm_u6_lt_one hnorm1)).mp hrefl.symm

lemma circle_arc_mem_Δ1 {z : ℂ} (hz1 : ‖z‖ < 1)
    (hcirc : ‖z - sideCenter 0‖ ^ 2 = ‖sideCenter 0‖ ^ 2 - 1)
    (hy_lo : -(R * Real.sqrt 3 / 2) ≤ ((z - sideCenter 0) * starRingEnd ℂ (1 + ω)).im)
    (hy_hi : ((z - sideCenter 0) * starRingEnd ℂ (1 + ω)).im ≤ R * Real.sqrt 3 / 2) :
    z ∈ Δ1 := by
  -- Write `v = (z - a0) * conj(1 + ω) = x + i y`.
  -- Then `z = (a0_mag + x + i y) * (1 + ω)` where `a0_mag = (2 + √3) R`,
  -- `x^2 + y^2 = a0_mag^2 - 1`, and `x < 0` (since `‖z‖ < 1 < a0_mag`).
  set u : ℂ := 1 + ω
  set M : ℝ := (2 + Real.sqrt 3) * R
  set v : ℂ := (z - sideCenter 0) * starRingEnd ℂ u
  set x : ℝ := v.re
  set y : ℝ := v.im
  have hu_norm : ‖u‖ = 1 := norm_one_add_ω
  have hu_mul : u * starRingEnd ℂ u = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, hu_norm]; norm_num
  have ha0_eq : sideCenter 0 = (M : ℂ) * u := by simp [sideCenter, a0, M, u]
  have hv_sq : x ^ 2 + y ^ 2 = M ^ 2 - 1 := by
    have h1 : ‖v‖ ^ 2 = ‖sideCenter 0‖ ^ 2 - 1 := by
      simp only [v, norm_mul, RCLike.norm_conj, hu_norm, mul_one]; exact hcirc
    rw [Complex.sq_norm, Complex.normSq_apply, norm_sideCenter] at h1
    simpa only [x, y, M, sq] using h1
  have hz_eq : z = ((M + x : ℝ) : ℂ) * u + ((y : ℝ) : ℂ) * (I * u) := by
    have hv_eq : v = (x : ℂ) + (y : ℂ) * I := (Complex.re_add_im v).symm
    have hz1' : z - sideCenter 0 = v * u := by
      calc z - sideCenter 0 = (z - sideCenter 0) * (u * starRingEnd ℂ u) := by rw [hu_mul, mul_one]
        _ = v * u := by simp only [v]; ring
    rw [ha0_eq] at hz1'
    rw [show z = (M : ℂ) * u + v * u by linear_combination hz1', hv_eq]
    push_cast; ring
  have hM_gt1 : 1 < M := by
    have := one_lt_norm_sideCenter 0; rwa [norm_sideCenter] at this
  have hx_neg : x < 0 := by
    have hre_z : (z * starRingEnd ℂ u).re = M + x := by
      rw [hz_eq]
      have h1 : (((M + x : ℝ) : ℂ) * u + (y : ℂ) * (I * u)) * starRingEnd ℂ u =
          ((M + x : ℝ) : ℂ) + (y : ℂ) * I := by
        linear_combination (((M + x : ℝ) : ℂ) + (y : ℂ) * I) * hu_mul
      rw [h1]; simp
    have hle : (z * starRingEnd ℂ u).re ≤ ‖z * starRingEnd ℂ u‖ := Complex.re_le_norm _
    rw [norm_mul, RCLike.norm_conj, hu_norm, mul_one, hre_z] at hle
    linarith
  -- Key bound: `M + x ≤ R / 2`? Wait: check at `z = R`:
  -- `z * conj u = R * (1/2 - i√3/2)`, so `M + x = R / 2`, `y = -R √3 / 2`!
  -- Since `y^2 ≤ (R √3 / 2)^2 = 3 R^2 / 4`, we get `x^2 = M^2 - 1 - y^2 ≥ M^2 - 1 - 3 R^2 / 4`!
  -- Check `(M - R / 2)^2 = M^2 - M R + R^2 / 4`:
  -- Wait: `M R = (2 + √3) R^2 = 1 + R^2`!
  -- So `(M - R / 2)^2 = M^2 - (1 + R^2) + R^2 / 4 = M^2 - 1 - 3 R^2 / 4`!!
  -- THEREFORE `x^2 ≥ (M - R / 2)^2`, and since `x < 0` and `M - R / 2 > 0`, **`x ≤ -(M - R / 2)`**, i.e. **`M + x ≤ R / 2`**!!
  have hMR : M * R = 1 + R ^ 2 := by
    simp only [M]; linarith [R_sq_mul]
  have hMx_le : M + x ≤ R / 2 := by
    have hsq_ge : (M - R / 2) ^ 2 ≤ x ^ 2 := by
      have hy2 : y ^ 2 ≤ (R * Real.sqrt 3 / 2) ^ 2 := by nlinarith
      have h34 : (R * Real.sqrt 3 / 2) ^ 2 = 3 / 4 * R ^ 2 := by
        nlinarith [sq_sqrt3]
      nlinarith
    have hpos : 0 < M - R / 2 := by linarith [R_lt_one]
    nlinarith
  -- Also compute `‖z‖^2 = (M + x)^2 + y^2 = M^2 + 2 M x + (M^2 - 1) = 2 M (M + x) - 1`!
  have hnorm_z_sq : ‖z‖ ^ 2 = 2 * M * (M + x) - 1 := by
    have h1 : ‖z‖ ^ 2 = ‖z * starRingEnd ℂ u‖ ^ 2 := by
      rw [norm_mul, RCLike.norm_conj, hu_norm, mul_one]
    have h2 : z * starRingEnd ℂ u = ((M + x : ℝ) : ℂ) + (y : ℂ) * I := by
      rw [hz_eq]
      linear_combination (((M + x : ℝ) : ℂ) + (y : ℂ) * I) * hu_mul
    rw [h1, h2, Complex.sq_norm, Complex.normSq_apply]
    simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add]
    nlinarith [hv_sq]
  -- Now check sides 1 and 2 using `normSq_sub_sideCenter_iff`!
  refine ⟨hz1, fun j => ?_⟩
  fin_cases j
  · exact hcirc.ge
  · -- Side 1: `a1 = ω * M * u`, so `Re(z * conj a1) = M * Re(ω^2 * (z * conj u))`!
    rw [← sub_nonneg, normSq_sub_sideCenter_iff]
    have hre1 : (z * starRingEnd ℂ (sideCenter 1)).re =
        M * (-(1 / 2) * (M + x) + (Real.sqrt 3 / 2) * y) := by
      have ha1 : sideCenter 1 = (M : ℂ) * (ω * u) := by
        simp only [sideCenter, Fin.val_one, pow_one, a0, M, u]; ring
      have hmul : z * starRingEnd ℂ (sideCenter 1) =
          (M : ℂ) * (ω ^ 2 * (z * starRingEnd ℂ u)) := by
        rw [ha1, map_mul, map_mul, Complex.conj_ofReal, star_ω]; ring
      have hzu : z * starRingEnd ℂ u = ((M + x : ℝ) : ℂ) + (y : ℂ) * I := by
        rw [hz_eq]
        linear_combination (((M + x : ℝ) : ℂ) + (y : ℂ) * I) * hu_mul
      rw [hmul, hzu, Complex.re_ofReal_mul, ω_sq]
      simp only [mul_re, add_re, add_im, ofReal_re, ofReal_im, mul_im, I_re, I_im, mul_zero,
        mul_one, sub_zero, add_zero, zero_add]
      ring
    change 0 ≤ ‖z‖ ^ 2 - 2 * (z * starRingEnd ℂ (sideCenter 1)).re + 1
    rw [hnorm_z_sq, hre1]
    -- Need: `2 M (M + x) - 1 - 2 M (-(1/2)(M+x) + (√3/2) y) + 1 ≥ 0`, i.e., `3 (M + x) ≥ √3 y`!
    -- Wait: check sign! At `z = R * ω`, `y = +R √3 / 2` and `M + x = R / 2` -> `3 (R/2) = 3R/2 = √3 * (R √3 / 2)` (EQUALITY!!)!
    -- Wait: `M + x` is LOWER-bounded? No, we need `M + x ≥ y / √3`!
    -- CHECK: `2 M (M + x) - 1 ≥ 0`? Wait: `‖z‖^2 = 2 M (M + x) - 1` -> at `z = R`, `2 M (R/2) - 1 = M R - 1 = R^2`!
    -- And `M + x = M - √(M^2 - 1 - y^2)` is INCREASING with `y^2`!!
    -- Since `y^2 ≥ 0`, wait: at `y = 0`, `M + x = M - √(M^2 - 1) > 0`!
    -- We need `3 (M + x) ≥ √3 * y`, i.e. `√3 * (M + x) ≥ y`!
    -- Check `y ≤ R √3 / 2` and `M + x`: at `y = R √3 / 2`, `M + x = R / 2`, so `√3 (M + x) = R √3 / 2 = y`!
    -- Is `√3 (M + x) ≥ y` for ALL `y ∈ [-R √3 / 2, R √3 / 2]`?!
    -- YES!! Check: `x = -√(M^2 - 1 - y^2)`, we want `√3 M - y ≥ √3 √(M^2 - 1 - y^2)`.
    -- Square both sides (since `√3 M > √3 > R √3 / 2 ≥ y`):
    -- `3 M^2 - 2 √3 M y + y^2 ≥ 3 M^2 - 3 - 3 y^2 ⟺ 4 y^2 - 2 √3 M y + 3 ≥ 0`!!
    -- Factor: check at `y = R √3 / 2`: `4 (3 R^2 / 4) - 2 √3 M (R √3 / 2) + 3 = 3 R^2 - 3 M R + 3 = 3 R^2 - 3(1 + R^2) + 3 = 0`!!
    -- Divide by `1`: `4 y^2 - 2 √3 M y + 3 = (R √3 / 2 - y) * (...)`!
    -- Let `t = R √3 / 2 - y ≥ 0`:
    -- At `y = R √3 / 2`, derivative wrt `y` is `8 y - 2 √3 M = 4 √3 R - 2 √3 (2 + √3) R = -6 R < 0`!
    -- So for `y ≤ R √3 / 2`, `4 y^2 - 2 √3 M y + 3 ≥ 0` ALWAYS!!
    have hM_pos : 0 < M := by linarith
    have hquad : 0 ≤ 4 * y ^ 2 - 2 * Real.sqrt 3 * M * y + 3 := by
      have hroot : 4 * (R * Real.sqrt 3 / 2) ^ 2 - 2 * Real.sqrt 3 * M * (R * Real.sqrt 3 / 2) + 3 = 0 := by
        linear_combination R ^ 2 * sq_sqrt3 - M * R * sq_sqrt3 - 3 * hMR
      have hfact : 4 * y ^ 2 - 2 * Real.sqrt 3 * M * y + 3 =
          (R * Real.sqrt 3 / 2 - y) * (2 * Real.sqrt 3 * M - 4 * (R * Real.sqrt 3 / 2 + y)) := by
        linear_combination hroot
      rw [hfact]
      have hterm2 : 0 ≤ 2 * Real.sqrt 3 * M - 4 * (R * Real.sqrt 3 / 2 + y) := by
        have hM_val : 2 * Real.sqrt 3 * M = 4 * Real.sqrt 3 * R + 6 * R := by
          simp only [M]; linear_combination 2 * R * sq_sqrt3
        linarith [hM_val, hy_hi, R_pos]
      exact mul_nonneg (by linarith [hy_hi]) hterm2
    have hsqrt_ineq : y ≤ Real.sqrt 3 * (M + x) := by
      have hpos : 0 ≤ Real.sqrt 3 * M - y := by
        have h1 : Real.sqrt 3 * 1 < Real.sqrt 3 * M := mul_lt_mul_of_pos_left hM_gt1 sqrt3_pos
        have h2 : R * Real.sqrt 3 / 2 < Real.sqrt 3 := by
          have := mul_lt_mul_of_pos_right R_lt_one sqrt3_pos
          linarith [sqrt3_pos]
        linarith [hy_hi]
      have hsq : 3 * x ^ 2 ≤ (Real.sqrt 3 * M - y) ^ 2 := by
        have hdiff : (Real.sqrt 3 * M - y) ^ 2 - 3 * x ^ 2 =
            4 * y ^ 2 - 2 * Real.sqrt 3 * M * y + 3 := by
          linear_combination -3 * hv_sq + M ^ 2 * sq_sqrt3
        linarith [hquad]
      have hneg : -(Real.sqrt 3 * x) ≤ Real.sqrt 3 * M - y := by
        have h3x : (-(Real.sqrt 3 * x)) ^ 2 = 3 * x ^ 2 := by linear_combination x ^ 2 * sq_sqrt3
        have hnn : 0 ≤ -(Real.sqrt 3 * x) := by
          have := mul_nonneg sqrt3_pos.le (neg_nonneg.mpr hx_neg.le); linarith
        nlinarith only [hsq, h3x, hpos, hnn]
      linarith
    have h3 : Real.sqrt 3 * y ≤ 3 * (M + x) := by
      have hmul := mul_le_mul_of_nonneg_left hsqrt_ineq sqrt3_pos.le
      have heq : Real.sqrt 3 * (Real.sqrt 3 * (M + x)) = 3 * (M + x) := by
        linear_combination (M + x) * sq_sqrt3
      linarith
    have hgoal : 2 * M * (M + x) - 1 - 2 * (M * (-(1 / 2) * (M + x) + Real.sqrt 3 / 2 * y)) + 1 =
        M * (3 * (M + x) - Real.sqrt 3 * y) := by ring
    rw [hgoal]
    exact mul_nonneg hM_pos.le (by linarith [h3])
  · -- Side 2: symmetric with `y` replaced by `-y`!
    rw [← sub_nonneg, normSq_sub_sideCenter_iff]
    have hre2 : (z * starRingEnd ℂ (sideCenter 2)).re =
        M * (-(1 / 2) * (M + x) - (Real.sqrt 3 / 2) * y) := by
      have ha2 : sideCenter 2 = (M : ℂ) * (ω ^ 2 * u) := by
        simp only [sideCenter, Fin.val_two, a0, M, u]; ring
      have hmul : z * starRingEnd ℂ (sideCenter 2) =
          (M : ℂ) * (ω * (z * starRingEnd ℂ u)) := by
        rw [ha2, map_mul, map_mul, Complex.conj_ofReal, star_ω_sq]; ring
      have hzu : z * starRingEnd ℂ u = ((M + x : ℝ) : ℂ) + (y : ℂ) * I := by
        rw [hz_eq]
        linear_combination (((M + x : ℝ) : ℂ) + (y : ℂ) * I) * hu_mul
      rw [hmul, hzu, Complex.re_ofReal_mul]
      simp only [mul_re, add_re, add_im, ofReal_re, ofReal_im, mul_im, I_re, I_im, ω_re, ω_im,
        mul_zero, mul_one, sub_zero, add_zero, zero_add]
      ring
    change 0 ≤ ‖z‖ ^ 2 - 2 * (z * starRingEnd ℂ (sideCenter 2)).re + 1
    rw [hnorm_z_sq, hre2]
    have hM_pos : 0 < M := by linarith
    have hquad : 0 ≤ 4 * (-y) ^ 2 - 2 * Real.sqrt 3 * M * (-y) + 3 := by
      have hroot : 4 * (R * Real.sqrt 3 / 2) ^ 2 - 2 * Real.sqrt 3 * M * (R * Real.sqrt 3 / 2) + 3 = 0 := by
        linear_combination R ^ 2 * sq_sqrt3 - M * R * sq_sqrt3 - 3 * hMR
      have hfact : 4 * (-y) ^ 2 - 2 * Real.sqrt 3 * M * (-y) + 3 =
          (R * Real.sqrt 3 / 2 - (-y)) * (2 * Real.sqrt 3 * M - 4 * (R * Real.sqrt 3 / 2 + (-y))) := by
        linear_combination hroot
      rw [hfact]
      have hterm2 : 0 ≤ 2 * Real.sqrt 3 * M - 4 * (R * Real.sqrt 3 / 2 + (-y)) := by
        have hM_val : 2 * Real.sqrt 3 * M = 4 * Real.sqrt 3 * R + 6 * R := by
          simp only [M]; linear_combination 2 * R * sq_sqrt3
        linarith [hM_val, hy_lo, R_pos]
      exact mul_nonneg (by linarith [hy_lo]) hterm2
    have hsqrt_ineq : -y ≤ Real.sqrt 3 * (M + x) := by
      have hpos : 0 ≤ Real.sqrt 3 * M - (-y) := by
        have h1 : Real.sqrt 3 * 1 < Real.sqrt 3 * M := mul_lt_mul_of_pos_left hM_gt1 sqrt3_pos
        have h2 : R * Real.sqrt 3 / 2 < Real.sqrt 3 := by
          have := mul_lt_mul_of_pos_right R_lt_one sqrt3_pos
          linarith [sqrt3_pos]
        linarith [hy_lo]
      have hsq : 3 * x ^ 2 ≤ (Real.sqrt 3 * M - (-y)) ^ 2 := by
        have hdiff : (Real.sqrt 3 * M - (-y)) ^ 2 - 3 * x ^ 2 =
            4 * (-y) ^ 2 - 2 * Real.sqrt 3 * M * (-y) + 3 := by
          linear_combination -3 * hv_sq + M ^ 2 * sq_sqrt3
        linarith [hquad]
      have hneg : -(Real.sqrt 3 * x) ≤ Real.sqrt 3 * M - (-y) := by
        have h3x : (-(Real.sqrt 3 * x)) ^ 2 = 3 * x ^ 2 := by linear_combination x ^ 2 * sq_sqrt3
        have hnn : 0 ≤ -(Real.sqrt 3 * x) := by
          have := mul_nonneg sqrt3_pos.le (neg_nonneg.mpr hx_neg.le); linarith
        nlinarith only [hsq, h3x, hpos, hnn]
      linarith
    have h3 : Real.sqrt 3 * (-y) ≤ 3 * (M + x) := by
      have hmul := mul_le_mul_of_nonneg_left hsqrt_ineq sqrt3_pos.le
      have heq : Real.sqrt 3 * (Real.sqrt 3 * (M + x)) = 3 * (M + x) := by
        linear_combination (M + x) * sq_sqrt3
      linarith
    have hgoal : 2 * M * (M + x) - 1 - 2 * (M * (-(1 / 2) * (M + x) - Real.sqrt 3 / 2 * y)) + 1 =
        M * (3 * (M + x) - Real.sqrt 3 * (-y)) := by ring
    rw [hgoal]
    exact mul_nonneg hM_pos.le (by linarith [h3])

lemma u6_arc_mem_frontier {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 2 * Real.pi / 3) :
    u6 (Complex.exp ((θ : ℂ) * I)) ∈ frontier Δ1Open := by
  rw [frontier_Δ1Open]
  rcases eq_or_lt_of_le h0 with rfl | h0'
  · simp only [ofReal_zero, zero_mul, Complex.exp_zero, u6_one]
    refine ⟨by simpa [vert1] using vert1_mem_Δ1 0, fun h => ?_⟩
    have := h.2 0
    have h0 := vert1_zero_on_side0
    simp only [vert1, Fin.val_zero, pow_zero, one_mul] at h0
    linarith
  rcases eq_or_lt_of_le h1 with rfl | h1'
  · rw [← ω_eq_exp, show ω = ω * 1 by ring, u6_rot, u6_one]
    refine ⟨by simpa [vert1] using vert1_mem_Δ1 1, fun h => ?_⟩
    have hrot := Δ1Open_rot_mem (Δ1Open_rot_mem h)
    have hmul : ω * (ω * (ω * (R : ℂ))) = (R : ℂ) := by linear_combination (R : ℂ) * ω_cube
    rw [hmul] at hrot
    have := hrot.2 0
    have h0 := vert1_zero_on_side0
    simp only [vert1, Fin.val_zero, pow_zero, one_mul] at h0
    linarith
  -- Interior point `0 < θ < 2π/3`!
  set y : ℝ → ℝ := fun t => ((u6 (Complex.exp ((t : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω)).im
  have hy_cont : ContinuousOn y (Icc 0 (2 * Real.pi / 3)) := by
    have hmaps : MapsTo (fun t : ℝ => Complex.exp ((t : ℂ) * I)) (Icc 0 (2 * Real.pi / 3)) (closedBall 0 1) :=
      fun t _ => by simp [Metric.mem_closedBall, dist_zero_right]
    have hu_cont : ContinuousOn (fun t : ℝ => u6 (Complex.exp ((t : ℂ) * I))) (Icc 0 (2 * Real.pi / 3)) :=
      u6_continuousOn_closedBall.comp (by fun_prop) hmaps
    exact Complex.continuous_im.comp_continuousOn ((hu_cont.sub continuousOn_const).mul continuousOn_const)
  have hy_deriv_ne : ∀ t ∈ Ioo 0 (2 * Real.pi / 3), deriv y t ≠ 0 := by
    intro t ht
    have hmem := exp_I_mem_Ω0 ht.1 ht.2
    have hnorm1 : ‖Complex.exp ((t : ℂ) * I)‖ ≤ 1 := by simp
    have hu_d := u6_hasDerivAt_of_I0_ne_zero (Ω0_subset_Ω hmem) (I0_ne_zero_of_norm_le_one hnorm1)
    have hexp_d : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * I)) (I * Complex.exp ((t : ℂ) * I)) t := by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * I) I t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I
      simpa only [Function.comp_def, smul_eq_mul] using (Complex.hasDerivAt_exp ((t : ℂ) * I)).scomp t h1
    have hcomp_d : HasDerivAt (fun s : ℝ => u6 (Complex.exp ((s : ℂ) * I)))
        (I * Complex.exp ((t : ℂ) * I) * deriv u6 (Complex.exp ((t : ℂ) * I))) t := by
      rw [← hu_d.deriv] at hu_d
      simpa only [Function.comp_def, smul_eq_mul] using hu_d.scomp t hexp_d
    have hv_d : HasDerivAt (fun s : ℝ => (u6 (Complex.exp ((s : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω))
        ((I * Complex.exp ((t : ℂ) * I) * deriv u6 (Complex.exp ((t : ℂ) * I))) * starRingEnd ℂ (1 + ω)) t :=
      (hcomp_d.sub_const (sideCenter 0)).mul_const (starRingEnd ℂ (1 + ω))
    have hre_d : HasDerivAt (fun s : ℝ => ((u6 (Complex.exp ((s : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω)).re)
        (((I * Complex.exp ((t : ℂ) * I) * deriv u6 (Complex.exp ((t : ℂ) * I))) * starRingEnd ℂ (1 + ω)).re) t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hv_d
    have him_d : HasDerivAt y
        (((I * Complex.exp ((t : ℂ) * I) * deriv u6 (Complex.exp ((t : ℂ) * I))) * starRingEnd ℂ (1 + ω)).im) t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hv_d
    -- Differentiate `x(s)^2 + y(s)^2 = const` at `s = t`!
    have hsq_eq : (fun s : ℝ =>
        ((u6 (Complex.exp ((s : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω)).re ^ 2 + y s ^ 2) =ᶠ[𝓝 t]
        fun _ => ‖sideCenter 0‖ ^ 2 - 1 := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      have hc := u6_arc_on_circle hs.1 hs.2
      have h1 : ‖(u6 (Complex.exp ((s : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω)‖ ^ 2 =
          ‖sideCenter 0‖ ^ 2 - 1 := by
        rw [norm_mul, RCLike.norm_conj, norm_one_add_ω, mul_one]; exact hc
      rw [Complex.sq_norm, Complex.normSq_apply] at h1
      simpa only [y, sq] using h1
    have hsq_d := ((hre_d.pow 2).add (him_d.pow 2)).unique
      ((hasDerivAt_const t (‖sideCenter 0‖ ^ 2 - 1)).congr_of_eventuallyEq hsq_eq)
    intro hy0
    rw [him_d.deriv] at hy0
    have hx_neg : ((u6 (Complex.exp ((t : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω)).re < 0 := by
      have h1 : ((u6 (Complex.exp ((t : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω)).re =
          (u6 (Complex.exp ((t : ℂ) * I)) * starRingEnd ℂ (1 + ω)).re - (2 + Real.sqrt 3) * R := by
        rw [sub_mul, sub_re]
        congr 1
        simp only [sideCenter, Fin.val_zero, pow_zero, one_mul, a0, mul_assoc]
        have hu1 : (1 + ω) * starRingEnd ℂ (1 + ω) = 1 := by
          rw [Complex.mul_conj, ← Complex.sq_norm, norm_one_add_ω]; norm_num
        rw [hu1, mul_one, ofReal_re]
      rw [h1]
      have hle : (u6 (Complex.exp ((t : ℂ) * I)) * starRingEnd ℂ (1 + ω)).re ≤
          ‖u6 (Complex.exp ((t : ℂ) * I)) * starRingEnd ℂ (1 + ω)‖ := Complex.re_le_norm _
      rw [norm_mul, RCLike.norm_conj, norm_one_add_ω, mul_one] at hle
      have hlt1 := norm_u6_lt_one hnorm1
      have hM := one_lt_norm_sideCenter 0
      rw [norm_sideCenter] at hM
      linarith
    have hx_d0 : (((I * Complex.exp ((t : ℂ) * I) * deriv u6 (Complex.exp ((t : ℂ) * I))) *
        starRingEnd ℂ (1 + ω)).re) = 0 := by
      rw [hy0] at hsq_d
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_zero, add_zero] at hsq_d
      nlinarith only [hsq_d, hx_neg]
    have hv_d0 : (I * Complex.exp ((t : ℂ) * I) * deriv u6 (Complex.exp ((t : ℂ) * I))) *
        starRingEnd ℂ (1 + ω) = 0 := Complex.ext hx_d0 hy0
    have hstar_ne : starRingEnd ℂ (1 + ω) ≠ 0 := by
      intro h; have := congrArg norm h; rw [RCLike.norm_conj, norm_one_add_ω, norm_zero] at this
      norm_num at this
    have hprod0 := (mul_eq_zero.mp hv_d0).resolve_right hstar_ne
    have hu_ne := u6_deriv_ne_zero_of_I0_ne_zero (Ω0_subset_Ω hmem) (I0_ne_zero_of_norm_le_one hnorm1)
    exact hu_ne ((mul_eq_zero.mp hprod0).resolve_left (mul_ne_zero I_ne_zero (Complex.exp_ne_zero _)))
  -- Since `y` is continuous on `[0, 2π/3]` and `deriv y ≠ 0` on `(0, 2π/3)`, `y` is injective on `[0, 2π/3]`
  -- (by Rolle's theorem!), hence `y θ ∈ [min(y 0, y (2π/3)), max(y 0, y (2π/3))]`!
  have hy_inj : InjOn y (Icc 0 (2 * Real.pi / 3)) := by
    intro s hs t ht heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hlt (hy_cont.mono (Icc_subset_Icc hs.1 ht.2)) heq
      exact hy_deriv_ne c ⟨lt_of_le_of_lt hs.1 hc.1, lt_of_lt_of_le hc.2 ht.2⟩ hc0
    · obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hgt (hy_cont.mono (Icc_subset_Icc ht.1 hs.2)) heq.symm
      exact hy_deriv_ne c ⟨lt_of_le_of_lt ht.1 hc.1, lt_of_lt_of_le hc.2 hs.2⟩ hc0
  have hy0_val : y 0 = -(R * Real.sqrt 3 / 2) := by
    simp only [y, ofReal_zero, zero_mul, Complex.exp_zero, u6_one, sideCenter, Fin.val_zero,
      pow_zero, one_mul, a0, sub_mul, sub_im]
    have hu1 : (1 + ω) * starRingEnd ℂ (1 + ω) = 1 := by
      rw [Complex.mul_conj, ← Complex.sq_norm, norm_one_add_ω]; norm_num
    rw [mul_assoc, hu1, mul_one, ofReal_im, sub_zero, one_add_ω]
    simp only [mul_im, ofReal_re, ofReal_im, conj_re, conj_im, zero_mul, add_zero]
    ring
  have hy23_val : y (2 * Real.pi / 3) = R * Real.sqrt 3 / 2 := by
    have hu_ω : u6 (Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) = ω * (R : ℂ) := by
      rw [← ω_eq_exp]
      conv_lhs => rw [show ω = ω * 1 by ring]
      rw [u6_rot, u6_one]
    simp only [y, hu_ω, sideCenter, Fin.val_zero, pow_zero, one_mul, a0, sub_mul, sub_im]
    have hu1 : (1 + ω) * starRingEnd ℂ (1 + ω) = 1 := by
      rw [Complex.mul_conj, ← Complex.sq_norm, norm_one_add_ω]; norm_num
    have hterm : (((2 + Real.sqrt 3) * R : ℝ) : ℂ) * (1 + ω) * starRingEnd ℂ (1 + ω) =
        (((2 + Real.sqrt 3) * R : ℝ) : ℂ) := by
      rw [mul_assoc, hu1, mul_one]
    rw [hterm, ofReal_im, sub_zero, one_add_ω]
    simp only [mul_im, mul_re, ofReal_re, ofReal_im, conj_re, conj_im, ω_re, ω_im]
    ring
  have hy_bounds : -(R * Real.sqrt 3 / 2) ≤ y θ ∧ y θ ≤ R * Real.sqrt 3 / 2 := by
    constructor
    · by_contra hlt; push Not at hlt
      have hmem : y 0 ∈ Icc (y θ) (y (2 * Real.pi / 3)) := by
        rw [hy0_val, hy23_val]; exact ⟨hlt.le, by linarith [mul_pos R_pos sqrt3_pos]⟩
      obtain ⟨s, hs, hys⟩ := intermediate_value_Icc h1'.le
        (hy_cont.mono (Icc_subset_Icc h0'.le le_rfl)) hmem
      have h0_eq := hy_inj (left_mem_Icc.mpr (by positivity)) ⟨le_trans h0'.le hs.1, hs.2⟩ hys.symm
      linarith [hs.1]
    · by_contra hgt; push Not at hgt
      have hmem : y (2 * Real.pi / 3) ∈ Icc (y 0) (y θ) := by
        rw [hy0_val, hy23_val]; exact ⟨by linarith [mul_pos R_pos sqrt3_pos], hgt.le⟩
      obtain ⟨s, hs, hys⟩ := intermediate_value_Icc h0'.le
        (hy_cont.mono (Icc_subset_Icc le_rfl h1'.le)) hmem
      have h23_eq := hy_inj (right_mem_Icc.mpr (by positivity)) ⟨hs.1, le_trans hs.2 h1'.le⟩ hys.symm
      linarith [hs.2]
  have hcirc := u6_arc_on_circle h0' h1'
  refine ⟨circle_arc_mem_Δ1 (norm_u6_lt_one (by simp)) hcirc hy_bounds.1 hy_bounds.2, fun h => ?_⟩
  linarith [h.2 0]

lemma u6_maps_sphere_to_frontier : MapsTo u6 (sphere 0 1) (frontier Δ1Open) := by
  intro ζ hζ
  have hnorm : ‖ζ‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hζ
  have hne : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hnorm; norm_num at hnorm
  have hpolar : ζ = Complex.exp ((Complex.arg ζ : ℂ) * I) := by
    have := Complex.norm_mul_exp_arg_mul_I ζ
    rw [hnorm, ofReal_one, one_mul] at this
    exact this.symm
  -- Shift `arg ζ` into `[0, 2π/3]` by multiplying by `ω^k`!
  have harg_le := Complex.arg_le_pi ζ
  have harg_gt := Complex.neg_pi_lt_arg ζ
  have hrot_front : ∀ z ∈ frontier Δ1Open, ω * z ∈ frontier Δ1Open := by
    intro z hz
    rw [frontier_Δ1Open] at hz ⊢
    refine ⟨Δ1_rot_mem hz.1, fun h => hz.2 ?_⟩
    have h3 := Δ1Open_rot_mem (Δ1Open_rot_mem h)
    have hmul : ω * (ω * (ω * z)) = z := by linear_combination z * ω_cube
    rwa [hmul] at h3
  by_cases h1 : 0 ≤ Complex.arg ζ ∧ Complex.arg ζ ≤ 2 * Real.pi / 3
  · rw [hpolar]; exact u6_arc_mem_frontier h1.1 h1.2
  · by_cases h2 : 2 * Real.pi / 3 < Complex.arg ζ
    · have hζ_eq : ζ = ω * Complex.exp (((Complex.arg ζ - 2 * Real.pi / 3 : ℝ) : ℂ) * I) := by
        conv_lhs => rw [hpolar]
        rw [ω_eq_exp, ← Complex.exp_add]; congr 1; push_cast; ring
      rw [hζ_eq, u6_rot]
      exact hrot_front _ (u6_arc_mem_frontier (by linarith) (by linarith [Real.pi_pos]))
    · push Not at h1 h2
      have harg_neg : Complex.arg ζ < 0 := by
        by_contra hge; push Not at hge; exact (h1 hge).not_ge h2
      by_cases h3 : -(2 * Real.pi / 3) ≤ Complex.arg ζ
      · have hζ_eq : ζ = ω * (ω * Complex.exp (((Complex.arg ζ + 2 * Real.pi / 3 : ℝ) : ℂ) * I)) := by
          conv_lhs => rw [hpolar]
          rw [ω_eq_exp, ← Complex.exp_add, ← Complex.exp_add]
          have h2pi : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by
            simp [Complex.exp_two_pi_mul_I]
          calc Complex.exp ((Complex.arg ζ : ℂ) * I)
              = Complex.exp ((Complex.arg ζ : ℂ) * I) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) := by
                  rw [h2pi, mul_one]
            _ = Complex.exp _ := by rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [hζ_eq, u6_rot, u6_rot]
        exact hrot_front _ (hrot_front _ (u6_arc_mem_frontier (by linarith) (by linarith [Real.pi_pos])))
      · push Not at h3
        have hζ_eq : ζ = ω * Complex.exp (((Complex.arg ζ + 4 * Real.pi / 3 : ℝ) : ℂ) * I) := by
          conv_lhs => rw [hpolar]
          rw [ω_eq_exp, ← Complex.exp_add]
          have h2pi : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by
            simp [Complex.exp_two_pi_mul_I]
          calc Complex.exp ((Complex.arg ζ : ℂ) * I)
              = Complex.exp ((Complex.arg ζ : ℂ) * I) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) := by
                  rw [h2pi, mul_one]
            _ = Complex.exp _ := by rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [hζ_eq, u6_rot]
        exact hrot_front _ (u6_arc_mem_frontier (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))

/- ## 6. Derivative, Boundary Mapping, and Reflection Law for `u3` -/

lemma w3_hasDerivAt {ζ : ℂ} (hζ : ζ ∈ Ω) :
    HasDerivAt w3 ((1 - ζ ^ 3) ^ ((-(2 / 3) : ℝ) : ℂ)) ζ := by
  have hJ := hasDerivAt_euler_comp_cube (a := 2 / 3) (b := 1 / 3) (c := 4 / 3)
    (by norm_num) (by norm_num) hζ
  have hw_d : HasDerivAt w3
      ((1 / 3 : ℂ) * J3 ζ + (1 / 3 : ℂ) * ζ * (3 * ζ ^ 2 * deriv (eulerInt (2 / 3) (1 / 3) (4 / 3)) (ζ ^ 3))) ζ := by
    unfold w3 J3
    have h1 := ((hasDerivAt_id ζ).const_mul (1 / 3 : ℂ)).mul hJ
    refine h1.congr_deriv ?_; simp only [id_eq]; ring
  refine hw_d.congr_deriv ?_
  rw [eulerInt_deriv (a := 2 / 3) (b := 1 / 3) (c := 4 / 3) (by norm_num) (by norm_num) hζ]
  have hint0 := eulerIntegrand_integrable_of_slitSet (a := 2 / 3) (b := 1 / 3) (c := 4 / 3)
    (by norm_num) (by norm_num) hζ
  have hint1 := eulerIntegrand_integrable_of_slitSet (a := 2 / 3 + 1) (b := 1 / 3 + 1) (c := 4 / 3 + 1)
    (by norm_num) (by norm_num) hζ
  unfold J3 eulerInt
  set C1 : ℂ := (2 / 3 : ℂ) * ζ ^ 3
  have hcomb : (1 / 3 : ℂ) * (∫ t in (0 : ℝ)..1, eulerIntegrand (2 / 3) (1 / 3) (4 / 3) (ζ ^ 3) t) +
      (1 / 3 : ℂ) * ζ * (3 * ζ ^ 2 * (((2 / 3 : ℝ) : ℂ) *
        (∫ t in (0 : ℝ)..1, eulerIntegrand (2 / 3 + 1) (1 / 3 + 1) (4 / 3 + 1) (ζ ^ 3) t))) =
      ∫ t in (0 : ℝ)..1, ((1 / 3 : ℂ) * eulerIntegrand (2 / 3) (1 / 3) (4 / 3) (ζ ^ 3) t +
        C1 * eulerIntegrand (2 / 3 + 1) (1 / 3 + 1) (4 / 3 + 1) (ζ ^ 3) t) := by
    rw [intervalIntegral.integral_add (hint0.const_mul (1 / 3 : ℂ)) (hint1.const_mul C1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    simp only [C1]; push_cast; ring
  rw [hcomb]
  -- Exact antiderivative: `G(t) = t^(1/3) * (1 - ζ^3 * t)^(-2/3)`!
  let G : ℝ → ℂ := fun t => (t : ℂ) ^ ((1 / 3 : ℝ) : ℂ) * (1 - ζ ^ 3 * (t : ℂ)) ^ ((-(2 / 3) : ℝ) : ℂ)
  have hG_deriv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt G ((1 / 3 : ℂ) * eulerIntegrand (2 / 3) (1 / 3) (4 / 3) (ζ ^ 3) t +
        C1 * eulerIntegrand (2 / 3 + 1) (1 / 3 + 1) (4 / 3 + 1) (ζ ^ 3) t) t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have hslit_t : (t : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr ht.1
    have hslit_ξt : 1 - ζ ^ 3 * (t : ℂ) ∈ Complex.slitPlane :=
      one_sub_mul_mem_slitPlane hζ ht.1.le ht.2.le
    have hξt0 : 1 - ζ ^ 3 * (t : ℂ) ≠ 0 := Complex.slitPlane_ne_zero hslit_ξt
    have hd1 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ ((1 / 3 : ℝ) : ℂ))
        (((1 / 3 : ℝ) : ℂ) * (t : ℂ) ^ (((1 / 3 : ℝ) : ℂ) - 1)) t := by
      simpa using (Complex.hasStrictDerivAt_cpow_const (c := ((1 / 3 : ℝ) : ℂ)) hslit_t).hasDerivAt.comp_ofReal
    have hd2 : HasDerivAt (fun x : ℝ => (1 - ζ ^ 3 * (x : ℂ)) ^ ((-(2 / 3) : ℝ) : ℂ))
        (((-(2 / 3) : ℝ) : ℂ) * (1 - ζ ^ 3 * (t : ℂ)) ^ (((-(2 / 3) : ℝ) : ℂ) - 1) * (-(ζ ^ 3))) t := by
      have hinner : HasDerivAt (fun x : ℝ => (1 : ℂ) - ζ ^ 3 * (x : ℂ)) (-(ζ ^ 3)) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (ζ ^ 3)).const_sub 1
      have hc := (Complex.hasStrictDerivAt_cpow_const (c := ((-(2 / 3) : ℝ) : ℂ)) hslit_ξt).hasDerivAt
      simpa only [Function.comp_def, smul_eq_mul, mul_comm] using hc.scomp t hinner
    refine (hd1.mul hd2).congr_deriv ?_
    have he1 : ((1 / 3 : ℝ) : ℂ) - 1 = ((1 / 3 - 1 : ℝ) : ℂ) := by norm_num
    have he2 : ((-(2 / 3) : ℝ) : ℂ) - 1 = ((-(2 / 3 + 1) : ℝ) : ℂ) := by norm_num
    have he3 : ((4 / 3 - 1 / 3 - 1 : ℝ) : ℂ) = 0 := by norm_num
    have he4 : ((4 / 3 + 1 - (1 / 3 + 1) - 1 : ℝ) : ℂ) = 0 := by norm_num
    have he5 : ((1 / 3 + 1 - 1 : ℝ) : ℂ) = ((1 / 3 : ℝ) : ℂ) := by norm_num
    simp only [eulerIntegrand, C1, he1, he2, he3, he4, he5, Complex.cpow_zero, mul_one]
    push_cast; ring
  have hG0 : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (t : ℂ) ^ ((1 / 3 : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun z : ℂ => z ^ ((1 / 3 : ℝ) : ℂ)) 0 :=
        Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by norm_num)
      have h0 : ((0 : ℂ) ^ ((1 / 3 : ℝ) : ℂ)) = 0 := Complex.zero_cpow (by norm_num)
      have hinner : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
        simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
      rw [← h0]
      exact (hc.tendsto.comp hinner).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t : ℝ => (1 - ζ ^ 3 * (t : ℂ)) ^ ((-(2 / 3) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hc : ContinuousAt (fun t : ℝ => (1 - ζ ^ 3 * (t : ℂ)) ^ ((-(2 / 3) : ℝ) : ℂ)) 0 :=
        continuousAt_cpow_const_comp (by fun_prop) (by simp : (1 - ζ ^ 3 * ((0 : ℝ) : ℂ)) ∈ Complex.slitPlane)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa [G] using h1.mul h2
  have hG1 : Tendsto G (𝓝[<] (1 : ℝ)) (𝓝 ((1 - ζ ^ 3) ^ ((-(2 / 3) : ℝ) : ℂ))) := by
    have h1 : Tendsto (fun t : ℝ => (t : ℂ) ^ ((1 / 3 : ℝ) : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
      have hc : ContinuousAt (fun t : ℝ => (t : ℂ) ^ ((1 / 3 : ℝ) : ℂ)) 1 :=
        continuousAt_cpow_const_comp (by fun_prop) (by simp : ((1 : ℝ) : ℂ) ∈ Complex.slitPlane)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t : ℝ => (1 - ζ ^ 3 * (t : ℂ)) ^ ((-(2 / 3) : ℝ) : ℂ))
        (𝓝[<] (1 : ℝ)) (𝓝 ((1 - ζ ^ 3) ^ ((-(2 / 3) : ℝ) : ℂ))) := by
      have hslit1 : 1 - ζ ^ 3 * ((1 : ℝ) : ℂ) ∈ Complex.slitPlane :=
        one_sub_mul_mem_slitPlane hζ zero_le_one le_rfl
      have hc : ContinuousAt (fun t : ℝ => (1 - ζ ^ 3 * (t : ℂ)) ^ ((-(2 / 3) : ℝ) : ℂ)) 1 :=
        continuousAt_cpow_const_comp (by fun_prop) hslit1
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa [G] using h1.mul h2
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    hG_deriv ((hint0.const_mul (1 / 3 : ℂ)).add (hint1.const_mul C1)) hG0 hG1
  simpa using hftc

lemma u3_hasDerivAt {ζ : ℂ} (hζ : ζ ∈ Ω) :
    HasDerivAt u3 (((R / w6_1 : ℝ) : ℂ) * (1 - ζ ^ 3) ^ ((-(2 / 3) : ℝ) : ℂ)) ζ :=
  (w3_hasDerivAt hζ).const_mul _

lemma u3_differentiableOn_Ω : DifferentiableOn ℂ u3 Ω := fun _ hζ =>
  (u3_hasDerivAt hζ).differentiableAt.differentiableWithinAt

lemma u3_deriv_ne_zero {ζ : ℂ} (hζ : ζ ∈ Ω) : deriv u3 ζ ≠ 0 := by
  rw [(u3_hasDerivAt hζ).deriv]
  refine mul_ne_zero (Complex.ofReal_ne_zero.mpr (div_ne_zero R_ne_zero w6_1_pos.ne')) ?_
  rw [Complex.cpow_def_of_ne_zero (one_sub_cube_ne_zero hζ)]
  exact Complex.exp_ne_zero _

lemma u3_arc_deriv {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * Real.pi / 3) :
    HasDerivAt (fun t : ℝ => ω * u3 (Complex.exp ((t : ℂ) * I)))
      (-((R / w6_1 * (2 * Real.sin (3 * θ / 2)) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * I) θ := by
  have hmem := exp_I_mem_Ω0 h0 h1
  have hu_d := u3_hasDerivAt (Ω0_subset_Ω hmem)
  have hexp_d : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * I)) (I * Complex.exp ((θ : ℂ) * I)) θ := by
    have h1' : HasDerivAt (fun s : ℝ => (s : ℂ) * I) I θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const I
    simpa only [Function.comp_def, smul_eq_mul] using (Complex.hasDerivAt_exp ((θ : ℂ) * I)).scomp θ h1'
  have hcomp := (hu_d.scomp θ hexp_d).const_mul ω
  refine hcomp.congr_deriv ?_
  have hsin : 0 < 2 * Real.sin (3 * θ / 2) := by
    have := Real.sin_pos_of_pos_of_lt_pi (x := 3 * θ / 2) (by linarith) (by linarith); linarith
  have hfac : 1 - Complex.exp ((θ : ℂ) * I) ^ 3 =
      ((2 * Real.sin (3 * θ / 2) : ℝ) : ℂ) *
        Complex.exp ((((3 * θ / 2 - Real.pi / 2 : ℝ) : ℂ)) * I) := by
    rw [← Complex.exp_nat_mul]
    rw [show (3 : ℕ) * ((θ : ℂ) * I) = ((3 * θ : ℝ) : ℂ) * I by push_cast; ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    apply Complex.ext
    · simp only [sub_re, one_re, add_re, Complex.cos_ofReal_re, mul_re, Complex.sin_ofReal_re,
        Complex.sin_ofReal_im, I_re, I_im, ofReal_re, ofReal_im, mul_zero, mul_one,
        add_zero, sub_self]
      rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, zero_add, mul_one]
      have hdouble := Real.cos_two_mul (3 * θ / 2)
      rw [show 2 * (3 * θ / 2) = 3 * θ by ring] at hdouble
      have hsq := Real.sin_sq_add_cos_sq (3 * θ / 2)
      nlinarith
    · simp only [sub_im, one_im, add_im, Complex.cos_ofReal_im, mul_im, Complex.sin_ofReal_re,
        Complex.sin_ofReal_im, I_re, I_im, ofReal_re, ofReal_im, mul_zero, mul_one, zero_add,
        add_zero, zero_sub]
      rw [Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, zero_sub, mul_one]
      have hdouble := Real.sin_two_mul (3 * θ / 2)
      rw [show 2 * (3 * θ / 2) = 3 * θ by ring] at hdouble
      nlinarith
  have harg_eq : Complex.arg (1 - Complex.exp ((θ : ℂ) * I) ^ 3) = 3 * θ / 2 - Real.pi / 2 := by
    rw [hfac, Complex.arg_real_mul _ hsin, Complex.arg_exp_mul_I, toIocMod_eq_self]
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hne : 1 - Complex.exp ((θ : ℂ) * I) ^ 3 ≠ 0 := one_sub_cube_ne_zero (Ω0_subset_Ω hmem)
  have hnorm : ‖1 - Complex.exp ((θ : ℂ) * I) ^ 3‖ = 2 * Real.sin (3 * θ / 2) := by
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsin.le, Complex.norm_exp_ofReal_mul_I,
      mul_one]
  have hcpow : (1 - Complex.exp ((θ : ℂ) * I) ^ 3) ^ ((-(2 / 3) : ℝ) : ℂ) =
      (((2 * Real.sin (3 * θ / 2)) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (((-(θ) + Real.pi / 3 : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero hne, Complex.log, hnorm, harg_eq, add_mul, Complex.exp_add]
    congr 1
    · rw [Real.rpow_def_of_pos hsin, Complex.ofReal_exp]
      congr 1; push_cast; ring
    · congr 1; push_cast; ring
  have hphase : ω * (I * Complex.exp ((θ : ℂ) * I) *
      Complex.exp (((-(θ) + Real.pi / 3 : ℝ) : ℂ) * I)) = -I := by
    rw [ω_eq_exp]
    have h1 : Complex.exp ((2 * Real.pi / 3 : ℝ) * I) *
        (I * Complex.exp ((θ : ℂ) * I) * Complex.exp (((-(θ) + Real.pi / 3 : ℝ) : ℂ) * I)) =
        I * (Complex.exp ((2 * Real.pi / 3 : ℝ) * I) * Complex.exp ((θ : ℂ) * I) *
          Complex.exp (((-(θ) + Real.pi / 3 : ℝ) : ℂ) * I)) := by ring
    rw [h1, ← Complex.exp_add, ← Complex.exp_add]
    have hexp_pi : Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I + (θ : ℂ) * I +
        ((-(θ) + Real.pi / 3 : ℝ) : ℂ) * I) = -1 := by
      have harg : ((2 * Real.pi / 3 : ℝ) : ℂ) * I + (θ : ℂ) * I +
          ((-(θ) + Real.pi / 3 : ℝ) : ℂ) * I = (Real.pi : ℂ) * I := by push_cast; ring
      rw [harg, Complex.exp_pi_mul_I]
    rw [hexp_pi]; ring
  simp only [smul_eq_mul, hcpow, Complex.ofReal_mul]
  linear_combination ((R / w6_1 : ℝ) : ℂ) * (((2 * Real.sin (3 * θ / 2)) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * hphase

lemma u3_arc_re_eq {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 2 * Real.pi / 3) :
    (ω * u3 (Complex.exp ((θ : ℂ) * I))).re = -(cAG / 2) := by
  let g : ℝ → ℝ := fun t => (ω * u3 (Complex.exp ((t : ℂ) * I))).re
  have hg_cont : ContinuousOn g (Icc 0 (2 * Real.pi / 3)) := by
    have hmaps : MapsTo (fun t : ℝ => Complex.exp ((t : ℂ) * I)) (Icc 0 (2 * Real.pi / 3)) (closedBall 0 1) :=
      fun t _ => by simp [Metric.mem_closedBall, dist_zero_right]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_const.mul (u3_continuousOn_closedBall.comp (by fun_prop) hmaps))
  have hg_deriv : ∀ t ∈ Ioo 0 (2 * Real.pi / 3), deriv g t = 0 := by
    intro t ht
    have hd : HasDerivAt g
        ((-((R / w6_1 * (2 * Real.sin (3 * t / 2)) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * I).re) t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (u3_arc_deriv ht.1 ht.2)
    rw [hd.deriv]; simp
  have hconst : g θ = g 0 := by
    rcases eq_or_lt_of_le h0 with rfl | h0'
    · rfl
    · obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope g h0'
        (hg_cont.mono (Icc_subset_Icc le_rfl h1))
        (fun t ht => (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
          (u3_arc_deriv ht.1 (lt_of_lt_of_le ht.2 h1))).differentiableAt.differentiableWithinAt)
      have hc0 := hg_deriv c ⟨hc.1, lt_of_lt_of_le hc.2 h1⟩
      rw [hc0] at hslope
      have hne : θ - 0 ≠ 0 := by linarith
      have := (div_eq_zero_iff.mp hslope.symm).resolve_right hne
      linarith
  rw [show (ω * u3 (Complex.exp ((θ : ℂ) * I))).re = g θ from rfl, hconst]
  simp only [g, ofReal_zero, zero_mul, Complex.exp_zero, u3_one, mul_re, ω_re, ω_im, ofReal_re,
    ofReal_im, mul_zero, sub_zero]
  ring

lemma u3_arc_mem_frontier {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 2 * Real.pi / 3) :
    u3 (Complex.exp ((θ : ℂ) * I)) ∈ frontier Δ2Open := by
  have hre_eq := u3_arc_re_eq h0 h1
  let h : ℝ → ℝ := fun t => (ω * u3 (Complex.exp ((t : ℂ) * I))).im
  have hh_cont : ContinuousOn h (Icc 0 (2 * Real.pi / 3)) := by
    have hmaps : MapsTo (fun t : ℝ => Complex.exp ((t : ℂ) * I)) (Icc 0 (2 * Real.pi / 3)) (closedBall 0 1) :=
      fun t _ => by simp [Metric.mem_closedBall, dist_zero_right]
    exact Complex.continuous_im.comp_continuousOn
      (continuousOn_const.mul (u3_continuousOn_closedBall.comp (by fun_prop) hmaps))
  have hh_deriv_neg : ∀ t ∈ Ioo 0 (2 * Real.pi / 3), deriv h t < 0 := by
    intro t ht
    have hd : HasDerivAt h
        ((-((R / w6_1 * (2 * Real.sin (3 * t / 2)) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * I).im) t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (u3_arc_deriv ht.1 ht.2)
    rw [hd.deriv]
    simp only [neg_mul, neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero, add_zero]
    have hsin : 0 < 2 * Real.sin (3 * t / 2) := by
      have := Real.sin_pos_of_pos_of_lt_pi (x := 3 * t / 2) (by linarith [ht.1]) (by linarith [ht.2]); linarith
    have hpos : 0 < R / w6_1 * (2 * Real.sin (3 * t / 2)) ^ (-(2 / 3 : ℝ)) :=
      mul_pos (div_pos R_pos w6_1_pos) (Real.rpow_pos_of_pos hsin _)
    linarith
  have hh_anti : AntitoneOn h (Icc 0 (2 * Real.pi / 3)) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _) hh_cont
      (fun t ht => by
        rw [interior_Icc] at ht
        exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
          (u3_arc_deriv ht.1 ht.2)).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [interior_Icc] at ht; exact (hh_deriv_neg t ht).le)
  have hh0 : h 0 = cAG * Real.sqrt 3 / 2 := by
    simp only [h, ofReal_zero, zero_mul, Complex.exp_zero, u3_one, mul_im, ω_re, ω_im, ofReal_re,
      ofReal_im, mul_zero, zero_add]
    ring
  have hh23 : h (2 * Real.pi / 3) = -(cAG * Real.sqrt 3 / 2) := by
    have hu_ω : u3 (Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) = ω * (cAG : ℂ) := by
      rw [← ω_eq_exp]
      conv_lhs => rw [show ω = ω * 1 by ring]
      rw [u3_rot, u3_one]
    simp only [h, hu_ω]
    rw [← mul_assoc, ← pow_two, ω_sq]
    simp only [mul_im, ofReal_re, ofReal_im, mul_zero, zero_add]
    ring
  have him_lo : -(cAG * Real.sqrt 3 / 2) ≤ h θ := by
    rw [← hh23]; exact hh_anti ⟨h0, h1⟩ (right_mem_Icc.mpr (by positivity)) h1
  have him_hi : h θ ≤ cAG * Real.sqrt 3 / 2 := by
    rw [← hh0]; exact hh_anti (left_mem_Icc.mpr (by positivity)) ⟨h0, h1⟩ h0
  rw [frontier_Δ2Open]
  set w := u3 (Complex.exp ((θ : ℂ) * I))
  have hmem_Δ2 : w ∈ Δ2 := by
    intro j
    fin_cases j
    · have hw : ω ^ (0 : ℕ) * w = ω ^ 2 * (ω * w) := by
        simp only [pow_zero, one_mul]; linear_combination -w * ω_cube
      change -(cAG / 2) ≤ (ω ^ (0 : ℕ) * w).re
      rw [hw, ω_sq, mul_re, hre_eq]
      change -(cAG / 2) ≤ -1 / 2 * -(cAG / 2) - -(Real.sqrt 3 / 2) * h θ
      have hmul := mul_le_mul_of_nonneg_left him_lo sqrt3_pos.le
      have hmul' : -(3 * cAG / 2) ≤ Real.sqrt 3 * h θ := by
        have heq : Real.sqrt 3 * -(cAG * Real.sqrt 3 / 2) = -(3 * cAG / 2) := by
          linear_combination -(cAG / 2) * sq_sqrt3
        linarith
      linarith
    · change -(cAG / 2) ≤ (ω ^ (1 : ℕ) * w).re
      simp only [pow_one, hre_eq, le_refl]
    · have hw : ω ^ (2 : ℕ) * w = ω * (ω * w) := by ring
      change -(cAG / 2) ≤ (ω ^ (2 : ℕ) * w).re
      rw [hw, mul_re, ω_re, ω_im, hre_eq]
      change -(cAG / 2) ≤ -1 / 2 * -(cAG / 2) - Real.sqrt 3 / 2 * h θ
      have hmul := mul_le_mul_of_nonneg_left him_hi sqrt3_pos.le
      have hmul' : Real.sqrt 3 * h θ ≤ 3 * cAG / 2 := by
        have heq : Real.sqrt 3 * (cAG * Real.sqrt 3 / 2) = 3 * cAG / 2 := by
          linear_combination (cAG / 2) * sq_sqrt3
        linarith
      linarith
  refine ⟨hmem_Δ2, fun hopen => ?_⟩
  have h1' := hopen 1
  simp only [Fin.val_one, pow_one, hre_eq] at h1'
  linarith

lemma u3_maps_sphere_to_frontier : MapsTo u3 (sphere 0 1) (frontier Δ2Open) := by
  intro ζ hζ
  have hnorm : ‖ζ‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hζ
  have hne : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hnorm; norm_num at hnorm
  have hpolar : ζ = Complex.exp ((Complex.arg ζ : ℂ) * I) := by
    have := Complex.norm_mul_exp_arg_mul_I ζ
    rw [hnorm, ofReal_one, one_mul] at this
    exact this.symm
  have harg_le := Complex.arg_le_pi ζ
  have harg_gt := Complex.neg_pi_lt_arg ζ
  have hrot_front : ∀ w ∈ frontier Δ2Open, ω * w ∈ frontier Δ2Open := by
    intro w hw
    have hΔ2_rot : ∀ z ∈ Δ2, ω * z ∈ Δ2 := by
      intro z hz j
      fin_cases j
      · have h1 := hz 1; simpa only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul] using h1
      · have h2 := hz 2; simpa only [Fin.val_one, Fin.val_two, pow_one, ← mul_assoc, ← pow_two] using h2
      · have h0 := hz 0
        have : ω ^ (2 : ℕ) * (ω * z) = ω ^ (0 : ℕ) * z := by
          simp only [pow_zero, one_mul]; linear_combination z * ω_cube
        change -(cAG / 2) ≤ (ω ^ (2 : ℕ) * (ω * z)).re
        rw [this]; exact h0
    have hΔ2o_rot : ∀ z ∈ Δ2Open, ω * z ∈ Δ2Open := by
      intro z hz j
      fin_cases j
      · have h1 := hz 1; simpa only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul] using h1
      · have h2 := hz 2; simpa only [Fin.val_one, Fin.val_two, pow_one, ← mul_assoc, ← pow_two] using h2
      · have h0 := hz 0
        have : ω ^ (2 : ℕ) * (ω * z) = ω ^ (0 : ℕ) * z := by
          simp only [pow_zero, one_mul]; linear_combination z * ω_cube
        change -(cAG / 2) < (ω ^ (2 : ℕ) * (ω * z)).re
        rw [this]; exact h0
    rw [frontier_Δ2Open] at hw ⊢
    refine ⟨hΔ2_rot w hw.1, fun h => hw.2 ?_⟩
    have h3 := hΔ2o_rot _ (hΔ2o_rot _ h)
    have hmul : ω * (ω * (ω * w)) = w := by linear_combination w * ω_cube
    rwa [hmul] at h3
  by_cases h1 : 0 ≤ Complex.arg ζ ∧ Complex.arg ζ ≤ 2 * Real.pi / 3
  · rw [hpolar]; exact u3_arc_mem_frontier h1.1 h1.2
  · by_cases h2 : 2 * Real.pi / 3 < Complex.arg ζ
    · have hζ_eq : ζ = ω * Complex.exp (((Complex.arg ζ - 2 * Real.pi / 3 : ℝ) : ℂ) * I) := by
        conv_lhs => rw [hpolar]
        rw [ω_eq_exp, ← Complex.exp_add]; congr 1; push_cast; ring
      rw [hζ_eq, u3_rot]
      exact hrot_front _ (u3_arc_mem_frontier (by linarith) (by linarith [Real.pi_pos]))
    · push Not at h1 h2
      have harg_neg : Complex.arg ζ < 0 := by
        by_contra hge; push Not at hge; exact (h1 hge).not_ge h2
      by_cases h3 : -(2 * Real.pi / 3) ≤ Complex.arg ζ
      · have hζ_eq : ζ = ω * (ω * Complex.exp (((Complex.arg ζ + 2 * Real.pi / 3 : ℝ) : ℂ) * I)) := by
          conv_lhs => rw [hpolar]
          rw [ω_eq_exp, ← Complex.exp_add, ← Complex.exp_add]
          have h2pi : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by
            simp [Complex.exp_two_pi_mul_I]
          calc Complex.exp ((Complex.arg ζ : ℂ) * I)
              = Complex.exp ((Complex.arg ζ : ℂ) * I) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) := by
                  rw [h2pi, mul_one]
            _ = Complex.exp _ := by rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [hζ_eq, u3_rot, u3_rot]
        exact hrot_front _ (hrot_front _ (u3_arc_mem_frontier (by linarith) (by linarith [Real.pi_pos])))
      · push Not at h3
        have hζ_eq : ζ = ω * Complex.exp (((Complex.arg ζ + 4 * Real.pi / 3 : ℝ) : ℂ) * I) := by
          conv_lhs => rw [hpolar]
          rw [ω_eq_exp, ← Complex.exp_add]
          have h2pi : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by
            simp [Complex.exp_two_pi_mul_I]
          calc Complex.exp ((Complex.arg ζ : ℂ) * I)
              = Complex.exp ((Complex.arg ζ : ℂ) * I) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) := by
                  rw [h2pi, mul_one]
            _ = Complex.exp _ := by rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [hζ_eq, u3_rot]
        exact hrot_front _ (u3_arc_mem_frontier (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))

/-- Reflection law for `u3` on `Ω0` via Identity Theorem! -/
lemma u3_reflection_law {ζ : ℂ} (hζ : ζ ∈ Ω0) :
    u3 (1 / starRingEnd ℂ ζ) = eucRefl 0 (u3 ζ) := by
  let h : ℂ → ℂ := fun z => eucRefl 0 (u3 (1 / starRingEnd ℂ z))
  have hh_diff : DifferentiableOn ℂ h Ω0 := by
    intro z hz
    have hne : z ≠ 0 := Ω0_ne_zero hz
    have hz' : 1 / starRingEnd ℂ z ∈ Ω0 := Ω0_inv_conj hz
    have hd := hasDerivAt_inv_conj hne (u3_hasDerivAt (Ω0_subset_Ω hz'))
    have hfull := (hd.const_mul (-ω)).add_const ((cAG : ℂ) * (1 + ω))
    exact hfull.differentiableAt.differentiableWithinAt
  have hu3_an : AnalyticOnNhd ℂ u3 Ω0 :=
    (u3_differentiableOn_Ω.mono Ω0_subset_Ω).analyticOnNhd isOpen_Ω0
  have hh_an : AnalyticOnNhd ℂ h Ω0 := hh_diff.analyticOnNhd isOpen_Ω0
  have hζ₀ : Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I) ∈ Ω0 :=
    exp_I_mem_Ω0 (by positivity) (by linarith [Real.pi_pos])
  have hfreq : ∃ᶠ z in 𝓝[≠] (Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I)), h z = u3 z := by
    rw [frequently_nhdsWithin_iff, Metric.nhds_basis_ball.frequently_iff]
    intro ε hε
    set δ : ℝ := min (Real.pi / 6) (ε / 2)
    have hδ_pos : 0 < δ := lt_min (by positivity) (by linarith)
    set θ : ℝ := Real.pi / 3 + δ
    have hθ_eq : θ = Real.pi / 3 + δ := rfl
    have hθ0 : 0 < θ := by linarith [Real.pi_pos, hθ_eq]
    have hθ1 : θ < 2 * Real.pi / 3 := by
      have : δ ≤ Real.pi / 6 := min_le_left _ _; linarith [Real.pi_pos, hθ_eq]
    refine ⟨Complex.exp ((θ : ℂ) * I), ?_, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      -- `‖e^(i(π/3 + δ)) - e^(iπ/3)‖ = ‖e^(iδ) - 1‖ ≤ δ < ε`!
      have hsub : Complex.exp ((θ : ℂ) * I) - Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I) =
          Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * I) * (Complex.exp ((δ : ℂ) * I) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; simp only [θ]; push_cast; ring
      rw [hsub, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      have hle : ‖Complex.exp ((δ : ℂ) * I) - 1‖ ≤ δ := by
        have hsq : ‖Complex.exp ((δ : ℂ) * I) - 1‖ ^ 2 ≤ δ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply, Complex.exp_mul_I]
          simp only [sub_re, sub_im, add_re, add_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
            mul_re, mul_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im, I_re, I_im, one_re, one_im,
            mul_zero, mul_one, sub_zero, add_zero, zero_add]
          have hsc := Real.sin_sq_add_cos_sq δ
          have hcos2 : Real.cos δ = 1 - 2 * Real.sin (δ / 2) ^ 2 := by
            have := Real.cos_two_mul' (δ / 2)
            rw [show 2 * (δ / 2) = δ by ring] at this
            linarith [Real.sin_sq_add_cos_sq (δ / 2)]
          have hsin_le : Real.sin (δ / 2) ≤ δ / 2 := Real.sin_le (by linarith)
          have hsin_nn : 0 ≤ Real.sin (δ / 2) :=
            Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
              (by have : δ ≤ Real.pi / 6 := min_le_left _ _; linarith [Real.pi_pos])
          have hsq_sin : Real.sin (δ / 2) ^ 2 ≤ (δ / 2) ^ 2 := by nlinarith only [hsin_le, hsin_nn]
          nlinarith only [hsc, hcos2, hsq_sin]
        nlinarith only [hsq, norm_nonneg (Complex.exp ((δ : ℂ) * I) - 1), hδ_pos]
      have hδ_lt : δ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      linarith
    · have hinv : 1 / starRingEnd ℂ (Complex.exp ((θ : ℂ) * I)) = Complex.exp ((θ : ℂ) * I) := by
        rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, one_div,
          ← Complex.exp_neg, neg_neg]
      simp only [h, hinv, eucRefl]
      have hre := u3_arc_re_eq hθ0.le hθ1.le
      have hadd := Complex.add_conj (ω * u3 (Complex.exp ((θ : ℂ) * I)))
      rw [hre] at hadd
      simp only [map_mul, star_ω] at hadd
      push_cast at hadd
      linear_combination -(ω ^ 2 * hadd) +
        (u3 (Complex.exp ((θ : ℂ) * I)) + ω * starRingEnd ℂ (u3 (Complex.exp ((θ : ℂ) * I)))) * ω_cube +
        (cAG : ℂ) * ω_sq_add_ω_add_one
    · intro heq
      have harg := congrArg Complex.arg heq
      rw [Complex.arg_exp_mul_I, Complex.arg_exp_mul_I,
        (toIocMod_eq_self two_pi_pos).mpr ⟨by linarith [Real.pi_pos, hθ_eq], by linarith [Real.pi_pos, hθ_eq]⟩,
        (toIocMod_eq_self two_pi_pos).mpr ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩] at harg
      linarith [hθ_eq]
  have heq_on := hh_an.eqOn_of_preconnected_of_frequently_eq hu3_an isPreconnected_Ω0 hζ₀ hfreq
  have hres := heq_on hζ
  simp only [h] at hres
  have := congrArg (eucRefl 0) hres
  rwa [eucRefl_invol] at this

end

end BlochAG

/- ==================== Bloch_Part3.lean ==================== -/
/-
# Ahlfors-Grunsky Extremal Map — Part 3: Biholomorphism, Side & Vertex Extension

Proves:
1. Degree-1 covering biholomorphism lemma: `u6 : ball 0 1 → Δ1Open` and `u3 : ball 0 1 → Δ2Open`
   are biholomorphisms extending to homeomorphisms `closedBall 0 1 → Δ1` and `closedBall 0 1 → Δ2`.
2. Conformal triangle map `φ = u3 ∘ u6Inv : Δ1 → Δ2` with `φ 0 = 0`, `deriv φ 0 = 1`,
   `φ (vert1 k) = vert2 k`, and `φ z = vert2 k ↔ z = vert1 k` on `Δ1`.
3. Word actions `hypWord`, `eucWord`, and holomorphic chart conjugation `chartMap`.
4. Local holomorphic extension across open sides (via Inverse Function Theorem + reflection laws)
   and across the three vertices `vert1 k` (via 12-tile dihedral star + Riemann removable
   singularity), proving `deriv φ_ext (vert1 k) = 0`.
5. Global neighborhood `U = {z ∈ ball 0 1 | ∃ x ∈ Δ1, hypDist x z < ρ₀}` with holomorphic
   `φ_ext` satisfying the uniform continuation property on `hypBall y (ρ₀ / 2)`.
-/

open Complex Real Set Metric Filter Topology MeasureTheory

namespace BlochAG

noncomputable section

/- ## 1. General Degree-1 Covering Biholomorphism Lemma -/

lemma differentiableOn_hasStrictDerivAt {g : ℂ → ℂ} {S : Set ℂ} (hSo : IsOpen S)
    (hg : DifferentiableOn ℂ g S) {a : ℂ} (ha : a ∈ S) :
    HasStrictDerivAt g (deriv g a) a := by
  have han : AnalyticAt ℂ g a := hg.analyticAt (hSo.mem_nhds ha)
  have hcd : ContDiffAt ℂ 1 g a := han.contDiffAt
  have hsd := hcd.hasStrictDerivAt one_ne_zero
  rwa [hsd.hasDerivAt.deriv] at hsd

lemma isPreconnected_compl_of_starShaped_bounded {S : Set ℂ} (hS0 : (0 : ℂ) ∈ S)
    (hS_star : ∀ z ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (t : ℂ) * z ∈ S)
    (hS_bdd : Bornology.IsBounded S) :
    IsPreconnected Sᶜ := by
  obtain ⟨M, hM⟩ := hS_bdd.subset_closedBall (0 : ℂ)
  set R0 : ℝ := max M 0 + 1
  have hR0_pos : 0 < R0 := by positivity
  have houtside : ∀ w : ℂ, R0 ≤ ‖w‖ → w ∈ Sᶜ := by
    intro w hw hwS
    have hle : ‖w‖ ≤ M := by simpa [Metric.mem_closedBall, dist_zero_right] using hM hwS
    have : M < R0 := lt_of_le_of_lt (le_max_left M 0) (lt_add_one _)
    linarith
  have hbase : (R0 : ℂ) ∈ Sᶜ := houtside (R0 : ℂ) (by simp [Real.norm_of_nonneg hR0_pos.le])
  suffices hpc : IsPathConnected Sᶜ from hpc.isConnected.isPreconnected
  refine ⟨(R0 : ℂ), hbase, fun z hz => ?_⟩
  have hzne : z ≠ 0 := fun h => hz (h ▸ hS0)
  have hzn_pos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
  -- First join `(R0 : ℂ)` to `(R0 / ‖z‖) * z` along the circle of radius `R0`.
  set θ : ℝ := Complex.arg z
  have hpolar : ((R0 / ‖z‖ : ℝ) : ℂ) * z = (R0 : ℂ) * Complex.exp ((θ : ℂ) * I) := by
    have hp := Complex.norm_mul_exp_arg_mul_I z
    have hzn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hzn_pos.ne'
    calc ((R0 / ‖z‖ : ℝ) : ℂ) * z
        = ((R0 / ‖z‖ : ℝ) : ℂ) * ((‖z‖ : ℂ) * Complex.exp ((θ : ℂ) * I)) := by rw [hp]
      _ = (R0 : ℂ) * Complex.exp ((θ : ℂ) * I) := by push_cast; field_simp [hzn]
  have hJ1 : JoinedIn Sᶜ (R0 : ℂ) (((R0 / ‖z‖ : ℝ) : ℂ) * z) := by
    rw [hpolar]
    refine ⟨{
      toFun := fun t => (R0 : ℂ) * Complex.exp ((((t : ℝ) * θ : ℝ) : ℂ) * I)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp
    }, fun t => houtside _ ?_⟩
    change R0 ≤ ‖(R0 : ℂ) * Complex.exp ((((t : ℝ) * θ : ℝ) : ℂ) * I)‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR0_pos.le,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hJ2 : JoinedIn Sᶜ (((R0 / ‖z‖ : ℝ) : ℂ) * z) z := by
    refine ⟨{
      toFun := fun t => (((1 - (t : ℝ)) * (R0 / ‖z‖) + (t : ℝ) : ℝ) : ℂ) * z
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp
    }, fun t => ?_⟩
    set s : ℝ := (1 - (t : ℝ)) * (R0 / ‖z‖) + (t : ℝ)
    change ((s : ℂ) * z) ∈ Sᶜ
    by_cases hle : ‖z‖ ≤ R0
    · have hs1 : 1 ≤ s := by
        have h1 : 1 ≤ R0 / ‖z‖ := (one_le_div hzn_pos).mpr hle
        have ht0 : 0 ≤ (t : ℝ) := t.2.1
        have ht1 : (t : ℝ) ≤ 1 := t.2.2
        dsimp only [s]; nlinarith
      intro hmem
      have hs_pos : 0 < s := by linarith
      have hinv_mem := hS_star _ hmem (1 / s) (by positivity) ((div_le_one hs_pos).mpr hs1)
      have heq : ((1 / s : ℝ) : ℂ) * ((s : ℂ) * z) = z := by
        have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs_pos.ne'
        push_cast; field_simp [hs0]
      rw [heq] at hinv_mem
      exact hz hinv_mem
    · push Not at hle
      refine houtside _ ?_
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      have hs_pos : 0 < s := by
        have h1 : 0 < R0 / ‖z‖ := div_pos hR0_pos hzn_pos
        dsimp only [s]
        rcases eq_or_lt_of_le ht0 with ht0' | ht0'
        · rw [← ht0']; linarith
        · have : 0 ≤ (1 - (t : ℝ)) * (R0 / ‖z‖) := mul_nonneg (by linarith) h1.le
          linarith
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs_pos.le]
      have : s * ‖z‖ = (1 - (t : ℝ)) * R0 + (t : ℝ) * ‖z‖ := by
        simp only [s]; field_simp [hzn_pos.ne']
      rw [this]; nlinarith
  exact hJ1.trans hJ2

lemma isPreconnected_of_starShaped_zero {T : Set ℂ} (hT0 : (0 : ℂ) ∈ T)
    (hT_star : ∀ z ∈ T, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (t : ℂ) * z ∈ T) :
    IsPreconnected T := by
  suffices hpc : IsPathConnected T from hpc.isConnected.isPreconnected
  refine ⟨(0 : ℂ), hT0, fun z hz => ?_⟩
  refine ⟨{
    toFun := fun t => ((t : ℝ) : ℂ) * z
    continuous_toFun := by fun_prop
    source' := by simp
    target' := by simp
  }, fun t => hT_star z hz t t.2.1 t.2.2⟩

/-- Degree-1 covering biholomorphism lemma on the unit disk. -/
lemma biholomorphism_of_degree_one {T : Set ℂ} {g : ℂ → ℂ}
    (hTo : IsOpen T) (hTc : IsPreconnected T) (hT0 : (0 : ℂ) ∈ T)
    (hT_int : interior (closure T) = T)
    (hT_compl_conn : IsPreconnected (closure T)ᶜ)
    (hT_bdd : Bornology.IsBounded T)
    (hg_cont : ContinuousOn g (closedBall 0 1))
    (hg_diff : DifferentiableOn ℂ g (ball 0 1))
    (hg_dne : ∀ ζ ∈ ball (0 : ℂ) 1, deriv g ζ ≠ 0)
    (hg_front : MapsTo g (sphere 0 1) (frontier T))
    (hg_zero : ∀ ζ ∈ closedBall (0 : ℂ) 1, g ζ = 0 ↔ ζ = 0) :
    MapsTo g (ball 0 1) T ∧ ∀ w ∈ T, ∃! ζ ∈ ball (0 : ℂ) 1, g ζ = w := by
  -- Step 1: `g '' ball 0 1` is open (via Inverse Function Theorem at every point).
  have hg_open_img : IsOpen (g '' ball 0 1) := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨ζ, hζ, rfl⟩
    have hsd := differentiableOn_hasStrictDerivAt isOpen_ball hg_diff hζ
    have hmap := hsd.map_nhds_eq (hg_dne ζ hζ)
    have hmem : ball (0 : ℂ) 1 ∈ 𝓝 ζ := isOpen_ball.mem_nhds hζ
    have h1 : g '' ball 0 1 ∈ Filter.map g (𝓝 ζ) := Filter.image_mem_map hmem
    rwa [hmap] at h1
  -- Step 2: `g '' ball 0 1 ⊆ T` (clopen bounded subset of connected unbounded `(closure T)ᶜ`).
  have hg_maps : MapsTo g (ball 0 1) T := by
    have hdisj : Disjoint (g '' ball 0 1) (closure T)ᶜ := by
      rw [Set.disjoint_iff]
      -- Show `U := (g '' ball 0 1) ∩ (closure T)ᶜ` is empty.
      set U : Set ℂ := g '' ball 0 1 ∩ (closure T)ᶜ
      have hcl_eq : g '' closedBall 0 1 ∩ (closure T)ᶜ = U := by
        ext w
        constructor
        · rintro ⟨⟨ζ, hζ, rfl⟩, hw⟩
          have hball : ζ ∈ ball (0 : ℂ) 1 := by
            by_contra hnb
            have hsph : ζ ∈ sphere (0 : ℂ) 1 := by
              rw [Metric.mem_sphere]; rw [Metric.mem_closedBall] at hζ
              rw [Metric.mem_ball] at hnb; linarith
            exact hw (frontier_subset_closure (hg_front hsph))
          exact ⟨⟨ζ, hball, rfl⟩, hw⟩
        · rintro ⟨⟨ζ, hζ, rfl⟩, hw⟩
          exact ⟨⟨ζ, ball_subset_closedBall hζ, rfl⟩, hw⟩
      have hU_closed : IsClosed (g '' closedBall 0 1) :=
        ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hg_cont).isClosed
      -- `(closure T)ᶜ ⊆ (g '' ball 0 1) ∪ (g '' closedBall 0 1)ᶜ` — two disjoint open sets!
      have hsub : (closure T)ᶜ ⊆ g '' ball 0 1 ∪ (g '' closedBall 0 1)ᶜ := by
        intro w hw
        by_cases hmem : w ∈ g '' ball 0 1
        · exact Or.inl hmem
        · right; intro hcl
          have hwU : w ∈ U := hcl_eq ▸ ⟨hcl, hw⟩
          exact hmem hwU.1
      have hdisj_in : Disjoint (g '' ball 0 1) (g '' closedBall 0 1)ᶜ :=
        Set.disjoint_iff.mpr fun _ ⟨h1, h2⟩ => h2 (image_mono ball_subset_closedBall h1)
      have hne_right : ((closure T)ᶜ ∩ (g '' closedBall 0 1)ᶜ).Nonempty := by
        have hb1 : Bornology.IsBounded (closure T) := hT_bdd.closure
        have hb2 : Bornology.IsBounded (g '' closedBall 0 1) :=
          ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hg_cont).isBounded
        obtain ⟨M1, hM1⟩ := hb1.subset_closedBall (0 : ℂ)
        obtain ⟨M2, hM2⟩ := hb2.subset_closedBall (0 : ℂ)
        set M : ℝ := max (max M1 M2) 0 + 1
        refine ⟨(M : ℂ), ?_, ?_⟩
        · intro hm
          have hle : M ≤ M1 := by
            have := hM1 hm
            rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
              Real.norm_of_nonneg (by positivity)] at this
            exact this
          have : M1 < M := lt_of_le_of_lt ((le_max_left M1 M2).trans (le_max_left _ _)) (lt_add_one _)
          linarith
        · intro hm
          have hle : M ≤ M2 := by
            have := hM2 hm
            rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
              Real.norm_of_nonneg (by positivity)] at this
            exact this
          have : M2 < M := lt_of_le_of_lt ((le_max_right M1 M2).trans (le_max_left _ _)) (lt_add_one _)
          linarith
      have hright := hT_compl_conn.subset_right_of_subset_union hg_open_img hU_closed.isOpen_compl
        hdisj_in hsub hne_right
      intro w ⟨hw1, hw2⟩
      exact hright hw2 (image_mono ball_subset_closedBall hw1)
    have hsub_cl : g '' ball 0 1 ⊆ closure T := by
      intro w hw
      by_contra hnc
      exact Set.disjoint_left.mp hdisj hw hnc
    intro ζ hζ
    rw [← hT_int]
    exact interior_maximal hsub_cl hg_open_img ⟨ζ, hζ, rfl⟩
  -- Step 3: For each `w ∈ T`, the fiber `F w = {ζ ∈ ball 0 1 | g ζ = w}` is finite,
  -- and its cardinality is locally constant on `T`.
  let F : ℂ → Set ℂ := fun w => {ζ ∈ ball (0 : ℂ) 1 | g ζ = w}
  have hF_eq_closed : ∀ w ∈ T, F w = {ζ ∈ closedBall (0 : ℂ) 1 | g ζ = w} := by
    intro w hw
    ext ζ
    constructor
    · rintro ⟨hζ, rfl⟩; exact ⟨ball_subset_closedBall hζ, rfl⟩
    · rintro ⟨hζ, rfl⟩
      refine ⟨?_, rfl⟩
      by_contra hnb
      have hsph : ζ ∈ sphere (0 : ℂ) 1 := by
        rw [Metric.mem_sphere]; rw [Metric.mem_closedBall] at hζ
        rw [Metric.mem_ball] at hnb; linarith
      have hfr := hg_front hsph
      rw [frontier, hTo.interior_eq] at hfr
      exact hfr.2 hw
  have hF_fin : ∀ w ∈ T, (F w).Finite := by
    intro w hw
    have hcomp : IsCompact (F w) := by
      rw [hF_eq_closed w hw]
      have hcl : IsClosed ({ζ ∈ closedBall (0 : ℂ) 1 | g ζ = w}) := by
        have : {ζ ∈ closedBall (0 : ℂ) 1 | g ζ = w} = closedBall (0 : ℂ) 1 ∩ g ⁻¹' {w} := rfl
        rw [this]
        exact hg_cont.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
      exact (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hcl (fun _ h => h.1)
    -- Every point `ζ ∈ F w` has an open neighborhood containing no other point of `F w`.
    have hdisc : ∀ ζ ∈ F w, ∃ U : Set ℂ, IsOpen U ∧ ζ ∈ U ∧ U ∩ F w = {ζ} := by
      intro ζ ⟨hζ, hgz⟩
      have hsd := differentiableOn_hasStrictDerivAt isOpen_ball hg_diff hζ
      set e := (hsd.hasStrictFDerivAt_equiv (hg_dne ζ hζ)).toOpenPartialHomeomorph g
      refine ⟨e.source ∩ ball 0 1, e.open_source.inter isOpen_ball,
        ⟨(hsd.hasStrictFDerivAt_equiv (hg_dne ζ hζ)).mem_toOpenPartialHomeomorph_source, hζ⟩, ?_⟩
      ext z
      constructor
      · rintro ⟨⟨hz_src, _⟩, ⟨_, hgz'⟩⟩
        rw [mem_singleton_iff]
        have hcoe : (e : ℂ → ℂ) = g :=
          (hsd.hasStrictFDerivAt_equiv (hg_dne ζ hζ)).toOpenPartialHomeomorph_coe
        have heq : e z = e ζ := by rw [hcoe, hgz', hgz]
        exact e.injOn hz_src
          (hsd.hasStrictFDerivAt_equiv (hg_dne ζ hζ)).mem_toOpenPartialHomeomorph_source heq
      · rintro rfl
        exact ⟨⟨(hsd.hasStrictFDerivAt_equiv (hg_dne z hζ)).mem_toOpenPartialHomeomorph_source, hζ⟩,
          ⟨hζ, hgz⟩⟩
    choose U hUo hUmem hUint using hdisc
    have hcov : F w ⊆ ⋃ ζ : F w, U ζ.1 ζ.2 := fun ζ hζ =>
      mem_iUnion.mpr ⟨⟨ζ, hζ⟩, hUmem ζ hζ⟩
    obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover (fun ζ : F w => U ζ.1 ζ.2)
      (fun ζ => hUo ζ.1 ζ.2) hcov
    refine (t.finite_toSet.image (fun ζ : F w => ζ.1)).subset fun z hz => ?_
    obtain ⟨ζ, hζt, hzU⟩ := mem_iUnion₂.mp (ht hz)
    have hzeq : z = ζ.1 := by
      have : z ∈ U ζ.1 ζ.2 ∩ F w := ⟨hzU, hz⟩
      rwa [hUint ζ.1 ζ.2, mem_singleton_iff] at this
    exact ⟨ζ, hζt, hzeq.symm⟩
  -- Step 4: Local constancy of `N w := (F w).ncard` on `T`.
  have hN_loc : ∀ w₀ ∈ T, ∃ W : Set ℂ, IsOpen W ∧ w₀ ∈ W ∧ W ⊆ T ∧
      ∀ w ∈ W, (F w).ncard = (F w₀).ncard := by
    intro w₀ hw₀
    set s : Finset ℂ := (hF_fin w₀ hw₀).toFinset
    have hs_mem : ∀ ζ, ζ ∈ s ↔ ζ ∈ F w₀ := fun ζ => Finite.mem_toFinset _
    -- For each `ζ ∈ s`, choose an open ball around `ζ` contained in `e_ζ.source ∩ ball 0 1`
    -- and pairwise disjoint from all other `ζ' ∈ s`.
    have hsep : ∀ ζ ∈ s, ∃ r : ℝ, 0 < r ∧ ball ζ r ⊆ ball 0 1 ∧
        (∀ ζ' ∈ s, ζ' ≠ ζ → Disjoint (ball ζ r) (ball ζ' r)) ∧
        ∃ e : OpenPartialHomeomorph ℂ ℂ, (e : ℂ → ℂ) = g ∧ ball ζ r ⊆ e.source := by
      intro ζ hζs
      have hζF : ζ ∈ F w₀ := (hs_mem ζ).mp hζs
      have hsd := differentiableOn_hasStrictDerivAt isOpen_ball hg_diff hζF.1
      set e := (hsd.hasStrictFDerivAt_equiv (hg_dne ζ hζF.1)).toOpenPartialHomeomorph g
      have hopen : IsOpen (e.source ∩ ball 0 1) := e.open_source.inter isOpen_ball
      have hmem : ζ ∈ e.source ∩ ball 0 1 :=
        ⟨(hsd.hasStrictFDerivAt_equiv (hg_dne ζ hζF.1)).mem_toOpenPartialHomeomorph_source, hζF.1⟩
      obtain ⟨r0, hr0, hbr0⟩ := Metric.isOpen_iff.mp hopen ζ hmem
      -- Minimum distance to other points in `s`
      set s' : Finset ℂ := s.erase ζ
      obtain ⟨r1, hr1, hr1_le⟩ : ∃ r1 : ℝ, 0 < r1 ∧ ∀ ζ' ∈ s, ζ' ≠ ζ → 2 * r1 ≤ dist ζ ζ' := by
        by_cases hemp : s'.Nonempty
        · refine ⟨(s'.inf' hemp (fun ζ' => dist ζ ζ')) / 3, ?_, ?_⟩
          · have hpos : 0 < s'.inf' hemp (fun ζ' => dist ζ ζ') := by
              rw [Finset.lt_inf'_iff]
              intro ζ' hζ'
              exact dist_pos.mpr (Finset.ne_of_mem_erase hζ').symm
            linarith
          · intro ζ' hζ' hne
            have hm : ζ' ∈ s' := Finset.mem_erase.mpr ⟨hne, hζ'⟩
            have hle : s'.inf' hemp (fun x => dist ζ x) ≤ dist ζ ζ' := Finset.inf'_le _ hm
            have hpos : 0 < s'.inf' hemp (fun x => dist ζ x) := by
              rw [Finset.lt_inf'_iff]; intro x hx; exact dist_pos.mpr (Finset.ne_of_mem_erase hx).symm
            linarith
        · rw [Finset.not_nonempty_iff_eq_empty] at hemp
          refine ⟨1, by norm_num, fun ζ' hζ' hne => ?_⟩
          have : ζ' ∈ s' := Finset.mem_erase.mpr ⟨hne, hζ'⟩
          rw [hemp] at this; exact absurd this (Finset.notMem_empty _)
      set r := min r0 r1
      refine ⟨r, lt_min hr0 hr1, (Metric.ball_subset_ball (min_le_left _ _)).trans (hbr0.trans inter_subset_right), ?_, e,
        (hsd.hasStrictFDerivAt_equiv (hg_dne ζ hζF.1)).toOpenPartialHomeomorph_coe,
        (Metric.ball_subset_ball (min_le_left _ _)).trans (hbr0.trans inter_subset_left)⟩
      intro ζ' hζ' hne
      rw [Set.disjoint_iff]
      intro z ⟨hz1, hz2⟩
      rw [Metric.mem_ball, dist_comm] at hz1 hz2
      have htri := dist_triangle_right ζ ζ' z
      have hrle : r ≤ r1 := min_le_right _ _
      have h2 := hr1_le ζ' hζ' hne
      linarith
    -- Pick a single uniform small `r` across all `ζ ∈ s`!
    choose r_fn hr_pos hr_ball hr_disj e_fn he_coe he_sub using hsep
    obtain ⟨r0, hr0_pos, hr0_le⟩ : ∃ r0 : ℝ, 0 < r0 ∧ ∀ (ζ : ℂ) (hζ : ζ ∈ s), r0 ≤ r_fn ζ hζ := by
      by_cases hne : s.attach.Nonempty
      · refine ⟨s.attach.inf' hne (fun p => r_fn p.1 p.2), ?_, ?_⟩
        · rw [Finset.lt_inf'_iff]; intro p _; exact hr_pos p.1 p.2
        · intro ζ hζ; exact Finset.inf'_le (fun p : {x // x ∈ s} => r_fn p.1 p.2) (Finset.mem_attach _ ⟨ζ, hζ⟩)
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        refine ⟨1, by norm_num, fun ζ hζ => ?_⟩
        have : (⟨ζ, hζ⟩ : {x // x ∈ s}) ∈ s.attach := Finset.mem_attach _ _
        rw [hne] at this; exact absurd this (Finset.notMem_empty _)
    let V : ℂ → Set ℂ := fun ζ => ball ζ r0
    have hV_disj : ∀ ζ ∈ s, ∀ ζ' ∈ s, ζ ≠ ζ' → Disjoint (V ζ) (V ζ') := by
      intro ζ hζ ζ' hζ' hne
      exact (hr_disj ζ hζ ζ' hζ' hne.symm).mono
        (Metric.ball_subset_ball (hr0_le ζ hζ)) (Metric.ball_subset_ball (hr0_le ζ hζ))
    have hV_open_img : ∀ (ζ : ℂ) (hζ : ζ ∈ s), IsOpen (g '' V ζ) := by
      intro ζ hζ
      have hsub : V ζ ⊆ (e_fn ζ hζ).source :=
        (Metric.ball_subset_ball (hr0_le ζ hζ)).trans (he_sub ζ hζ)
      have heq : g '' V ζ = (e_fn ζ hζ) '' V ζ := by rw [he_coe ζ hζ]
      rw [heq]
      exact (e_fn ζ hζ).isOpen_image_of_subset_source isOpen_ball hsub
    -- Compact complement `K := closedBall 0 1 \ ⋃ ζ ∈ s, V ζ`
    set U_union : Set ℂ := ⋃ ζ ∈ s, V ζ
    have hU_open : IsOpen U_union := isOpen_biUnion fun _ _ => isOpen_ball
    set K : Set ℂ := closedBall 0 1 \ U_union
    have hK_comp : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).diff hU_open
    have hgK_closed : IsClosed (g '' K) :=
      (hK_comp.image_of_continuousOn (hg_cont.mono sdiff_subset)).isClosed
    have hw0_not_gK : w₀ ∉ g '' K := by
      rintro ⟨ζ, ⟨hζc, hζnU⟩, hgz⟩
      have hζF : ζ ∈ F w₀ := by rw [hF_eq_closed w₀ hw₀]; exact ⟨hζc, hgz⟩
      have hζs : ζ ∈ s := (hs_mem ζ).mpr hζF
      exact hζnU (mem_iUnion₂.mpr ⟨ζ, hζs, Metric.mem_ball_self hr0_pos⟩)
    set W : Set ℂ := T ∩ (g '' K)ᶜ ∩ ⋂ (p : {x // x ∈ s}), g '' V p.1
    have hW_open : IsOpen W :=
      (hTo.inter hgK_closed.isOpen_compl).inter (isOpen_iInter_of_finite fun p => hV_open_img p.1 p.2)
    have hw0_W : w₀ ∈ W := by
      refine ⟨⟨hw₀, hw0_not_gK⟩, mem_iInter.mpr fun p => ?_⟩
      exact ⟨p.1, Metric.mem_ball_self hr0_pos, ((hs_mem p.1).mp p.2).2⟩
    refine ⟨W, hW_open, hw0_W, fun _ h => h.1.1, fun w hw => ?_⟩
    -- Establish a bijection between `s` (`F w₀`) and `F w`!
    have huniq : ∀ p : {x // x ∈ s}, ∃! z ∈ V p.1, g z = w := by
      intro p
      have hw_img : w ∈ g '' V p.1 := (mem_iInter.mp hw.2) p
      obtain ⟨z, hzV, hgz⟩ := hw_img
      refine ⟨z, ⟨hzV, hgz⟩, fun z' ⟨hz'V, hgz'⟩ => ?_⟩
      have hsub : V p.1 ⊆ (e_fn p.1 p.2).source :=
        (Metric.ball_subset_ball (hr0_le p.1 p.2)).trans (he_sub p.1 p.2)
      have heq : (e_fn p.1 p.2) z' = (e_fn p.1 p.2) z := by rw [he_coe p.1 p.2, hgz', hgz]
      exact (e_fn p.1 p.2).injOn (hsub hz'V) (hsub hzV) heq
    choose φ_w hφ_mem hφ_uniq using huniq
    have hFw_eq : F w = range φ_w := by
      ext z
      constructor
      · intro hzF
        have hzc : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hzF.1
        have hzU : z ∈ U_union := by
          by_contra hznU
          exact hw.1.2 ⟨z, ⟨hzc, hznU⟩, hzF.2⟩
        obtain ⟨ζ, hζs, hzV⟩ := mem_iUnion₂.mp hzU
        exact ⟨⟨ζ, hζs⟩, (hφ_uniq ⟨ζ, hζs⟩ z ⟨hzV, hzF.2⟩).symm⟩
      · rintro ⟨p, rfl⟩
        have hball : V p.1 ⊆ ball 0 1 :=
          (Metric.ball_subset_ball (hr0_le p.1 p.2)).trans (hr_ball p.1 p.2)
        exact ⟨hball (hφ_mem p).1, (hφ_mem p).2⟩
    have hφ_inj : Function.Injective φ_w := by
      intro p q heq
      by_contra hne
      have hne_val : p.1 ≠ q.1 := fun h => hne (Subtype.ext h)
      have hdisj := hV_disj p.1 p.2 q.1 q.2 hne_val
      have hm1 : φ_w p ∈ V p.1 := (hφ_mem p).1
      have hm2 : φ_w p ∈ V q.1 := heq ▸ (hφ_mem q).1
      exact Set.disjoint_left.mp hdisj hm1 hm2
    rw [hFw_eq, Set.ncard_range_of_injective hφ_inj, Nat.card_eq_fintype_card, Fintype.card_coe]
    have hnc : (F w₀).ncard = s.card := by
      rw [← Set.ncard_coe_finset s]
      congr 1; ext ζ; exact (hs_mem ζ).symm
    exact hnc.symm
  -- Step 5: Since `N w` is locally constant on preconnected `T`, `N w = N 0 = 1` for all `w ∈ T`!
  have hF0_eq : F 0 = {0} := by
    ext ζ
    constructor
    · rintro ⟨hζ, hgz⟩
      rw [mem_singleton_iff]
      exact (hg_zero ζ (ball_subset_closedBall hζ)).mp hgz
    · rintro rfl
      exact ⟨Metric.mem_ball_self zero_lt_one, (hg_zero 0 (Metric.mem_closedBall_self zero_le_one)).mpr rfl⟩
  have hN0 : (F 0).ncard = 1 := by rw [hF0_eq, Set.ncard_singleton]
  have hN_one : ∀ w ∈ T, (F w).ncard = 1 := by
    set A : Set ℂ := {w ∈ T | (F w).ncard = 1}
    set B : Set ℂ := {w ∈ T | (F w).ncard ≠ 1}
    have hAo : IsOpen A := by
      rw [isOpen_iff_mem_nhds]
      intro w ⟨hwT, hw1⟩
      obtain ⟨W, hWo, hwW, hWT, hWN⟩ := hN_loc w hwT
      exact Filter.mem_of_superset (hWo.mem_nhds hwW) fun y hy => ⟨hWT hy, (hWN y hy).trans hw1⟩
    have hBo : IsOpen B := by
      rw [isOpen_iff_mem_nhds]
      intro w ⟨hwT, hw1⟩
      obtain ⟨W, hWo, hwW, hWT, hWN⟩ := hN_loc w hwT
      exact Filter.mem_of_superset (hWo.mem_nhds hwW) fun y hy => ⟨hWT hy, by rw [hWN y hy]; exact hw1⟩
    have hsub : T ⊆ A ∪ B := fun w hw => by
      by_cases h : (F w).ncard = 1
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr ⟨hw, h⟩
    have hdisj : Disjoint A B := Set.disjoint_iff.mpr fun _ ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => h2 h1
    have hneA : (T ∩ A).Nonempty := ⟨0, hT0, hT0, hN0⟩
    have hT_sub_A := hTc.subset_left_of_subset_union hAo hBo hdisj hsub hneA
    intro w hw; exact (hT_sub_A hw).2
  refine ⟨hg_maps, fun w hw => ?_⟩
  obtain ⟨ζ, hζ⟩ := Set.ncard_eq_one.mp (hN_one w hw)
  have hζ_mem : ζ ∈ F w := by rw [hζ]; exact mem_singleton ζ
  exact ⟨ζ, hζ_mem, fun ζ' hζ' => by change ζ' ∈ F w at hζ'; rw [hζ, mem_singleton_iff] at hζ'; exact hζ'⟩

/- ## 2. Biholomorphisms `u6`, `u3`, Boundary Injectivity, and `φ = u3 ∘ u6Inv` -/

lemma isPreconnected_Δ1Open : IsPreconnected Δ1Open :=
  isPreconnected_of_starShaped_zero zero_mem_Δ1Open fun z hz t ht0 ht1 => by
    rcases eq_or_lt_of_le ht1 with rfl | hlt
    · simpa using hz
    · exact smul_mem_Δ1Open_of_mem_Δ1 ⟨hz.1, fun j => (hz.2 j).le⟩ ht0 hlt

lemma isPreconnected_Δ2Open : IsPreconnected Δ2Open :=
  isPreconnected_of_starShaped_zero zero_mem_Δ2Open fun w hw t ht0 ht1 => by
    rcases eq_or_lt_of_le ht1 with rfl | hlt
    · simpa using hw
    · exact smul_mem_Δ2Open_of_mem_Δ2 (fun j => (hw j).le) ht0 hlt

lemma u6_biholo :
    MapsTo u6 (ball 0 1) Δ1Open ∧ ∀ z ∈ Δ1Open, ∃! ζ ∈ ball (0 : ℂ) 1, u6 ζ = z := by
  have hcompl : IsPreconnected (closure Δ1Open)ᶜ := by
    rw [closure_Δ1Open]
    exact isPreconnected_compl_of_starShaped_bounded
      ⟨zero_mem_Δ1Open.1, fun j => (zero_mem_Δ1Open.2 j).le⟩
      (fun z hz t ht0 ht1 => smul_mem_Δ1 hz ht0 ht1) isCompact_Δ1.isBounded
  refine biholomorphism_of_degree_one isOpen_Δ1Open isPreconnected_Δ1Open zero_mem_Δ1Open
    (by rw [closure_Δ1Open, interior_Δ1]) hcompl isBounded_Δ1Open
    u6_continuousOn_closedBall u6_differentiableOn_ball
    (fun ζ hζ => u6_deriv_ne_zero_of_I0_ne_zero (ball_subset_Ω hζ)
      (I0_ne_zero_of_norm_le_one (le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hζ))))
    u6_maps_sphere_to_frontier
    (fun ζ hζ => u6_eq_zero_iff (by simpa [Metric.mem_closedBall, dist_zero_right] using hζ))

lemma u3_biholo :
    MapsTo u3 (ball 0 1) Δ2Open ∧ ∀ w ∈ Δ2Open, ∃! ζ ∈ ball (0 : ℂ) 1, u3 ζ = w := by
  have hcompl : IsPreconnected (closure Δ2Open)ᶜ := by
    rw [closure_Δ2Open]
    exact isPreconnected_compl_of_starShaped_bounded
      (fun j => (zero_mem_Δ2Open j).le)
      (fun w hw t ht0 ht1 => smul_mem_Δ2 hw ht0 ht1) (closure_Δ2Open ▸ isBounded_Δ2Open.closure)
  refine biholomorphism_of_degree_one isOpen_Δ2Open isPreconnected_Δ2Open zero_mem_Δ2Open
    (by rw [closure_Δ2Open, interior_Δ2]) hcompl isBounded_Δ2Open
    u3_continuousOn_closedBall (u3_differentiableOn_Ω.mono ball_subset_Ω)
    (fun ζ hζ => u3_deriv_ne_zero (ball_subset_Ω hζ))
    u3_maps_sphere_to_frontier
    (fun ζ hζ => u3_eq_zero_iff (by simpa [Metric.mem_closedBall, dist_zero_right] using hζ))

/-- Two distinct geodesic sides of `Δ1` intersect inside `ball 0 1` only at their shared vertex. -/
lemma side0_inter_side1_eq_vert1 {z : ℂ} (hz1 : ‖z‖ < 1)
    (hs0 : ‖z - sideCenter 0‖ ^ 2 = ‖sideCenter 0‖ ^ 2 - 1)
    (hs1 : ‖z - sideCenter 1‖ ^ 2 = ‖sideCenter 1‖ ^ 2 - 1) :
    z = vert1 1 := by
  have h0 : ‖z‖ ^ 2 - 2 * (z * starRingEnd ℂ (sideCenter 0)).re + 1 = 0 := by
    linarith [normSq_sub_sideCenter_iff 0 z]
  have h1 : ‖z‖ ^ 2 - 2 * (z * starRingEnd ℂ (sideCenter 1)).re + 1 = 0 := by
    linarith [normSq_sub_sideCenter_iff 1 z]
  have hre_eq : (z * starRingEnd ℂ (sideCenter 0)).re = (z * starRingEnd ℂ (sideCenter 1)).re := by
    linarith
  set M : ℝ := (2 + Real.sqrt 3) * R
  have hM_pos : 0 < M := by have := R_pos; have := sqrt3_pos; positivity
  -- Compute `(z * conj(sideCenter 0 - sideCenter 1)).re = 0`:
  -- `sideCenter 0 = M (1/2 + i√3/2)`, `sideCenter 1 = -M`, so `sideCenter 0 - sideCenter 1 = M (3/2 + i√3/2)`.
  have ha0 : sideCenter 0 = (M : ℂ) * ⟨1 / 2, Real.sqrt 3 / 2⟩ := by
    simp only [sideCenter, Fin.val_zero, pow_zero, one_mul, a0, one_add_ω, M]
  have ha1 : sideCenter 1 = -((M : ℂ)) := by
    simp only [sideCenter, Fin.val_one, pow_one, a0, M]
    have : ω * (1 + ω) = -1 := by linear_combination ω_sq_add_ω_add_one
    linear_combination (M : ℂ) * this
  have hre0 : (z * starRingEnd ℂ (sideCenter 0)).re = M * (z.re / 2 + z.im * Real.sqrt 3 / 2) := by
    rw [ha0, map_mul, Complex.conj_ofReal]
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, conj_re, conj_im, zero_mul, sub_zero, add_zero]
    ring
  have hre1 : (z * starRingEnd ℂ (sideCenter 1)).re = -M * z.re := by
    rw [ha1, map_neg, Complex.conj_ofReal]
    simp only [mul_neg, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    ring
  rw [hre0, hre1] at hre_eq
  have hlin : 3 * z.re + Real.sqrt 3 * z.im = 0 := by nlinarith
  -- Hence `z = t * ω` where `t = -2 * z.re`!
  set t : ℝ := -2 * z.re
  have hz_im : z.im = t * (Real.sqrt 3 / 2) := by
    have h3 : Real.sqrt 3 * (Real.sqrt 3 * z.im) = 3 * z.im := by linear_combination z.im * sq_sqrt3
    have hmul : Real.sqrt 3 * (3 * z.re + Real.sqrt 3 * z.im) = 0 := by rw [hlin, mul_zero]
    simp only [t]; nlinarith [h3, hmul]
  have hz_eq : z = (t : ℂ) * ω := by
    apply Complex.ext
    · simp only [mul_re, ofReal_re, ofReal_im, ω_re, ω_im, zero_mul, sub_zero, t]; ring
    · simp only [mul_im, ofReal_re, ofReal_im, ω_re, ω_im, zero_mul, add_zero, hz_im]
  have hnorm_z : ‖z‖ ^ 2 = t ^ 2 := by
    rw [hz_eq, norm_mul, norm_ω, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hre1' : (z * starRingEnd ℂ (sideCenter 1)).re = M * t / 2 := by
    rw [hre1]; simp only [t]; ring
  rw [hnorm_z, hre1'] at h1
  -- `t^2 - M * t + 1 = 0`, and `M = R + 1 / R`, so `(t - R) * (t - 1 / R) = 0`!
  have hMR : M * R = 1 + R ^ 2 := by simp only [M]; linarith [R_sq_mul]
  have hfac : (t - R) * (R * t - 1) = 0 := by linear_combination R * h1 + t * hMR
  have ht_abs : |t| < 1 := by
    have : ‖z‖ = |t| := by
      rw [hz_eq, norm_mul, norm_ω, mul_one, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hne2 : R * t - 1 ≠ 0 := by
    have ht_le : t < 1 := (abs_lt.mp ht_abs).2
    have hlt : R * t < 1 := by
      rcases le_or_gt t 0 with ht0 | ht0
      · nlinarith [R_pos]
      · nlinarith [R_pos, R_lt_one]
    linarith
  have htR : t = R := sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hne2)
  rw [hz_eq, htR]; simp [vert1, mul_comm]

lemma side_inter_side_eq_vert1 {j k : Fin 3} (hjk : j ≠ k) {z : ℂ} (hz1 : ‖z‖ < 1)
    (hsj : ‖z - sideCenter j‖ ^ 2 = ‖sideCenter j‖ ^ 2 - 1)
    (hsk : ‖z - sideCenter k‖ ^ 2 = ‖sideCenter k‖ ^ 2 - 1) :
    (j = 0 ∧ k = 1 → z = vert1 1) ∧
    (j = 1 ∧ k = 2 → z = vert1 2) ∧
    (j = 2 ∧ k = 0 → z = vert1 0) := by
  refine ⟨fun ⟨hj, hk⟩ => side0_inter_side1_eq_vert1 hz1 (hj ▸ hsj) (hk ▸ hsk), ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩
    have hnorm : ‖ω ^ 2 * z‖ < 1 := by rw [norm_mul, norm_ω_pow, one_mul]; exact hz1
    have h0 : ‖ω ^ 2 * z - sideCenter 0‖ ^ 2 = ‖sideCenter 0‖ ^ 2 - 1 := by
      have ha : sideCenter 0 = ω ^ 2 * sideCenter 1 := by
        simp only [sideCenter, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul]
        linear_combination -a0 * ω_cube
      rw [ha, ← mul_sub, norm_mul, norm_ω_pow, one_mul, norm_mul, norm_ω_pow, one_mul]
      exact hsj
    have h1 : ‖ω ^ 2 * z - sideCenter 1‖ ^ 2 = ‖sideCenter 1‖ ^ 2 - 1 := by
      have ha : sideCenter 1 = ω ^ 2 * sideCenter 2 := by
        simp only [sideCenter, Fin.val_one, Fin.val_two, pow_one]
        linear_combination -ω * a0 * ω_cube
      rw [ha, ← mul_sub, norm_mul, norm_ω_pow, one_mul, norm_mul, norm_ω_pow, one_mul]
      exact hsk
    have hres := side0_inter_side1_eq_vert1 hnorm h0 h1
    have := congrArg (ω * ·) hres
    simp only [vert1, Fin.val_one, Fin.val_two, pow_one] at this ⊢
    linear_combination this - z * ω_cube
  · rintro ⟨rfl, rfl⟩
    have hnorm : ‖ω * z‖ < 1 := by rw [norm_mul, norm_ω, one_mul]; exact hz1
    have h0 : ‖ω * z - sideCenter 0‖ ^ 2 = ‖sideCenter 0‖ ^ 2 - 1 := by
      have ha : sideCenter 0 = ω * sideCenter 2 := by
        simp only [sideCenter, Fin.val_zero, Fin.val_two, pow_zero, one_mul]
        linear_combination -a0 * ω_cube
      rw [ha, ← mul_sub, norm_mul, norm_ω, one_mul, norm_mul, norm_ω, one_mul]
      exact hsj
    have h1 : ‖ω * z - sideCenter 1‖ ^ 2 = ‖sideCenter 1‖ ^ 2 - 1 := by
      have ha : sideCenter 1 = ω * sideCenter 0 := by simp [sideCenter]
      rw [ha, ← mul_sub, norm_mul, norm_ω, one_mul, norm_mul, norm_ω, one_mul]
      exact hsk
    have hres := side0_inter_side1_eq_vert1 hnorm h0 h1
    have := congrArg (ω ^ 2 * ·) hres
    simp only [vert1, Fin.val_one, Fin.val_zero, pow_one, pow_zero, one_mul] at this ⊢
    linear_combination this + ((R : ℂ) - z) * ω_cube

/-- Strict injectivity of `u6` on the boundary arc `[0, 2π/3]` and strict membership off vertices. -/
lemma u6_arc_injOn : InjOn (fun θ : ℝ => u6 (Complex.exp ((θ : ℂ) * I))) (Icc 0 (2 * Real.pi / 3)) := by
  set y : ℝ → ℝ := fun t => ((u6 (Complex.exp ((t : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω)).im
  have hy_cont : ContinuousOn y (Icc 0 (2 * Real.pi / 3)) := by
    have hexp : ContinuousOn (fun t : ℝ => Complex.exp ((t : ℂ) * I)) (Icc 0 (2 * Real.pi / 3)) := by
      fun_prop
    have hmaps : MapsTo (fun t : ℝ => Complex.exp ((t : ℂ) * I)) (Icc 0 (2 * Real.pi / 3)) (closedBall 0 1) := by
      intro t _; simp [Metric.mem_closedBall, dist_zero_right]
    exact Complex.continuous_im.comp_continuousOn
      (((u6_continuousOn_closedBall.comp hexp hmaps).sub continuousOn_const).mul continuousOn_const)
  have hy_deriv_ne : ∀ t ∈ Ioo 0 (2 * Real.pi / 3), deriv y t ≠ 0 := by
    intro t ht
    have hmem : Complex.exp ((t : ℂ) * I) ∈ Ω0 := exp_I_mem_Ω0 ht.1 ht.2
    have hnorm1 : ‖Complex.exp ((t : ℂ) * I)‖ ≤ 1 := by simp
    have hu_d := u6_hasDerivAt_of_I0_ne_zero (Ω0_subset_Ω hmem) (I0_ne_zero_of_norm_le_one hnorm1)
    have hexp_d : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * I)) (I * Complex.exp ((t : ℂ) * I)) t := by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * I) I t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I
      simpa [mul_comm] using h1.cexp
    have hcomp_d : HasDerivAt (fun s : ℝ => u6 (Complex.exp ((s : ℂ) * I)))
        (I * Complex.exp ((t : ℂ) * I) * deriv u6 (Complex.exp ((t : ℂ) * I))) t := by
      simpa only [Function.comp_def, smul_eq_mul, hu_d.deriv] using hu_d.scomp t hexp_d
    have hv_d : HasDerivAt (fun s : ℝ => (u6 (Complex.exp ((s : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω))
        ((I * Complex.exp ((t : ℂ) * I) * deriv u6 (Complex.exp ((t : ℂ) * I))) * starRingEnd ℂ (1 + ω)) t :=
      (hcomp_d.sub_const _).mul_const _
    have hre_d : HasDerivAt (fun s : ℝ => ((u6 (Complex.exp ((s : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω)).re)
        (((I * Complex.exp ((t : ℂ) * I) * deriv u6 (Complex.exp ((t : ℂ) * I))) * starRingEnd ℂ (1 + ω)).re) t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hv_d
    have him_d : HasDerivAt y
        (((I * Complex.exp ((t : ℂ) * I) * deriv u6 (Complex.exp ((t : ℂ) * I))) * starRingEnd ℂ (1 + ω)).im) t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hv_d
    have hsq_eq : (fun s : ℝ =>
        ((u6 (Complex.exp ((s : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω)).re ^ 2 + y s ^ 2) =ᶠ[𝓝 t]
        fun _ => ‖sideCenter 0‖ ^ 2 - 1 := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      have h1 : ‖(u6 (Complex.exp ((s : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω)‖ ^ 2 =
          ‖sideCenter 0‖ ^ 2 - 1 := by
        rw [norm_mul, RCLike.norm_conj, norm_one_add_ω, mul_one]
        exact u6_arc_on_circle hs.1 hs.2
      rw [Complex.sq_norm, Complex.normSq_apply] at h1
      simpa only [y, sq] using h1
    have hsq_d := ((hre_d.pow 2).add (him_d.pow 2)).unique
      ((hasDerivAt_const t (‖sideCenter 0‖ ^ 2 - 1)).congr_of_eventuallyEq hsq_eq)
    intro hy0
    rw [him_d.deriv] at hy0
    have hx_neg : ((u6 (Complex.exp ((t : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω)).re < 0 := by
      have h1 : ((u6 (Complex.exp ((t : ℂ) * I)) - sideCenter 0) * starRingEnd ℂ (1 + ω)).re =
          (u6 (Complex.exp ((t : ℂ) * I)) * starRingEnd ℂ (1 + ω)).re - (2 + Real.sqrt 3) * R := by
        rw [sub_mul, sub_re]; congr 1
        simp only [sideCenter, Fin.val_zero, pow_zero, one_mul, a0, mul_assoc]
        have hu1 : (1 + ω) * starRingEnd ℂ (1 + ω) = 1 := by
          rw [Complex.mul_conj, ← Complex.sq_norm, norm_one_add_ω]; norm_num
        rw [hu1, mul_one, ofReal_re]
      rw [h1]
      have hle : (u6 (Complex.exp ((t : ℂ) * I)) * starRingEnd ℂ (1 + ω)).re ≤
          ‖u6 (Complex.exp ((t : ℂ) * I)) * starRingEnd ℂ (1 + ω)‖ := Complex.re_le_norm _
      rw [norm_mul, RCLike.norm_conj, norm_one_add_ω, mul_one] at hle
      have hlt1 := norm_u6_lt_one hnorm1
      have hM := one_lt_norm_sideCenter 0; rw [norm_sideCenter] at hM; linarith
    have hx_d0 : (((I * Complex.exp ((t : ℂ) * I) * deriv u6 (Complex.exp ((t : ℂ) * I))) *
        starRingEnd ℂ (1 + ω)).re) = 0 := by
      rw [hy0] at hsq_d
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_zero, add_zero] at hsq_d
      nlinarith only [hsq_d, hx_neg]
    have hv_d0 : (I * Complex.exp ((t : ℂ) * I) * deriv u6 (Complex.exp ((t : ℂ) * I))) *
        starRingEnd ℂ (1 + ω) = 0 := Complex.ext hx_d0 hy0
    have hstar_ne : starRingEnd ℂ (1 + ω) ≠ 0 := by
      intro h; have := congrArg norm h; rw [RCLike.norm_conj, norm_one_add_ω, norm_zero] at this
      norm_num at this
    have hprod0 := (mul_eq_zero.mp hv_d0).resolve_right hstar_ne
    have hu_ne := u6_deriv_ne_zero_of_I0_ne_zero (Ω0_subset_Ω hmem) (I0_ne_zero_of_norm_le_one hnorm1)
    exact hu_ne ((mul_eq_zero.mp hprod0).resolve_left (mul_ne_zero I_ne_zero (Complex.exp_ne_zero _)))
  intro s hs t ht heq
  have hyeq : y s = y t := by simp only [y, heq]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hlt (hy_cont.mono (Icc_subset_Icc hs.1 ht.2)) hyeq
    exact hy_deriv_ne c ⟨lt_of_le_of_lt hs.1 hc.1, lt_of_lt_of_le hc.2 ht.2⟩ hc0
  · obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hgt (hy_cont.mono (Icc_subset_Icc ht.1 hs.2)) hyeq.symm
    exact hy_deriv_ne c ⟨lt_of_le_of_lt ht.1 hc.1, lt_of_lt_of_le hc.2 hs.2⟩ hc0

lemma u6_arc_strict_other_sides {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * Real.pi / 3) :
    ‖sideCenter 1‖ ^ 2 - 1 < ‖u6 (Complex.exp ((θ : ℂ) * I)) - sideCenter 1‖ ^ 2 ∧
    ‖sideCenter 2‖ ^ 2 - 1 < ‖u6 (Complex.exp ((θ : ℂ) * I)) - sideCenter 2‖ ^ 2 := by
  have hfr := u6_arc_mem_frontier h0.le h1.le
  rw [frontier_Δ1Open] at hfr
  have hcirc := u6_arc_on_circle h0 h1
  have hz1 : ‖u6 (Complex.exp ((θ : ℂ) * I))‖ < 1 := hfr.1.1
  constructor
  · refine lt_of_le_of_ne (hfr.1.2 1) fun heq => ?_
    have hv := side0_inter_side1_eq_vert1 hz1 hcirc heq.symm
    have hv_eq : u6 (Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) = vert1 1 := by
      rw [← ω_eq_exp]; conv_lhs => rw [show ω = ω * 1 by ring]
      rw [u6_rot, u6_one]; simp [vert1]
    have hθ_eq := u6_arc_injOn ⟨h0.le, h1.le⟩ (right_mem_Icc.mpr (by positivity)) (hv.trans hv_eq.symm)
    linarith
  · refine lt_of_le_of_ne (hfr.1.2 2) fun heq => ?_
    have hv := (side_inter_side_eq_vert1 (by decide : (2 : Fin 3) ≠ 0) hz1 heq.symm hcirc).2.2 ⟨rfl, rfl⟩
    have hv_eq : u6 (Complex.exp (((0 : ℝ) : ℂ) * I)) = vert1 0 := by simp [u6_one, vert1]
    have hθ_eq := u6_arc_injOn ⟨h0.le, h1.le⟩ (left_mem_Icc.mpr (by positivity)) (hv.trans hv_eq.symm)
    linarith

/-- Decomposition of any point on `sphere 0 1` as `ω^k * exp (i θ)` with `θ ∈ [0, 2π/3)`. -/
lemma sphere_decomp {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) :
    ∃ (k : Fin 3) (θ : ℝ), 0 ≤ θ ∧ θ < 2 * Real.pi / 3 ∧ ζ = ω ^ (k : ℕ) * Complex.exp ((θ : ℂ) * I) := by
  have hnorm : ‖ζ‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hζ
  have hpolar : ζ = Complex.exp ((Complex.arg ζ : ℂ) * I) := by
    have := Complex.norm_mul_exp_arg_mul_I ζ
    rw [hnorm, ofReal_one, one_mul] at this
    exact this.symm
  have hle := Complex.arg_le_pi ζ
  have hgt := Complex.neg_pi_lt_arg ζ
  have h2pi : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by simp [Complex.exp_two_pi_mul_I]
  by_cases h1 : 0 ≤ Complex.arg ζ ∧ Complex.arg ζ < 2 * Real.pi / 3
  · exact ⟨0, Complex.arg ζ, h1.1, h1.2, by simpa using hpolar⟩
  · by_cases h2 : 2 * Real.pi / 3 ≤ Complex.arg ζ
    · refine ⟨1, Complex.arg ζ - 2 * Real.pi / 3, by linarith, by linarith [Real.pi_pos], ?_⟩
      conv_lhs => rw [hpolar]
      simp only [Fin.val_one, pow_one, ω_eq_exp, ← Complex.exp_add]
      congr 1; push_cast; ring
    · push Not at h1 h2
      have hneg : Complex.arg ζ < 0 := by by_contra hge; push Not at hge; exact (h1 hge).not_gt h2
      by_cases h3 : -(2 * Real.pi / 3) ≤ Complex.arg ζ
      · refine ⟨2, Complex.arg ζ + 2 * Real.pi / 3, by linarith, by linarith, ?_⟩
        conv_lhs => rw [hpolar]
        simp only [Fin.val_two, pow_two, ω_eq_exp, ← Complex.exp_add]
        calc Complex.exp ((Complex.arg ζ : ℂ) * I)
            = Complex.exp ((Complex.arg ζ : ℂ) * I) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) := by
                rw [h2pi, mul_one]
          _ = Complex.exp _ := by rw [← Complex.exp_add]; congr 1; push_cast; ring
      · push Not at h3
        refine ⟨1, Complex.arg ζ + 4 * Real.pi / 3, by linarith [Real.pi_pos], by linarith [Real.pi_pos], ?_⟩
        conv_lhs => rw [hpolar]
        simp only [Fin.val_one, pow_one, ω_eq_exp, ← Complex.exp_add]
        calc Complex.exp ((Complex.arg ζ : ℂ) * I)
            = Complex.exp ((Complex.arg ζ : ℂ) * I) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) := by
                rw [h2pi, mul_one]
          _ = Complex.exp _ := by rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma u6_rot_pow (k : ℕ) (ζ : ℂ) : u6 (ω ^ k * ζ) = ω ^ k * u6 ζ := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, u6_rot, ih, mul_assoc]

lemma u3_rot_pow (k : ℕ) (ζ : ℂ) : u3 (ω ^ k * ζ) = ω ^ k * u3 ζ := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, u3_rot, ih, mul_assoc]

lemma sideCenter_rot_eq (k j : Fin 3) (hjk : j ≠ k) :
    ∃ m : Fin 3, (m = 1 ∨ m = 2) ∧ sideCenter j = ω ^ (k : ℕ) * sideCenter m := by
  fin_cases k <;> fin_cases j
  · exact absurd rfl hjk
  · exact ⟨1, Or.inl rfl, by simp [sideCenter]⟩
  · exact ⟨2, Or.inr rfl, by simp [sideCenter]⟩
  · exact ⟨2, Or.inr rfl, by simp only [sideCenter, Fin.val_two, pow_zero, pow_one, one_mul]; linear_combination -a0 * ω_cube⟩
  · exact absurd rfl hjk
  · exact ⟨1, Or.inl rfl, by simp only [sideCenter, Fin.val_one, pow_one]; ring⟩
  · exact ⟨1, Or.inl rfl, by simp only [sideCenter, Fin.val_one, pow_zero, pow_one, one_mul]; linear_combination -a0 * ω_cube⟩
  · exact ⟨2, Or.inr rfl, by simp only [sideCenter, Fin.val_two, pow_one]; linear_combination -ω * a0 * ω_cube⟩
  · exact absurd rfl hjk

lemma u6_injOn_closedBall : InjOn u6 (closedBall 0 1) := by
  -- First show `InjOn u6 (sphere 0 1)`.
  have hsph : InjOn u6 (sphere 0 1) := by
    intro ζ₁ hζ₁ ζ₂ hζ₂ heq
    obtain ⟨k₁, θ₁, h0₁, h1₁, rfl⟩ := sphere_decomp hζ₁
    obtain ⟨k₂, θ₂, h0₂, h1₂, rfl⟩ := sphere_decomp hζ₂
    rw [u6_rot_pow, u6_rot_pow] at heq
    -- Case split on whether `k₁ = k₂`!
    by_cases hk : k₁ = k₂
    · subst hk
      have heq' := mul_left_cancel₀ (pow_ne_zero _ ω_ne_zero) heq
      have hθ := u6_arc_injOn ⟨h0₁, h1₁.le⟩ ⟨h0₂, h1₂.le⟩ heq'
      rw [hθ]
    · -- `k₁ ≠ k₂`: check which sides the two points lie on!
      have hside_of_rot : ∀ (k : Fin 3) (θ : ℝ), 0 ≤ θ → θ < 2 * Real.pi / 3 →
          ‖ω ^ (k : ℕ) * u6 (Complex.exp ((θ : ℂ) * I)) - sideCenter k‖ ^ 2 =
            ‖sideCenter k‖ ^ 2 - 1 := by
        intro k θ h0 h1
        have hc : ‖u6 (Complex.exp ((θ : ℂ) * I)) - sideCenter 0‖ ^ 2 = ‖sideCenter 0‖ ^ 2 - 1 := by
          rcases eq_or_lt_of_le h0 with rfl | h0'
          · simpa [u6_one, vert1] using vert1_zero_on_side0
          · exact u6_arc_on_circle h0' h1
        have ha : sideCenter k = ω ^ (k : ℕ) * sideCenter 0 := by simp [sideCenter]
        rw [ha, ← mul_sub, norm_mul, norm_ω_pow, one_mul, norm_mul, norm_ω_pow, one_mul]
        exact hc
      set z := ω ^ (k₁ : ℕ) * u6 (Complex.exp ((θ₁ : ℂ) * I))
      have hz1 : ‖z‖ < 1 := by
        rw [norm_mul, norm_ω_pow, one_mul]
        exact norm_u6_lt_one (by simp)
      have hs1 : ‖z - sideCenter k₁‖ ^ 2 = ‖sideCenter k₁‖ ^ 2 - 1 := hside_of_rot k₁ θ₁ h0₁ h1₁
      have hs2 : ‖z - sideCenter k₂‖ ^ 2 = ‖sideCenter k₂‖ ^ 2 - 1 := by
        rw [heq]; exact hside_of_rot k₂ θ₂ h0₂ h1₂
      -- Hence `z` is a vertex of `Δ1`!
      -- Any `z = ω^k * u6(e^(iθ))` with `0 < θ < 2π/3` is STRICT on the other two sides!
      have hnot_pos : ∀ (k : Fin 3) (θ : ℝ), 0 < θ → θ < 2 * Real.pi / 3 →
          ∀ j : Fin 3, j ≠ k →
            ‖sideCenter j‖ ^ 2 - 1 < ‖ω ^ (k : ℕ) * u6 (Complex.exp ((θ : ℂ) * I)) - sideCenter j‖ ^ 2 := by
        intro k θ h0 h1 j hjk
        have hstr := u6_arc_strict_other_sides h0 h1
        obtain ⟨m, hm12, hsc⟩ := sideCenter_rot_eq k j hjk
        rw [hsc, ← mul_sub, norm_mul, norm_ω_pow, one_mul, norm_mul, norm_ω_pow, one_mul]
        rcases hm12 with rfl | rfl
        · exact hstr.1
        · exact hstr.2
      have hθ1_zero : θ₁ = 0 := by
        rcases eq_or_lt_of_le h0₁ with rfl | hpos
        · rfl
        · exfalso; exact (hnot_pos k₁ θ₁ hpos h1₁ k₂ (Ne.symm hk)).ne hs2.symm
      have hθ2_zero : θ₂ = 0 := by
        rcases eq_or_lt_of_le h0₂ with rfl | hpos
        · rfl
        · exfalso
          have := hnot_pos k₂ θ₂ hpos h1₂ k₁ hk
          rw [← heq] at this; exact this.ne hs1.symm
      subst hθ1_zero; subst hθ2_zero
      simp only [z, ofReal_zero, zero_mul, Complex.exp_zero, u6_one] at heq
      have hpow_eq : ω ^ (k₁ : ℕ) = ω ^ (k₂ : ℕ) :=
        mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr R_ne_zero) heq
      exfalso; apply hk
      fin_cases k₁ <;> fin_cases k₂
      all_goals first | rfl | (
        simp only [pow_zero, pow_one, ω_sq] at hpow_eq
        have him := congrArg Complex.im hpow_eq
        have hre := congrArg Complex.re hpow_eq
        simp only [one_re, one_im, ω_re, ω_im] at hre him
        linarith [sqrt3_pos])
  -- Now combine `ball 0 1` and `sphere 0 1`!
  intro ζ₁ hζ₁ ζ₂ hζ₂ heq
  by_cases hb1 : ζ₁ ∈ ball (0 : ℂ) 1
  · by_cases hb2 : ζ₂ ∈ ball (0 : ℂ) 1
    · have hu := u6_biholo.2 (u6 ζ₁) (u6_biholo.1 hb1)
      exact (hu.unique ⟨hb1, rfl⟩ ⟨hb2, heq.symm⟩)
    · exfalso
      have hs2 : ζ₂ ∈ sphere (0 : ℂ) 1 := by
        rw [Metric.mem_sphere]; rw [Metric.mem_closedBall] at hζ₂; rw [Metric.mem_ball] at hb2; linarith
      have hfr := u6_maps_sphere_to_frontier hs2
      rw [frontier_Δ1Open, ← heq] at hfr
      exact hfr.2 (u6_biholo.1 hb1)
  · have hs1 : ζ₁ ∈ sphere (0 : ℂ) 1 := by
      rw [Metric.mem_sphere]; rw [Metric.mem_closedBall] at hζ₁; rw [Metric.mem_ball] at hb1; linarith
    by_cases hb2 : ζ₂ ∈ ball (0 : ℂ) 1
    · exfalso
      have hfr := u6_maps_sphere_to_frontier hs1
      rw [frontier_Δ1Open, heq] at hfr
      exact hfr.2 (u6_biholo.1 hb2)
    · have hs2 : ζ₂ ∈ sphere (0 : ℂ) 1 := by
        rw [Metric.mem_sphere]; rw [Metric.mem_closedBall] at hζ₂; rw [Metric.mem_ball] at hb2; linarith
      exact hsph hs1 hs2 heq

lemma u6_image_closedBall : u6 '' closedBall 0 1 = Δ1 := by
  apply Subset.antisymm
  · rintro _ ⟨ζ, hζ, rfl⟩
    by_cases hb : ζ ∈ ball (0 : ℂ) 1
    · have h := u6_biholo.1 hb; exact ⟨h.1, fun j => (h.2 j).le⟩
    · have hs : ζ ∈ sphere (0 : ℂ) 1 := by
        rw [Metric.mem_sphere]; rw [Metric.mem_closedBall] at hζ; rw [Metric.mem_ball] at hb; linarith
      have hfr := u6_maps_sphere_to_frontier hs
      rw [frontier_Δ1Open] at hfr; exact hfr.1
  · rw [← closure_Δ1Open]
    have hcl : IsClosed (u6 '' closedBall 0 1) :=
      ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn u6_continuousOn_closedBall).isClosed
    refine hcl.closure_subset_iff.mpr fun z hz => ?_
    obtain ⟨ζ, ⟨hζ, rfl⟩, _⟩ := u6_biholo.2 z hz
    exact ⟨ζ, ball_subset_closedBall hζ, rfl⟩

/-- Global inverse of `u6` on `Δ1`. -/
def u6Inv (z : ℂ) : ℂ := Function.invFunOn u6 (closedBall 0 1) z

lemma u6Inv_mem_closedBall {z : ℂ} (hz : z ∈ Δ1) : u6Inv z ∈ closedBall 0 1 := by
  rw [← u6_image_closedBall] at hz
  exact Function.invFunOn_mem hz

lemma u6_u6Inv {z : ℂ} (hz : z ∈ Δ1) : u6 (u6Inv z) = z := by
  rw [← u6_image_closedBall] at hz
  exact Function.invFunOn_eq hz

lemma u6Inv_u6 {ζ : ℂ} (hζ : ζ ∈ closedBall 0 1) : u6Inv (u6 ζ) = ζ := by
  have hz : u6 ζ ∈ Δ1 := u6_image_closedBall ▸ ⟨ζ, hζ, rfl⟩
  exact u6_injOn_closedBall (u6Inv_mem_closedBall hz) hζ (u6_u6Inv hz)

lemma u6Inv_mem_ball {z : ℂ} (hz : z ∈ Δ1Open) : u6Inv z ∈ ball 0 1 := by
  have hz1 : z ∈ Δ1 := ⟨hz.1, fun j => (hz.2 j).le⟩
  obtain ⟨ζ, ⟨hζ, hgz⟩, _⟩ := u6_biholo.2 z hz
  have heq : u6Inv z = ζ := by rw [← hgz, u6Inv_u6 (ball_subset_closedBall hζ)]
  rwa [heq]

lemma u6Inv_zero : u6Inv 0 = 0 := by
  conv_lhs => rw [← u6_zero]
  exact u6Inv_u6 (Metric.mem_closedBall_self zero_le_one)

lemma u6Inv_vert (k : Fin 3) : u6Inv (vert1 k) = ω ^ (k : ℕ) := by
  have hv : u6 (ω ^ (k : ℕ)) = vert1 k := by
    rw [show ω ^ (k : ℕ) = ω ^ (k : ℕ) * 1 by ring, u6_rot_pow, u6_one]; rfl
  rw [← hv]
  exact u6Inv_u6 (by simp [Metric.mem_closedBall, dist_zero_right, norm_ω])

lemma u6Inv_rot {z : ℂ} (hz : z ∈ Δ1) : u6Inv (ω * z) = ω * u6Inv z := by
  have hmem : ω * u6Inv z ∈ closedBall 0 1 := by
    have h := u6Inv_mem_closedBall hz
    simpa [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_ω] using h
  rw [← u6Inv_u6 hmem, u6_rot, u6_u6Inv hz]

lemma u6Inv_continuousOn : ContinuousOn u6Inv Δ1 := by
  rw [continuousOn_iff_continuous_domRestrict]
  -- `u6` restricted to compact `closedBall 0 1` -> `Δ1` is a continuous bijection to Hausdorff `Δ1`!
  let f : closedBall (0 : ℂ) 1 → Δ1 := fun ζ => ⟨u6 ζ.1, u6_image_closedBall ▸ ⟨ζ.1, ζ.2, rfl⟩⟩
  have hf_cont : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact continuousOn_iff_continuous_domRestrict.mp u6_continuousOn_closedBall
  have hf_bij : Function.Bijective f := by
    constructor
    · intro a b hab
      exact Subtype.ext (u6_injOn_closedBall a.2 b.2 (congrArg Subtype.val hab))
    · intro z
      exact ⟨⟨u6Inv z.1, u6Inv_mem_closedBall z.2⟩, Subtype.ext (u6_u6Inv z.2)⟩
  have : CompactSpace (closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  let h := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf_bij) hf_cont
  have hinv_eq : (Δ1.domRestrict u6Inv) = fun z => (h.symm z).1 := by
    ext z
    have h1 : f (h.symm z) = z := h.apply_symm_apply z
    have h2 : u6 (h.symm z).1 = z.1 := congrArg Subtype.val h1
    rw [domRestrict_apply, ← h2, u6Inv_u6 (h.symm z).2]
  rw [hinv_eq]
  exact continuous_subtype_val.comp h.symm.continuous

lemma u6Inv_hasDerivAt {z : ℂ} (hz : z ∈ Δ1Open) :
    HasDerivAt u6Inv (deriv u6 (u6Inv z))⁻¹ z := by
  set ζ := u6Inv z
  have hζ : ζ ∈ ball (0 : ℂ) 1 := u6Inv_mem_ball hz
  have hsd := differentiableOn_hasStrictDerivAt isOpen_ball u6_differentiableOn_ball hζ
  have hdne := u6_deriv_ne_zero_of_I0_ne_zero (ball_subset_Ω hζ)
    (I0_ne_zero_of_norm_le_one (le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hζ)))
  have hleft : ∀ᶠ w in 𝓝 ζ, u6Inv (u6 w) = w := by
    filter_upwards [isOpen_ball.mem_nhds hζ] with w hw
    exact u6Inv_u6 (ball_subset_closedBall hw)
  have hinv := hsd.to_local_left_inverse hdne hleft
  rw [u6_u6Inv ⟨hz.1, fun j => (hz.2 j).le⟩] at hinv
  exact hinv.hasDerivAt

lemma u6Inv_differentiableOn : DifferentiableOn ℂ u6Inv Δ1Open := fun _ hz =>
  (u6Inv_hasDerivAt hz).differentiableAt.differentiableWithinAt

/-- Conformal map `φ := u3 ∘ u6Inv : Δ1 → Δ2`. -/
def φ (z : ℂ) : ℂ := u3 (u6Inv z)

lemma φ_continuousOn : ContinuousOn φ Δ1 :=
  u3_continuousOn_closedBall.comp u6Inv_continuousOn (fun _ hz => u6Inv_mem_closedBall hz)

lemma φ_differentiableOn : DifferentiableOn ℂ φ Δ1Open :=
  (u3_differentiableOn_Ω.mono ball_subset_Ω).comp u6Inv_differentiableOn (fun _ hz => u6Inv_mem_ball hz)

lemma φ_zero : φ 0 = 0 := by simp [φ, u6Inv_zero, u3_zero]

lemma deriv_φ_zero : deriv φ 0 = 1 := by
  have h1 : HasDerivAt u6Inv (deriv u6 0)⁻¹ 0 := by
    have := u6Inv_hasDerivAt zero_mem_Δ1Open
    rwa [u6Inv_zero] at this
  have h2 : HasDerivAt u3 (deriv u3 0) (u6Inv 0) := by
    rw [u6Inv_zero]
    exact ((u3_differentiableOn_Ω.mono ball_subset_Ω).differentiableAt
      (isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))).hasDerivAt
  have hcomp : HasDerivAt φ (deriv u3 0 * (deriv u6 0)⁻¹) 0 := by
    have hc : HasDerivAt (fun x => u3 (u6Inv x)) (deriv u3 0 * (deriv u6 0)⁻¹) 0 := h2.comp (0 : ℂ) h1
    exact hc
  rw [hcomp.deriv, deriv_u3_zero, deriv_u6_zero]
  have hne : ((R / w6_1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (div_ne_zero R_ne_zero w6_1_pos.ne')
  exact mul_inv_cancel₀ hne

lemma φ_mapsTo : MapsTo φ Δ1 Δ2 := by
  intro z hz
  have hζ := u6Inv_mem_closedBall hz
  by_cases hb : u6Inv z ∈ ball (0 : ℂ) 1
  · exact fun j => (u3_biholo.1 hb j).le
  · have hs : u6Inv z ∈ sphere (0 : ℂ) 1 := by
      rw [Metric.mem_sphere]; rw [Metric.mem_closedBall] at hζ; rw [Metric.mem_ball] at hb; linarith
    have hfr := u3_maps_sphere_to_frontier hs
    rw [frontier_Δ2Open] at hfr; exact hfr.1

lemma φ_vert (k : Fin 3) : φ (vert1 k) = vert2 k := by
  simp only [φ, u6Inv_vert]
  rw [show ω ^ (k : ℕ) = ω ^ (k : ℕ) * 1 by ring, u3_rot_pow, u3_one]; rfl

lemma φ_rot {z : ℂ} (hz : z ∈ Δ1) : φ (ω * z) = ω * φ z := by
  simp only [φ, u6Inv_rot hz, u3_rot]

/-- On `closedBall 0 1`, `u3 ζ = vert2 k` if and only if `ζ = ω^k`. -/
lemma u3_eq_vert2_iff {ζ : ℂ} (hζ : ζ ∈ closedBall (0 : ℂ) 1) (k : Fin 3) :
    u3 ζ = vert2 k ↔ ζ = ω ^ (k : ℕ) := by
  constructor
  · intro heq
    -- Reduce to `k = 0` by rotating by `ω^(3 - k)`.
    suffices h0 : ∀ ξ ∈ closedBall (0 : ℂ) 1, u3 ξ = (cAG : ℂ) → ξ = 1 by
      set m : ℕ := (3 - k.val) % 3
      have hm : ω ^ m * ω ^ (k : ℕ) = 1 := by
        fin_cases k
        · simp [m]
        · simp only [m, Nat.reduceSub, Nat.reduceMod]; rw [← pow_add]; exact ω_cube
        · simp only [m, Nat.reduceSub, Nat.reduceMod]; rw [← pow_add]; exact ω_cube
      have hξ_mem : ω ^ m * ζ ∈ closedBall (0 : ℂ) 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_ω] using hζ
      have hξ_val : u3 (ω ^ m * ζ) = (cAG : ℂ) := by
        rw [u3_rot_pow, heq]; unfold vert2; rw [← mul_assoc, hm, one_mul]
      have hξ1 := h0 _ hξ_mem hξ_val
      have := congrArg (ω ^ (k : ℕ) * ·) hξ1
      rw [← mul_assoc, mul_comm (ω ^ (k : ℕ)), hm, one_mul, mul_one] at this
      exact this
    intro ξ hξ hval
    have hs : ξ ∈ sphere (0 : ℂ) 1 := by
      by_contra hns
      have hb : ξ ∈ ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hξ; rw [Metric.mem_sphere] at hns
        exact lt_of_le_of_ne hξ hns
      have hopen := u3_biholo.1 hb 1
      rw [hval, Fin.val_one, pow_one, mul_re, ω_re, ω_im, ofReal_re, ofReal_im, mul_zero, sub_zero] at hopen
      linarith
    obtain ⟨j, θ, h0, h1, rfl⟩ := sphere_decomp hs
    rw [u3_rot_pow] at hval
    -- `h(t) = (ω * u3(e^(i t))).im` is strictly decreasing on `[0, 2π/3]` from `+cAG √3/2` to `-cAG √3/2`,
    -- and `(ω * u3(e^(i t))).re = -cAG/2`!
    have hre := u3_arc_re_eq h0 h1.le
    fin_cases j
    · simp only [pow_zero, one_mul] at hval ⊢
      -- `u3 (exp (i θ)) = cAG`: show `θ = 0` using strict decrease of `h(t) = (ω * u3(e^(it))).im`!
      by_contra hne
      have hθ_pos : 0 < θ := lt_of_le_of_ne h0 fun h0' => hne (by rw [← h0']; simp)
      set h : ℝ → ℝ := fun t => (ω * u3 (Complex.exp ((t : ℂ) * I))).im
      have hh_cont : ContinuousOn h (Icc 0 θ) := by
        have hexp : ContinuousOn (fun t : ℝ => Complex.exp ((t : ℂ) * I)) (Icc 0 θ) := by fun_prop
        have hmaps : MapsTo (fun t : ℝ => Complex.exp ((t : ℂ) * I)) (Icc 0 θ) (closedBall 0 1) := by
          intro t _; simp [Metric.mem_closedBall, dist_zero_right]
        exact Complex.continuous_im.comp_continuousOn
          (continuousOn_const.mul (u3_continuousOn_closedBall.comp hexp hmaps))
      have hh_eq : h 0 = h θ := by simp [h, u3_one, hval]
      obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hθ_pos hh_cont hh_eq
      have hcd : HasDerivAt h
          ((-(((R / w6_1 * (2 * Real.sin (3 * c / 2)) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) * I).im) c :=
        Complex.imCLM.hasFDerivAt.comp_hasDerivAt c (u3_arc_deriv hc.1 (lt_trans hc.2 h1))
      rw [hcd.deriv] at hc0
      have hpos_sin : 0 < Real.sin (3 * c / 2) :=
        Real.sin_pos_of_pos_of_lt_pi (x := 3 * c / 2) (by linarith [hc.1]) (by linarith [hc.2, h1])
      have hpow_pos : 0 < (2 * Real.sin (3 * c / 2)) ^ (-(2 / 3 : ℝ)) :=
        Real.rpow_pos_of_pos (by linarith) _
      have hneg : -(R / w6_1 * (2 * Real.sin (3 * c / 2)) ^ (-(2 / 3 : ℝ))) < 0 := by
        have := div_pos R_pos w6_1_pos; nlinarith
      simp only [mul_im, neg_re, neg_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero,
        add_zero] at hc0
      linarith
    · -- `j = 1`: `ω * u3 (e^(i θ)) = cAG`, so `(ω * u3 (e^(i θ))).re = cAG ≠ -cAG/2`!
      simp only [pow_one] at hval
      rw [hval, ofReal_re] at hre
      linarith [cAG_pos]
    · -- `j = 2`: `ω^2 * u3 (e^(i θ)) = cAG ⟹ ω * u3 (e^(i θ)) = ω^2 * cAG`, so `h θ = -cAG √3/2 = h(2π/3)`!
      exfalso
      have hval' : ω ^ 2 * u3 (Complex.exp ((θ : ℂ) * I)) = (cAG : ℂ) := hval
      have hω_val : ω * u3 (Complex.exp ((θ : ℂ) * I)) = ω ^ 2 * (cAG : ℂ) := by
        have := congrArg (ω ^ 2 * ·) hval'
        linear_combination this - ω * u3 (Complex.exp ((θ : ℂ) * I)) * ω_cube
      set h : ℝ → ℝ := fun t => (ω * u3 (Complex.exp ((t : ℂ) * I))).im
      have hh_cont : ContinuousOn h (Icc θ (2 * Real.pi / 3)) := by
        have hexp : ContinuousOn (fun t : ℝ => Complex.exp ((t : ℂ) * I)) (Icc θ (2 * Real.pi / 3)) := by
          fun_prop
        have hmaps : MapsTo (fun t : ℝ => Complex.exp ((t : ℂ) * I)) (Icc θ (2 * Real.pi / 3)) (closedBall 0 1) := by
          intro t _; simp [Metric.mem_closedBall, dist_zero_right]
        exact Complex.continuous_im.comp_continuousOn
          (continuousOn_const.mul (u3_continuousOn_closedBall.comp hexp hmaps))
      have hh23 : h (2 * Real.pi / 3) = h θ := by
        have hu_ω : u3 (Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) = ω * (cAG : ℂ) := by
          rw [← ω_eq_exp]; conv_lhs => rw [show ω = ω * 1 by ring]; rw [u3_rot, u3_one]
        simp only [h, hu_ω, hω_val, ← mul_assoc, ← pow_two]
      obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero h1 hh_cont hh23.symm
      have hcd : HasDerivAt h
          ((-(((R / w6_1 * (2 * Real.sin (3 * c / 2)) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) * I).im) c :=
        Complex.imCLM.hasFDerivAt.comp_hasDerivAt c (u3_arc_deriv (lt_of_le_of_lt h0 hc.1) hc.2)
      rw [hcd.deriv] at hc0
      have hpos_sin : 0 < Real.sin (3 * c / 2) :=
        Real.sin_pos_of_pos_of_lt_pi (x := 3 * c / 2) (by linarith [h0, hc.1]) (by linarith [hc.2])
      have hpow_pos : 0 < (2 * Real.sin (3 * c / 2)) ^ (-(2 / 3 : ℝ)) :=
        Real.rpow_pos_of_pos (by linarith) _
      have hneg : -(R / w6_1 * (2 * Real.sin (3 * c / 2)) ^ (-(2 / 3 : ℝ))) < 0 := by
        have := div_pos R_pos w6_1_pos; nlinarith
      simp only [mul_im, neg_re, neg_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero,
        add_zero] at hc0
      linarith
  · rintro rfl
    rw [show ω ^ (k : ℕ) = ω ^ (k : ℕ) * 1 by ring, u3_rot_pow, u3_one]; rfl

lemma φ_eq_vert2_iff {z : ℂ} (hz : z ∈ Δ1) (k : Fin 3) :
    φ z = vert2 k ↔ z = vert1 k := by
  constructor
  · intro h
    have hζ := (u3_eq_vert2_iff (u6Inv_mem_closedBall hz) k).mp h
    rw [← u6_u6Inv hz, hζ, show ω ^ (k : ℕ) = ω ^ (k : ℕ) * 1 by ring, u6_rot_pow, u6_one]; rfl
  · rintro rfl; exact φ_vert k

/- ## 3. Reflection Words (`hypWord`, `eucWord`) and Holomorphic Chart Conjugation -/

def hypWord : List (Fin 3) → ℂ → ℂ
  | [], z => z
  | j :: js, z => hypRefl j (hypWord js z)

def eucWord : List (Fin 3) → ℂ → ℂ
  | [], w => w
  | j :: js, w => eucRefl j (eucWord js w)

@[simp] lemma hypWord_nil (z : ℂ) : hypWord [] z = z := rfl
@[simp] lemma hypWord_cons (j : Fin 3) (js : List (Fin 3)) (z : ℂ) :
    hypWord (j :: js) z = hypRefl j (hypWord js z) := rfl
@[simp] lemma eucWord_nil (w : ℂ) : eucWord [] w = w := rfl
@[simp] lemma eucWord_cons (j : Fin 3) (js : List (Fin 3)) (w : ℂ) :
    eucWord (j :: js) w = eucRefl j (eucWord js w) := rfl

lemma hypWord_append (u v : List (Fin 3)) (z : ℂ) :
    hypWord (u ++ v) z = hypWord u (hypWord v z) := by
  induction u with
  | nil => rfl
  | cons j js ih => simp [ih]

lemma eucWord_append (u v : List (Fin 3)) (w : ℂ) :
    eucWord (u ++ v) w = eucWord u (eucWord v w) := by
  induction u with
  | nil => rfl
  | cons j js ih => simp [ih]

lemma hypWord_mem_ball (w : List (Fin 3)) {z : ℂ} (hz : ‖z‖ < 1) : ‖hypWord w z‖ < 1 := by
  induction w with
  | nil => exact hz
  | cons j js ih => exact hypRefl_mem_ball j ih

lemma hypWord_reverse_left (w : List (Fin 3)) {z : ℂ} (hz : ‖z‖ < 1) :
    hypWord w.reverse (hypWord w z) = z := by
  induction w with
  | nil => rfl
  | cons j js ih =>
    rw [List.reverse_cons, hypWord_append, hypWord_cons]
    simp only [hypWord_cons, hypWord_nil]
    rw [hypRefl_invol j (hypWord_mem_ball js hz), ih]

lemma hypWord_reverse_right (w : List (Fin 3)) {z : ℂ} (hz : ‖z‖ < 1) :
    hypWord w (hypWord w.reverse z) = z := by
  simpa only [List.reverse_reverse] using hypWord_reverse_left w.reverse hz

lemma eucWord_reverse_left (w : List (Fin 3)) (z : ℂ) :
    eucWord w.reverse (eucWord w z) = z := by
  induction w with
  | nil => rfl
  | cons j js ih =>
    rw [List.reverse_cons, eucWord_append, eucWord_cons]
    simp only [eucWord_cons, eucWord_nil, eucRefl_invol, ih]

lemma eucWord_reverse_right (w : List (Fin 3)) (z : ℂ) :
    eucWord w (eucWord w.reverse z) = z := by
  simpa only [List.reverse_reverse] using eucWord_reverse_left w.reverse z

lemma hypDist_hypWord (w : List (Fin 3)) {z₁ z₂ : ℂ} (h1 : ‖z₁‖ < 1) (h2 : ‖z₂‖ < 1) :
    hypDist (hypWord w z₁) (hypWord w z₂) = hypDist z₁ z₂ := by
  induction w with
  | nil => rfl
  | cons j js ih =>
    simp only [hypWord_cons]
    rw [hypDist_hypRefl j (hypWord_mem_ball js h1) (hypWord_mem_ball js h2), ih]

lemma eucWord_preserves_lattice (w : List (Fin 3)) {z : ℂ} (hz : z ∈ targetLattice) :
    eucWord w z ∈ targetLattice := by
  induction w with
  | nil => exact hz
  | cons j js ih => exact eucRefl_preserves_lattice j ih

lemma continuousOn_hypRefl (j : Fin 3) : ContinuousOn (hypRefl j) (ball 0 1) := by
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  refine ContinuousAt.continuousWithinAt ?_
  unfold hypRefl
  exact ((continuousAt_const.mul Complex.continuous_conj.continuousAt).sub continuousAt_const).div
    (Complex.continuous_conj.continuousAt.sub continuousAt_const)
    (conj_sub_conj_sideCenter_ne_zero j hz1)

lemma continuousOn_hypWord (w : List (Fin 3)) : ContinuousOn (hypWord w) (ball 0 1) := by
  induction w with
  | nil => exact continuousOn_id
  | cons j js ih =>
    refine (continuousOn_hypRefl j).comp ih fun z hz => ?_
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    exact hypWord_mem_ball js hz

lemma continuous_eucRefl (j : Fin 3) : Continuous (eucRefl j) := by
  fin_cases j <;> unfold eucRefl <;> fun_prop

lemma continuous_eucWord (w : List (Fin 3)) : Continuous (eucWord w) := by
  induction w with
  | nil => exact continuous_id
  | cons j js ih => exact (continuous_eucRefl j).comp ih

/-- Rotate every reflection index in a word by `m` modulo 3. -/
def rotWord (m : ℕ) (w : List (Fin 3)) : List (Fin 3) :=
  w.map fun j => ⟨(j.val + m) % 3, Nat.mod_lt _ (by norm_num)⟩

lemma hypWord_rotWord1 (w : List (Fin 3)) (z : ℂ) :
    hypWord (rotWord 1 w) (ω * z) = ω * hypWord w z := by
  induction w with
  | nil => rfl
  | cons j js ih =>
    change hypRefl ⟨(j.val + 1) % 3, Nat.mod_lt _ (by norm_num)⟩ (hypWord (rotWord 1 js) (ω * z)) =
      ω * hypRefl j (hypWord js z)
    rw [ih, hypRefl_rot]

lemma eucWord_rotWord1 (w : List (Fin 3)) (z : ℂ) :
    eucWord (rotWord 1 w) (ω * z) = ω * eucWord w z := by
  induction w with
  | nil => rfl
  | cons j js ih =>
    change eucRefl ⟨(j.val + 1) % 3, Nat.mod_lt _ (by norm_num)⟩ (eucWord (rotWord 1 js) (ω * z)) =
      ω * eucRefl j (eucWord js z)
    rw [ih, eucRefl_rot]

lemma rotWord_reverse (m : ℕ) (w : List (Fin 3)) :
    (rotWord m w).reverse = rotWord m w.reverse := by
  simp [rotWord, List.map_reverse]

/-- Conjugated chart map `eucWord w ∘ f ∘ hypWord w.reverse`. -/
def chartMap (w : List (Fin 3)) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  eucWord w (f (hypWord w.reverse z))

lemma chartMap_nil (f : ℂ → ℂ) (z : ℂ) : chartMap [] f z = f z := rfl

lemma chartMap_cons (j : Fin 3) (js : List (Fin 3)) (f : ℂ → ℂ) (z : ℂ) :
    chartMap (j :: js) f z = eucRefl j (chartMap js f (hypRefl j z)) := by
  simp only [chartMap, eucWord_cons, List.reverse_cons, hypWord_append, hypWord_cons, hypWord_nil]

lemma chartMap_append (u v : List (Fin 3)) (f : ℂ → ℂ) (z : ℂ) :
    chartMap (u ++ v) f z = chartMap u (chartMap v f) z := by
  simp only [chartMap, eucWord_append, List.reverse_append, hypWord_append]

lemma hasDerivAt_refl_conj (j : Fin 3) {f : ℂ → ℂ} {f' z : ℂ} (hz : ‖z‖ < 1)
    (hf : HasDerivAt f f' (hypRefl j z)) :
    ∃ c : ℂ, c ≠ 0 ∧
      HasDerivAt (fun x => eucRefl j (f (hypRefl j x))) (c * starRingEnd ℂ f') z := by
  set a := sideCenter j
  have ha_sq_ne : (‖a‖ ^ 2 - 1 : ℝ) ≠ 0 := (sideCenter_sq_sub_one_pos j).ne'
  have hden : z - a ≠ 0 := by
    intro h; have := congrArg (starRingEnd ℂ) h
    simp only [map_sub, map_zero] at this
    exact conj_sub_conj_sideCenter_ne_zero j hz this
  let M : ℂ → ℂ := fun x => (starRingEnd ℂ a * x - 1) / (x - a)
  have hM_conj : ∀ x : ℂ, hypRefl j x = starRingEnd ℂ (M x) := by
    intro x; unfold hypRefl M
    simp only [a, map_div₀, map_sub, map_mul, map_one, RingHomCompTriple.comp_apply, RingHom.id_apply]
  have hM_deriv : HasDerivAt M ((1 - a * starRingEnd ℂ a) / (z - a) ^ 2) z := by
    have hnum : HasDerivAt (fun x => starRingEnd ℂ a * x - 1) (starRingEnd ℂ a) z := by
      simpa using ((hasDerivAt_id z).const_mul (starRingEnd ℂ a)).sub_const 1
    have hden_d : HasDerivAt (fun x => x - a) 1 z := (hasDerivAt_id z).sub_const a
    refine (hnum.div hden_d hden).congr_deriv ?_
    ring
  have hM_dne : (1 - a * starRingEnd ℂ a) / (z - a) ^ 2 ≠ 0 := by
    refine div_ne_zero ?_ (pow_ne_zero 2 hden)
    rw [Complex.mul_conj, ← Complex.sq_norm]
    exact_mod_cast (by linarith [sideCenter_sq_sub_one_pos j] : (1 : ℝ) - ‖a‖ ^ 2 ≠ 0)
  have hf_conj : HasDerivAt (fun w => starRingEnd ℂ (f (starRingEnd ℂ w))) (starRingEnd ℂ f') (M z) :=
    hasDerivAt_conj_comp_conj (by rwa [← hM_conj z])
  have hcomp : HasDerivAt (fun x => starRingEnd ℂ (f (hypRefl j x)))
      (starRingEnd ℂ f' * ((1 - a * starRingEnd ℂ a) / (z - a) ^ 2)) z := by
    have h1 := hf_conj.comp z hM_deriv
    simpa only [Function.comp_def, ← hM_conj] using h1
  fin_cases j
  · refine ⟨(-ω) * ((1 - a * starRingEnd ℂ a) / (z - a) ^ 2),
      mul_ne_zero (neg_ne_zero.mpr ω_ne_zero) hM_dne, ?_⟩
    simpa only [eucRefl, mul_assoc, mul_left_comm] using
      ((hcomp.const_mul (-ω)).add_const ((cAG : ℂ) * (1 + ω))).congr_deriv (by ring)
  · refine ⟨(-1) * ((1 - a * starRingEnd ℂ a) / (z - a) ^ 2),
      mul_ne_zero (by norm_num) hM_dne, ?_⟩
    simpa only [eucRefl, neg_one_mul] using
      ((hcomp.const_mul (-1 : ℂ)).sub_const (cAG : ℂ)).congr_deriv (by ring)
  · refine ⟨(-(ω ^ 2)) * ((1 - a * starRingEnd ℂ a) / (z - a) ^ 2),
      mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 ω_ne_zero)) hM_dne, ?_⟩
    simpa only [eucRefl, mul_assoc, mul_left_comm] using
      ((hcomp.const_mul (-(ω ^ 2))).add_const ((cAG : ℂ) * (1 + ω ^ 2))).congr_deriv (by ring)

lemma chartMap_differentiableAt (w : List (Fin 3)) {f : ℂ → ℂ} {z : ℂ} (hz : ‖z‖ < 1)
    (hf : DifferentiableAt ℂ f (hypWord w.reverse z)) :
    DifferentiableAt ℂ (chartMap w f) z := by
  induction w generalizing z with
  | nil => exact hf
  | cons j js ih =>
    have hrz : ‖hypRefl j z‖ < 1 := hypRefl_mem_ball j hz
    have hsub : DifferentiableAt ℂ (chartMap js f) (hypRefl j z) := by
      apply ih hrz
      simpa only [List.reverse_cons, hypWord_append, hypWord_cons, hypWord_nil] using hf
    obtain ⟨_, _, hd⟩ := hasDerivAt_refl_conj j hz hsub.hasDerivAt
    have heq : chartMap (j :: js) f = fun x => eucRefl j (chartMap js f (hypRefl j x)) := by
      ext x; exact chartMap_cons j js f x
    rw [heq]; exact hd.differentiableAt

lemma chartMap_deriv_eq_zero_iff (w : List (Fin 3)) {f : ℂ → ℂ} {z : ℂ} (hz : ‖z‖ < 1)
    (hf : DifferentiableAt ℂ f (hypWord w.reverse z)) :
    deriv (chartMap w f) z = 0 ↔ deriv f (hypWord w.reverse z) = 0 := by
  induction w generalizing z with
  | nil => rfl
  | cons j js ih =>
    have hrz : ‖hypRefl j z‖ < 1 := hypRefl_mem_ball j hz
    have hf' : DifferentiableAt ℂ f (hypWord js.reverse (hypRefl j z)) := by
      simpa only [List.reverse_cons, hypWord_append, hypWord_cons, hypWord_nil] using hf
    have hsub := chartMap_differentiableAt js hrz hf'
    obtain ⟨c, hc, hd⟩ := hasDerivAt_refl_conj j hz hsub.hasDerivAt
    have heq : chartMap (j :: js) f = fun x => eucRefl j (chartMap js f (hypRefl j x)) := by
      ext x; exact chartMap_cons j js f x
    rw [heq, hd.deriv, mul_eq_zero]
    simp only [hc, false_or, map_eq_zero]
    rw [ih hrz hf']
    simp only [List.reverse_cons, hypWord_append, hypWord_cons, hypWord_nil]

/- ## 4. Local Holomorphic Extension Across Open Sides -/

/-- Side reflection laws rotated to side `j`. -/
lemma u6_reflection_law_side (j : Fin 3) {ζ : ℂ} (hζ : ω ^ ((3 - j.val) % 3) * ζ ∈ Ω0)
    (hI0 : I0 ζ ≠ 0) (hI0' : I0 (1 / starRingEnd ℂ ζ) ≠ 0) :
    u6 (1 / starRingEnd ℂ ζ) = hypRefl j (u6 ζ) := by
  set m : ℕ := (3 - j.val) % 3
  set ξ := ω ^ m * ζ
  have hI0_ξ : I0 ξ ≠ 0 := by
    have h3 : ξ ^ 3 = ζ ^ 3 := by
      dsimp only [ξ]
      rw [mul_pow, ← pow_mul, mul_comm m 3, pow_mul, ω_cube, one_pow, one_mul]
    unfold I0; rwa [h3]
  have hinv_ξ : 1 / starRingEnd ℂ ξ = ω ^ m * (1 / starRingEnd ℂ ζ) := by
    have hstar : starRingEnd ℂ (ω ^ m) * ω ^ m = 1 := by
      rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm, norm_ω_pow]; norm_num
    simp only [ξ, map_mul, one_div, mul_inv, mul_comm (ω ^ m)]
    congr 1
    exact inv_eq_of_mul_eq_one_right hstar
  have hI0_ξ' : I0 (1 / starRingEnd ℂ ξ) ≠ 0 := by
    rw [hinv_ξ]
    have h3 : (ω ^ m * (1 / starRingEnd ℂ ζ)) ^ 3 = (1 / starRingEnd ℂ ζ) ^ 3 := by
      rw [mul_pow, ← pow_mul, mul_comm m 3, pow_mul, ω_cube, one_pow, one_mul]
    unfold I0; rwa [h3]
  have h0 := u6_reflection_law hζ hI0_ξ hI0_ξ'
  rw [hinv_ξ, u6_rot_pow, u6_rot_pow] at h0
  fin_cases j
  · simpa [m] using h0
  · simp only [m, Nat.reduceSub, Nat.reduceMod] at h0
    have h1 := congrArg (ω * ·) h0
    have hrot2 : hypRefl 1 (ω * (ω ^ 2 * u6 ζ)) = ω * hypRefl 0 (ω ^ 2 * u6 ζ) :=
      hypRefl_rot 0 (ω ^ 2 * u6 ζ)
    have hmul : ω * (ω ^ 2 * u6 ζ) = u6 ζ := by linear_combination u6 ζ * ω_cube
    have hmul' : ω * (ω ^ 2 * u6 (1 / starRingEnd ℂ ζ)) = u6 (1 / starRingEnd ℂ ζ) := by
      linear_combination u6 (1 / starRingEnd ℂ ζ) * ω_cube
    rw [← hrot2, hmul, hmul'] at h1
    exact h1
  · simp only [m, Nat.reduceSub, Nat.reduceMod, pow_one] at h0
    have h1 := congrArg (ω ^ 2 * ·) h0
    have hrot0 : hypRefl 1 (ω * (ω * u6 ζ)) = ω * hypRefl 0 (ω * u6 ζ) :=
      hypRefl_rot 0 (ω * u6 ζ)
    have hrot1 : hypRefl 2 (ω * (ω * (ω * u6 ζ))) = ω * hypRefl 1 (ω * (ω * u6 ζ)) :=
      hypRefl_rot 1 (ω * (ω * u6 ζ))
    have hrot : hypRefl 2 (ω ^ 2 * (ω * u6 ζ)) = ω ^ 2 * hypRefl 0 (ω * u6 ζ) := by
      calc hypRefl 2 (ω ^ 2 * (ω * u6 ζ))
          = hypRefl 2 (ω * (ω * (ω * u6 ζ))) := by ring_nf
        _ = ω * hypRefl 1 (ω * (ω * u6 ζ)) := hrot1
        _ = ω * (ω * hypRefl 0 (ω * u6 ζ)) := by rw [hrot0]
        _ = ω ^ 2 * hypRefl 0 (ω * u6 ζ) := by ring
    have hmul : ω ^ 2 * (ω * u6 ζ) = u6 ζ := by linear_combination u6 ζ * ω_cube
    have hmul' : ω ^ 2 * (ω * u6 (1 / starRingEnd ℂ ζ)) = u6 (1 / starRingEnd ℂ ζ) := by
      linear_combination u6 (1 / starRingEnd ℂ ζ) * ω_cube
    rw [← hrot, hmul, hmul'] at h1
    exact h1

lemma u3_reflection_law_side (j : Fin 3) {ζ : ℂ} (hζ : ω ^ ((3 - j.val) % 3) * ζ ∈ Ω0) :
    u3 (1 / starRingEnd ℂ ζ) = eucRefl j (u3 ζ) := by
  set m : ℕ := (3 - j.val) % 3
  set ξ := ω ^ m * ζ
  have hinv_ξ : 1 / starRingEnd ℂ ξ = ω ^ m * (1 / starRingEnd ℂ ζ) := by
    have hstar : starRingEnd ℂ (ω ^ m) * ω ^ m = 1 := by
      rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm, norm_ω_pow]; norm_num
    simp only [ξ, map_mul, one_div, mul_inv, mul_comm (ω ^ m)]
    congr 1
    exact inv_eq_of_mul_eq_one_right hstar
  have h0 := u3_reflection_law hζ
  rw [hinv_ξ, u3_rot_pow, u3_rot_pow] at h0
  fin_cases j
  · simpa [m] using h0
  · simp only [m, Nat.reduceSub, Nat.reduceMod] at h0
    have h1 := congrArg (ω * ·) h0
    have hrot2 : eucRefl 1 (ω * (ω ^ 2 * u3 ζ)) = ω * eucRefl 0 (ω ^ 2 * u3 ζ) := eucRefl_rot 0 _
    have hmul : ω * (ω ^ 2 * u3 ζ) = u3 ζ := by linear_combination u3 ζ * ω_cube
    have hmul' : ω * (ω ^ 2 * u3 (1 / starRingEnd ℂ ζ)) = u3 (1 / starRingEnd ℂ ζ) := by
      linear_combination u3 (1 / starRingEnd ℂ ζ) * ω_cube
    rw [← hrot2, hmul, hmul'] at h1
    exact h1
  · simp only [m, Nat.reduceSub, Nat.reduceMod, pow_one] at h0
    have h1 := congrArg (ω ^ 2 * ·) h0
    have hrot0 : eucRefl 1 (ω * (ω * u3 ζ)) = ω * eucRefl 0 (ω * u3 ζ) := eucRefl_rot 0 _
    have hrot1 : eucRefl 2 (ω * (ω * (ω * u3 ζ))) = ω * eucRefl 1 (ω * (ω * u3 ζ)) := eucRefl_rot 1 _
    have hrot : eucRefl 2 (ω ^ 2 * (ω * u3 ζ)) = ω ^ 2 * eucRefl 0 (ω * u3 ζ) := by
      calc eucRefl 2 (ω ^ 2 * (ω * u3 ζ))
          = eucRefl 2 (ω * (ω * (ω * u3 ζ))) := by ring_nf
        _ = ω * eucRefl 1 (ω * (ω * u3 ζ)) := hrot1
        _ = ω * (ω * eucRefl 0 (ω * u3 ζ)) := by rw [hrot0]
        _ = ω ^ 2 * eucRefl 0 (ω * u3 ζ) := by ring
    have hmul : ω ^ 2 * (ω * u3 ζ) = u3 ζ := by linear_combination u3 ζ * ω_cube
    have hmul' : ω ^ 2 * (ω * u3 (1 / starRingEnd ℂ ζ)) = u3 (1 / starRingEnd ℂ ζ) := by
      linear_combination u3 (1 / starRingEnd ℂ ζ) * ω_cube
    rw [← hrot, hmul, hmul'] at h1
    exact h1

/-- Holomorphic extension of `φ` across any interior point `z` of side `j` of `Δ1`. -/
lemma φ_side_extension (j : Fin 3) {z : ℂ} (hz : z ∈ Δ1)
    (hsj : ‖z - sideCenter j‖ ^ 2 = ‖sideCenter j‖ ^ 2 - 1)
    (hother : ∀ i : Fin 3, i ≠ j → ‖sideCenter i‖ ^ 2 - 1 < ‖z - sideCenter i‖ ^ 2) :
    ∃ (ρ : ℝ) (ψ : ℂ → ℂ), 0 < ρ ∧ ρ ≤ 1 / 2 ∧
      DifferentiableOn ℂ ψ (hypBall z ρ) ∧
      (∀ x ∈ hypBall z ρ, ∀ i : Fin 3, i ≠ j → ‖sideCenter i‖ ^ 2 - 1 < ‖x - sideCenter i‖ ^ 2) ∧
      hypBall z ρ ⊆ Δ1 ∪ hypRefl j '' Δ1 ∧
      (∀ x ∈ hypBall z ρ ∩ Δ1, ψ x = φ x) ∧
      (∀ x ∈ hypBall z ρ ∩ hypRefl j '' Δ1, ψ x = chartMap [j] φ x) := by
  set ζ := u6Inv z
  have hζ_cl : ζ ∈ closedBall (0 : ℂ) 1 := u6Inv_mem_closedBall hz
  have hζ_sph : ζ ∈ sphere (0 : ℂ) 1 := by
    by_contra hns
    have hb : ζ ∈ ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hζ_cl; rw [Metric.mem_sphere] at hns
      exact lt_of_le_of_ne hζ_cl hns
    have hopen := u6_biholo.1 hb
    rw [u6_u6Inv hz] at hopen
    exact (hopen.2 j).ne hsj.symm
  obtain ⟨k, θ, h0, h1, hζ_eq⟩ := sphere_decomp hζ_sph
  -- Show `k = j` and `0 < θ`!
  have hθ_pos : 0 < θ := by
    rcases eq_or_lt_of_le h0 with rfl | hpos
    · exfalso
      have hv : z = vert1 k := by
        rw [← u6_u6Inv hz]; change u6 ζ = vert1 k
        rw [hζ_eq]; simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
        rw [show ω ^ (k : ℕ) = ω ^ (k : ℕ) * 1 by ring, u6_rot_pow, u6_one]; rfl
      -- At `vert1 k`, BOTH side `k` and side `(k + 2) % 3` satisfy equality, contradicting `hother`!
      have hv_on : ‖vert1 k - sideCenter k‖ ^ 2 = ‖sideCenter k‖ ^ 2 - 1 ∧
          ‖vert1 k - sideCenter ⟨(k.val + 2) % 3, Nat.mod_lt _ (by norm_num)⟩‖ ^ 2 =
            ‖sideCenter ⟨(k.val + 2) % 3, Nat.mod_lt _ (by norm_num)⟩‖ ^ 2 - 1 := by
        have h00 := vert1_zero_on_side0
        have h02 := vert1_zero_on_side2
        simp only [vert1, sideCenter, Fin.val_zero, Fin.val_two, pow_zero, one_mul] at h00 h02
        constructor
        · simp only [vert1, sideCenter, ← mul_sub, norm_mul, norm_ω_pow, one_mul]; exact h00
        · have hsc : sideCenter ⟨(k.val + 2) % 3, Nat.mod_lt _ (by norm_num)⟩ = ω ^ (k : ℕ) * (ω ^ 2 * a0) := by
            fin_cases k <;> simp only [sideCenter, Nat.reduceAdd, Nat.reduceMod, pow_zero, pow_one, one_mul]
            · linear_combination -a0 * ω_cube
            · linear_combination -ω * a0 * ω_cube
          rw [hsc]
          have hna : ‖ω ^ 2 * a0‖ = ‖a0‖ := by rw [norm_mul, norm_ω_pow, one_mul]
          rw [hna] at h02
          simp only [vert1, ← mul_sub, norm_mul, norm_ω_pow, one_mul]; exact h02
      by_cases hkj' : k = j
      · subst hkj'
        have hij : (⟨(k.val + 2) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) ≠ k := by
          fin_cases k <;> decide
        have hstr := hother _ hij; rw [hv] at hstr
        exact hstr.ne hv_on.2.symm
      · have hstr := hother k hkj'; rw [hv] at hstr
        exact hstr.ne hv_on.1.symm
    · exact hpos
  have hkj : k = j := by
    by_contra hne
    have hstr := u6_arc_strict_other_sides hθ_pos h1
    obtain ⟨m, hm12, hsc⟩ := sideCenter_rot_eq k j (Ne.symm hne)
    have hz_eq : z = ω ^ (k : ℕ) * u6 (Complex.exp ((θ : ℂ) * I)) := by
      rw [← u6_u6Inv hz]; change u6 ζ = _; rw [hζ_eq, u6_rot_pow]
    rw [hz_eq, hsc, ← mul_sub, norm_mul, norm_ω_pow, one_mul, norm_mul, norm_ω_pow, one_mul] at hsj
    rcases hm12 with rfl | rfl
    · exact hstr.1.ne hsj.symm
    · exact hstr.2.ne hsj.symm
  subst k
  -- Now `ζ = ω^j * exp (i θ)` with `0 < θ < 2π/3`, so `ω^((3-j)%3) * ζ = exp (i θ) ∈ Ω0`!
  set Ωj : Set ℂ := {w : ℂ | ω ^ ((3 - j.val) % 3) * w ∈ Ω0}
  have hΩj_open : IsOpen Ωj := isOpen_Ω0.preimage (continuous_const.mul continuous_id)
  have hΩj_sub_Ω : Ωj ⊆ Ω := by
    intro w hw
    have h1' : (ω ^ ((3 - j.val) % 3) * w) ^ 3 ∈ slitSet := Ω0_subset_Ω hw
    have h3 : (ω ^ ((3 - j.val) % 3) * w) ^ 3 = w ^ 3 := by
      rw [mul_pow, ← pow_mul, mul_comm _ 3, pow_mul, ω_cube, one_pow, one_mul]
    change w ^ 3 ∈ slitSet
    rwa [h3] at h1'
  have hζ_Ωj : ζ ∈ Ωj := by
    change ω ^ ((3 - j.val) % 3) * ζ ∈ Ω0
    rw [hζ_eq, ← mul_assoc]
    have hpow1 : ω ^ ((3 - j.val) % 3) * ω ^ (j : ℕ) = 1 := by
      fin_cases j
      · simp
      · simp only [Nat.reduceSub, Nat.reduceMod]; rw [← pow_add]; exact ω_cube
      · simp only [Nat.reduceSub, Nat.reduceMod]; rw [← pow_add]; exact ω_cube
    rw [hpow1, one_mul]
    exact exp_I_mem_Ω0 hθ_pos h1
  have hI0_ζ : I0 ζ ≠ 0 := I0_ne_zero_of_norm_le_one (by simpa [Metric.mem_closedBall, dist_zero_right] using hζ_cl)
  -- Open neighborhood `U_ζ ⊆ Ωj` where `I0 ≠ 0` and `1 / conj w` stays in `U_ζ`!
  set U0 : Set ℂ := Ωj ∩ {w | I0 w ≠ 0}
  have hI0_cont : ContinuousOn I0 Ω := fun w hw =>
    (hasDerivAt_euler_comp_cube (a := 1 / 12) (b := 5 / 12) (c := 2 / 3) (by norm_num) (by norm_num) hw).continuousAt.continuousWithinAt
  have hU0_open : IsOpen U0 := by
    have h1' : U0 = Ωj ∩ (I0 ⁻¹' {0}ᶜ) := rfl
    rw [h1']
    exact (hI0_cont.mono hΩj_sub_Ω).isOpen_inter_preimage hΩj_open isClosed_singleton.isOpen_compl
  have hζ_U0 : ζ ∈ U0 := ⟨hζ_Ωj, hI0_ζ⟩
  have hu6_diff_U0 : DifferentiableOn ℂ u6 U0 := fun w hw =>
    (u6_hasDerivAt_of_I0_ne_zero (hΩj_sub_Ω hw.1) hw.2).differentiableAt.differentiableWithinAt
  have hsd := differentiableOn_hasStrictDerivAt hU0_open hu6_diff_U0 hζ_U0
  have hdne := u6_deriv_ne_zero_of_I0_ne_zero (hΩj_sub_Ω hζ_Ωj) hI0_ζ
  set e := (hsd.hasStrictFDerivAt_equiv hdne).toOpenPartialHomeomorph u6
  have he_coe : (e : ℂ → ℂ) = u6 := (hsd.hasStrictFDerivAt_equiv hdne).toOpenPartialHomeomorph_coe
  have hζ_src : ζ ∈ e.source := (hsd.hasStrictFDerivAt_equiv hdne).mem_toOpenPartialHomeomorph_source
  have hz_tgt : z ∈ e.target := by
    rw [← u6_u6Inv hz]; exact (hsd.hasStrictFDerivAt_equiv hdne).image_mem_toOpenPartialHomeomorph_target
  -- Shrink `e.source` to an open neighborhood `V_ζ` of `ζ` with `V_ζ ⊆ e.source ∩ U0` and `1/conj V_ζ ⊆ e.source ∩ U0`!
  have hinv_ζ : 1 / starRingEnd ℂ ζ = ζ := by
    rw [hζ_eq, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      one_div, mul_inv, ← Complex.exp_neg, neg_neg]
    have hstar : (starRingEnd ℂ (ω ^ (j : ℕ)))⁻¹ = ω ^ (j : ℕ) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm, norm_ω_pow]; norm_num
    rw [hstar]
  have hinv_cont : ContinuousAt (fun w : ℂ => 1 / starRingEnd ℂ w) ζ := by
    refine continuousAt_const.div Complex.continuous_conj.continuousAt ?_
    intro h; have := congrArg norm h; rw [RCLike.norm_conj, norm_zero] at this
    have hn : ‖ζ‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hζ_sph
    linarith
  have hV_nhds : (e.source ∩ U0) ∩ (fun w => 1 / starRingEnd ℂ w) ⁻¹' (e.source ∩ U0) ∈ 𝓝 ζ :=
    Filter.inter_mem ((e.open_source.inter hU0_open).mem_nhds ⟨hζ_src, hζ_U0⟩)
      (hinv_cont.preimage_mem_nhds (by rw [hinv_ζ]; exact (e.open_source.inter hU0_open).mem_nhds ⟨hζ_src, hζ_U0⟩))
  -- Choose `ρ ∈ (0, 1/2]` such that:
  -- (1) `hypBall z ρ ⊆ e.target` and `e.symm '' hypBall z ρ ⊆ (e.source ∩ U0) ∩ (1/conj)⁻¹'(e.source ∩ U0)`
  -- (2) `u6Inv '' (hypBall z ρ ∩ Δ1) ⊆ e.source`
  -- (3) for all `x ∈ hypBall z ρ`, `∀ i ≠ j`, `‖sideCenter i‖^2 - 1 < ‖x - sideCenter i‖^2`!
  have h1_nhds : e.target ∩ e.symm ⁻¹' ((e.source ∩ U0) ∩ (fun w => 1 / starRingEnd ℂ w) ⁻¹' (e.source ∩ U0)) ∈ 𝓝 z := by
    have hsymm_cont : ContinuousAt e.symm z := (e.continuousOn_symm z hz_tgt).continuousAt (e.open_target.mem_nhds hz_tgt)
    have hsymm_z : e.symm z = ζ := by
      have : e ζ = z := by rw [he_coe]; exact u6_u6Inv hz
      rw [← this]; exact e.left_inv hζ_src
    exact Filter.inter_mem (e.open_target.mem_nhds hz_tgt)
      (hsymm_cont.preimage_mem_nhds (by rw [hsymm_z]; exact hV_nhds))
  have h2_nhds : {x : ℂ | x ∈ Δ1 → u6Inv x ∈ e.source} ∈ 𝓝 z := by
    have hcont_at : ContinuousWithinAt u6Inv Δ1 z := u6Inv_continuousOn z hz
    have hmem : e.source ∈ 𝓝 (u6Inv z) := e.open_source.mem_nhds hζ_src
    have hpre := hcont_at.preimage_mem_nhdsWithin hmem
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hpre
    obtain ⟨t, ht, hsub⟩ := hpre
    exact Filter.mem_of_superset ht fun x hx hxΔ => hsub ⟨hx, hxΔ⟩
  have h3_nhds : {x : ℂ | ∀ i : Fin 3, i ≠ j → ‖sideCenter i‖ ^ 2 - 1 < ‖x - sideCenter i‖ ^ 2} ∈ 𝓝 z := by
    have hopen : IsOpen {x : ℂ | ∀ i : Fin 3, i ≠ j → ‖sideCenter i‖ ^ 2 - 1 < ‖x - sideCenter i‖ ^ 2} := by
      have : {x : ℂ | ∀ i : Fin 3, i ≠ j → ‖sideCenter i‖ ^ 2 - 1 < ‖x - sideCenter i‖ ^ 2} =
          ⋂ i : {i : Fin 3 // i ≠ j}, (fun x : ℂ => ‖x - sideCenter i.1‖ ^ 2) ⁻¹' Ioi (‖sideCenter i.1‖ ^ 2 - 1) := by
        ext x; simp
      rw [this]
      exact isOpen_iInter_of_finite fun i =>
        isOpen_Ioi.preimage ((continuous_id.sub continuous_const).norm.pow 2)
    exact hopen.mem_nhds hother
  -- Convert Euclidean neighborhood of `z` into a `hypBall z ρ`!
  have hall_nhds := Filter.inter_mem (Filter.inter_mem h1_nhds h2_nhds) h3_nhds
  obtain ⟨δ, hδ, hball_δ⟩ := Metric.mem_nhds_iff.mp hall_nhds
  -- Since `hypDist x z < ρ ⟹ ‖x - z‖ < 2 * ρ` (for `‖x‖ < 1, ‖z‖ < 1`, `‖1 - conj z * x‖ < 2`!),
  -- choose `ρ = min (1 / 2) (δ / 2)`!
  set ρ : ℝ := min (1 / 2) (δ / 2)
  have hρ_pos : 0 < ρ := lt_min (by norm_num) (by linarith)
  have hρ_le : ρ ≤ 1 / 2 := min_le_left _ _
  have hhb_sub : hypBall z ρ ⊆ ball z δ := by
    intro x ⟨hx1, hdist⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hden_le : ‖1 - starRingEnd ℂ z * x‖ ≤ 2 := by
      calc ‖1 - starRingEnd ℂ z * x‖ ≤ ‖(1 : ℂ)‖ + ‖starRingEnd ℂ z * x‖ := norm_sub_le _ _
        _ = 1 + ‖z‖ * ‖x‖ := by rw [norm_one, norm_mul, RCLike.norm_conj]
        _ ≤ 1 + 1 * 1 := by nlinarith [hz.1, hx1, norm_nonneg z, norm_nonneg x]
        _ = 2 := by norm_num
    have hden_pos : 0 < ‖1 - starRingEnd ℂ z * x‖ :=
      norm_pos_iff.mpr (one_sub_conj_mul_ne_zero hx1 hz.1)
    unfold hypDist at hdist
    rw [norm_div, div_lt_iff₀ hden_pos] at hdist
    have hρδ : ρ ≤ δ / 2 := min_le_right _ _
    nlinarith
  -- Define `ψ := u3 ∘ e.symm` on `hypBall z ρ`!
  let ψ : ℂ → ℂ := fun x => u3 (e.symm x)
  have hψ_diff : DifferentiableOn ℂ ψ (hypBall z ρ) := by
    intro x hx
    have hmem1 := (hball_δ (hhb_sub hx)).1.1
    have hxt : x ∈ e.target := hmem1.1
    have hxs : e.symm x ∈ e.source ∩ U0 := hmem1.2.1
    have hsd_x := differentiableOn_hasStrictDerivAt hU0_open hu6_diff_U0 hxs.2
    have hdne_x := u6_deriv_ne_zero_of_I0_ne_zero (hΩj_sub_Ω hxs.2.1) hxs.2.2
    have hleft_x : ∀ᶠ w in 𝓝 (e.symm x), e.symm (u6 w) = w := by
      filter_upwards [e.open_source.mem_nhds hxs.1] with w hw
      rw [← he_coe]; exact e.left_inv hw
    have hinv_x := hsd_x.to_local_left_inverse hdne_x hleft_x
    have he_eq : u6 (e.symm x) = x := by rw [← he_coe]; exact e.right_inv hxt
    rw [he_eq] at hinv_x
    have hu3_x : DifferentiableAt ℂ u3 (e.symm x) :=
      u3_differentiableOn_Ω.differentiableAt (isOpen_Ω.mem_nhds (hΩj_sub_Ω hxs.2.1))
    exact (hu3_x.comp x hinv_x.hasDerivAt.differentiableAt).differentiableWithinAt
  have hother_hb : ∀ x ∈ hypBall z ρ, ∀ i : Fin 3, i ≠ j →
      ‖sideCenter i‖ ^ 2 - 1 < ‖x - sideCenter i‖ ^ 2 :=
    fun x hx => (hball_δ (hhb_sub hx)).2
  have hhb_refl : ∀ x ∈ hypBall z ρ, hypRefl j x ∈ hypBall z ρ := by
    intro x ⟨hx1, hdist⟩
    refine ⟨hypRefl_mem_ball j hx1, ?_⟩
    have hfix : hypRefl j z = z := (hypRefl_fixed_iff j hz.1).mpr hsj
    rw [← hfix, hypDist_hypRefl j hx1 hz.1]
    exact hdist
  have hhb_cov : hypBall z ρ ⊆ Δ1 ∪ hypRefl j '' Δ1 := by
    intro x hx
    by_cases hside : ‖sideCenter j‖ ^ 2 - 1 ≤ ‖x - sideCenter j‖ ^ 2
    · left
      refine ⟨hx.1, fun i => ?_⟩
      by_cases hij : i = j
      · exact hij ▸ hside
      · exact (hother_hb x hx i hij).le
    · push Not at hside
      right
      refine ⟨hypRefl j x, ?_, hypRefl_invol j hx.1⟩
      have hrx := hhb_refl x hx
      refine ⟨hrx.1, fun i => ?_⟩
      by_cases hij : i = j
      · subst i
        have hsign := hypRefl_side_sign j hx.1
        have hnum_pos : 0 < ‖sideCenter j‖ ^ 2 - 1 := sideCenter_sq_sub_one_pos j
        have hden_pos : 0 < ‖x - sideCenter j‖ ^ 2 := by
          have hne : x - sideCenter j ≠ 0 := by
            intro h0; have := congrArg (starRingEnd ℂ) h0
            simp only [map_sub, map_zero] at this
            exact conj_sub_conj_sideCenter_ne_zero j hx.1 this
          positivity
        have hfrac : 0 < (‖sideCenter j‖ ^ 2 - 1) / ‖x - sideCenter j‖ ^ 2 := div_pos hnum_pos hden_pos
        nlinarith
      · exact (hother_hb _ hrx i hij).le
  have hψ_Δ1 : ∀ x ∈ hypBall z ρ ∩ Δ1, ψ x = φ x := by
    intro x ⟨hx, hxΔ⟩
    have hxt : x ∈ e.target := (hball_δ (hhb_sub hx)).1.1.1
    have hu_src : u6Inv x ∈ e.source := (hball_δ (hhb_sub hx)).1.2 hxΔ
    have heq : e.symm x = u6Inv x := by
      have h1 : e (u6Inv x) = x := by rw [he_coe]; exact u6_u6Inv hxΔ
      conv_lhs => rw [← h1]
      exact e.left_inv hu_src
    simp only [ψ, φ, heq]
  have hψ_refl : ∀ x ∈ hypBall z ρ ∩ hypRefl j '' Δ1, ψ x = chartMap [j] φ x := by
    intro x ⟨hx, hxR⟩
    have hrx : hypRefl j x ∈ hypBall z ρ := hhb_refl x hx
    have hrxΔ : hypRefl j x ∈ Δ1 := by
      obtain ⟨y, hyΔ, hyx⟩ := hxR
      rwa [← hyx, hypRefl_invol j hyΔ.1]
    -- Show `e.symm x = 1 / conj (e.symm (hypRefl j x))`!
    have hmem_rx := (hball_δ (hhb_sub hrx)).1.1
    set w := e.symm (hypRefl j x)
    have hw_U0 : w ∈ e.source ∩ U0 := hmem_rx.2.1
    have hw'_U0 : 1 / starRingEnd ℂ w ∈ e.source ∩ U0 := hmem_rx.2.2
    have hu6_w' : u6 (1 / starRingEnd ℂ w) = x := by
      rw [u6_reflection_law_side j hw_U0.2.1 hw_U0.2.2 hw'_U0.2.2]
      have h1 : u6 w = hypRefl j x := by rw [← he_coe]; exact e.right_inv hmem_rx.1
      rw [h1, hypRefl_invol j hx.1]
    have hsymm_x : e.symm x = 1 / starRingEnd ℂ w := by
      have h1 : e (1 / starRingEnd ℂ w) = x := by rw [he_coe]; exact hu6_w'
      rw [← h1]; exact e.left_inv hw'_U0.1
    have hψ_rx : ψ (hypRefl j x) = φ (hypRefl j x) := hψ_Δ1 _ ⟨hrx, hrxΔ⟩
    simp only [ψ, hsymm_x, u3_reflection_law_side j hw_U0.2.1]
    change eucRefl j (ψ (hypRefl j x)) = chartMap [j] φ x
    rw [hψ_rx]
    simp only [chartMap, eucWord_cons, eucWord_nil, List.reverse_singleton, hypWord_cons, hypWord_nil]
  exact ⟨ρ, ψ, hρ_pos, hρ_le, hψ_diff, hother_hb, hhb_cov, hψ_Δ1, hψ_refl⟩

/- ## 5. Exact Algebraic Sector Coordinates & 12-Tile Vertex Extension -/

/-- Exact linear characterization of side 0 in `w = mobiusToZero R z` coordinates! -/
lemma mobiusToZero_R_side0_sign {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(1 : ℂ) + (R : ℂ) * mobiusToZero (R : ℂ) z‖ ^ 2 *
      (‖z - sideCenter 0‖ ^ 2 - (‖sideCenter 0‖ ^ 2 - 1)) =
      -6 * R ^ 3 * (mobiusToZero (R : ℂ) z * (1 + zeta12)).im := by
  set w := mobiusToZero (R : ℂ) z
  have hR : ‖(R : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_of_nonneg R_pos.le] using R_lt_one
  have hRm : ‖-(R : ℂ)‖ < 1 := by simpa using hR
  have hw1 : ‖w‖ < 1 := mobiusToZero_mem_ball hR hz
  have hz_from_w : z = (w + (R : ℂ)) / (1 + (R : ℂ) * w) := by
    have hinv := mobiusToZero_inv hR hz
    simpa only [w, mobiusToZero, map_neg, Complex.conj_ofReal, sub_neg_eq_add, neg_mul] using hinv.symm
  have hden : (1 : ℂ) + (R : ℂ) * w ≠ 0 := by
    have := one_sub_conj_mul_ne_zero hw1 hRm
    simpa [Complex.conj_ofReal] using this
  rw [normSq_sub_sideCenter_iff 0 z]
  have h1 : ‖(1 : ℂ) + (R : ℂ) * w‖ ^ 2 * ‖z‖ ^ 2 = ‖w + (R : ℂ)‖ ^ 2 := by
    rw [hz_from_w, norm_div, div_pow, mul_div_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hden))]
  have h2 : ‖(1 : ℂ) + (R : ℂ) * w‖ ^ 2 * (z * starRingEnd ℂ (sideCenter 0)).re =
      ((w + (R : ℂ)) * (1 + (R : ℂ) * starRingEnd ℂ w) * starRingEnd ℂ a0).re := by
    have hsc : sideCenter 0 = a0 := by simp [sideCenter]
    rw [hsc, hz_from_w]
    have hmul : (((‖(1 : ℂ) + (R : ℂ) * w‖ ^ 2 : ℝ) : ℂ) *
        (((w + (R : ℂ)) / (1 + (R : ℂ) * w)) * starRingEnd ℂ a0)) =
        (w + (R : ℂ)) * (1 + (R : ℂ) * starRingEnd ℂ w) * starRingEnd ℂ a0 := by
      have hsq : ((‖(1 : ℂ) + (R : ℂ) * w‖ ^ 2 : ℝ) : ℂ) =
          (1 + (R : ℂ) * w) * (1 + (R : ℂ) * starRingEnd ℂ w) := by
        rw [Complex.sq_norm, ← Complex.mul_conj]
        simp [Complex.conj_ofReal]
      rw [hsq]
      field_simp [hden]
    have := congrArg Complex.re hmul
    simpa only [Complex.re_ofReal_mul] using this
  have hlin : ‖(1 : ℂ) + (R : ℂ) * w‖ ^ 2 *
      (‖z‖ ^ 2 - 2 * (z * starRingEnd ℂ (sideCenter 0)).re + 1) =
      ‖w + (R : ℂ)‖ ^ 2 - 2 * ((w + (R : ℂ)) * (1 + (R : ℂ) * starRingEnd ℂ w) * starRingEnd ℂ a0).re +
        ‖(1 : ℂ) + (R : ℂ) * w‖ ^ 2 := by
    linear_combination h1 - 2 * h2
  rw [hlin, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, one_re, one_im, conj_re, conj_im,
    zeta12, a0_re, a0_im, zero_mul, sub_zero, add_zero, zero_add]
  have hA : 1 + R ^ 2 - (2 + Real.sqrt 3) * R ^ 2 = 0 := by linarith [R_sq_mul]
  have hB : 4 * R - (1 + R ^ 2) * (2 + Real.sqrt 3) * R = -3 * R ^ 3 := by
    have hR2 : 2 * R ^ 2 - (Real.sqrt 3 - 1) = 0 := by linarith [R_sq]
    linear_combination R * hA + R * hR2
  have hC : -(1 - R ^ 2) * ((2 + Real.sqrt 3) * R * Real.sqrt 3) = -3 * (2 + Real.sqrt 3) * R ^ 3 := by
    have hR2 : 2 * R ^ 2 - (Real.sqrt 3 - 1) = 0 := by linarith [R_sq]
    linear_combination (2 + Real.sqrt 3) * R * ((3 + Real.sqrt 3) / 2 * hR2 + sq_sqrt3 / 2)
  linear_combination (1 + w.re ^ 2 + w.im ^ 2) * hA + w.re * hB + w.im * hC

lemma mobiusToZero_R_side2_sign {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(1 : ℂ) + (R : ℂ) * mobiusToZero (R : ℂ) z‖ ^ 2 *
      (‖z - sideCenter 2‖ ^ 2 - (‖sideCenter 2‖ ^ 2 - 1)) =
      6 * R ^ 3 * (mobiusToZero (R : ℂ) z * (1 + zeta12Inv)).im := by
  have hcz : ‖starRingEnd ℂ z‖ < 1 := by simpa [RCLike.norm_conj] using hz
  have h0 := mobiusToZero_R_side0_sign hcz
  have hconj_m : mobiusToZero (R : ℂ) (starRingEnd ℂ z) = starRingEnd ℂ (mobiusToZero (R : ℂ) z) := by
    unfold mobiusToZero; simp [Complex.conj_ofReal]
  have ha2 : sideCenter 2 = starRingEnd ℂ (sideCenter 0) := by
    simp only [sideCenter, Fin.val_two, Fin.val_zero, pow_zero, one_mul, a0, map_mul,
      Complex.conj_ofReal, map_add, map_one, star_ω]
    have : ω ^ 2 * (1 + ω) = 1 + ω ^ 2 := by linear_combination ω_cube
    linear_combination (((2 + Real.sqrt 3) * R : ℝ) : ℂ) * this
  have hnorm1 : ‖(1 : ℂ) + (R : ℂ) * mobiusToZero (R : ℂ) (starRingEnd ℂ z)‖ =
      ‖(1 : ℂ) + (R : ℂ) * mobiusToZero (R : ℂ) z‖ := by
    rw [hconj_m]
    have : (1 : ℂ) + (R : ℂ) * starRingEnd ℂ (mobiusToZero (R : ℂ) z) =
        starRingEnd ℂ ((1 : ℂ) + (R : ℂ) * mobiusToZero (R : ℂ) z) := by
      simp [Complex.conj_ofReal]
    rw [this, RCLike.norm_conj]
  have hnorm2 : ‖starRingEnd ℂ z - sideCenter 0‖ = ‖z - sideCenter 2‖ := by
    rw [ha2]
    have : starRingEnd ℂ (z - starRingEnd ℂ (sideCenter 0)) = starRingEnd ℂ z - sideCenter 0 := by simp
    rw [← this, RCLike.norm_conj]
  have hnorm3 : ‖sideCenter 0‖ = ‖sideCenter 2‖ := by rw [ha2, RCLike.norm_conj]
  rw [hnorm1, hnorm2, hnorm3, hconj_m] at h0
  have him : (starRingEnd ℂ (mobiusToZero (R : ℂ) z) * (1 + zeta12)).im =
      -(mobiusToZero (R : ℂ) z * (1 + zeta12Inv)).im := by
    have : starRingEnd ℂ (mobiusToZero (R : ℂ) z) * (1 + zeta12) =
        starRingEnd ℂ (mobiusToZero (R : ℂ) z * (1 + zeta12Inv)) := by
      simp [star_zeta12Inv]
    rw [this, conj_im]
  rw [him] at h0; linarith

/-- The closed fundamental wedge `W0` in `w = mobiusToZero R z` coordinates. -/
def W0 : Set ℂ :=
  {w : ℂ | (w * (1 + zeta12)).im ≤ 0 ∧ 0 ≤ (w * (1 + zeta12Inv)).im}

lemma mem_W0_iff_sides {z : ℂ} (hz : ‖z‖ < 1) :
    mobiusToZero (R : ℂ) z ∈ W0 ↔
      ‖sideCenter 0‖ ^ 2 - 1 ≤ ‖z - sideCenter 0‖ ^ 2 ∧
      ‖sideCenter 2‖ ^ 2 - 1 ≤ ‖z - sideCenter 2‖ ^ 2 := by
  have hR : ‖(R : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_of_nonneg R_pos.le] using R_lt_one
  have hRm : ‖-(R : ℂ)‖ < 1 := by simpa using hR
  have hw1 : ‖mobiusToZero (R : ℂ) z‖ < 1 := mobiusToZero_mem_ball hR hz
  have hden_pos : 0 < ‖(1 : ℂ) + (R : ℂ) * mobiusToZero (R : ℂ) z‖ ^ 2 := by
    have hne : (1 : ℂ) + (R : ℂ) * mobiusToZero (R : ℂ) z ≠ 0 := by
      simpa [Complex.conj_ofReal] using one_sub_conj_mul_ne_zero hw1 hRm
    positivity
  have hR3_pos : 0 < 6 * R ^ 3 := by have := R_pos; positivity
  have hs0 := mobiusToZero_R_side0_sign hz
  have hs2 := mobiusToZero_R_side2_sign hz
  unfold W0
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h2⟩; constructor <;> nlinarith
  · rintro ⟨h0, h2⟩; constructor <;> nlinarith

lemma conj_mem_W0_iff {w : ℂ} : starRingEnd ℂ w ∈ W0 ↔ w ∈ W0 := by
  have h1 : (starRingEnd ℂ w * (1 + zeta12)).im = -(w * (1 + zeta12Inv)).im := by
    have : starRingEnd ℂ w * (1 + zeta12) = starRingEnd ℂ (w * (1 + zeta12Inv)) := by
      simp [star_zeta12Inv]
    rw [this, conj_im]
  have h2 : (starRingEnd ℂ w * (1 + zeta12Inv)).im = -(w * (1 + zeta12)).im := by
    have hst : starRingEnd ℂ zeta12 = zeta12Inv := by
      rw [← star_zeta12Inv, RingHomCompTriple.comp_apply, RingHom.id_apply]
    have : starRingEnd ℂ w * (1 + zeta12Inv) = starRingEnd ℂ (w * (1 + zeta12)) := by
      simp [hst]
    rw [this, conj_im]
  unfold W0; simp only [mem_ofPred_eq, h1, h2]
  constructor <;> rintro ⟨a, b⟩ <;> exact ⟨by linarith, by linarith⟩

/-- The 12 cyclic dihedral words `u k` around `vert1 0 = R` (`k : ℕ`). -/
def v0Word : ℕ → List (Fin 3)
  | 0 => []
  | k + 1 => v0Word k ++ [if k % 2 = 0 then 2 else 0]

lemma zeta12_eq_exp : zeta12 = Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * I) := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]; simp [zeta12, Real.cos_pi_div_six]
  · rw [Complex.exp_ofReal_mul_I_im]; simp [zeta12, Real.sin_pi_div_six]

lemma zeta12Inv_eq_exp : zeta12Inv = Complex.exp (((-(Real.pi / 6) : ℝ) : ℂ) * I) := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]; simp [zeta12Inv, Real.cos_pi_div_six]
  · rw [Complex.exp_ofReal_mul_I_im]; simp [zeta12Inv, Real.sin_pi_div_six]; ring

lemma mobiusToZero_R_v0Word (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    mobiusToZero (R : ℂ) (hypWord (v0Word k) z) =
      if k % 2 = 0 then zeta12 ^ k * mobiusToZero (R : ℂ) z
      else zeta12 ^ k * starRingEnd ℂ (mobiusToZero (R : ℂ) z) := by
  induction k generalizing z with
  | zero => simp [v0Word]
  | succ k ih =>
    simp only [v0Word, hypWord_append, hypWord_cons, hypWord_nil]
    by_cases hev : k % 2 = 0
    · have hodd : (k + 1) % 2 ≠ 0 := by omega
      simp only [hev, ↓reduceIte, hodd]
      rw [ih (hypRefl_mem_ball 2 hz)]
      simp only [hev, ↓reduceIte, mobiusToZero_R_hypRefl2 hz, pow_succ]
      ring
    · have hev1 : (k + 1) % 2 = 0 := by omega
      simp only [hev, ↓reduceIte, hev1]
      rw [ih (hypRefl_mem_ball 0 hz)]
      simp only [hev, ↓reduceIte, mobiusToZero_R_hypRefl0 hz, map_mul, star_zeta12Inv,
        RingHomCompTriple.comp_apply, RingHom.id_apply, pow_succ]
      ring

lemma hypWord_v0Word_12 {z : ℂ} (hz : ‖z‖ < 1) : hypWord (v0Word 12) z = z := by
  have hm := mobiusToZero_R_v0Word 12 hz
  simp only [Nat.reduceMod, ↓reduceIte] at hm
  have h12 : zeta12 ^ 12 = 1 := by
    have : zeta12 ^ 12 = ((zeta12 ^ 2) ^ 3) ^ 2 := by ring
    rw [this, zeta12_pow_six]; norm_num
  rw [h12, one_mul] at hm
  have hR : ‖(R : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_of_nonneg R_pos.le] using R_lt_one
  have := congrArg (mobiusToZero (-(R : ℂ))) hm
  rwa [mobiusToZero_inv hR (hypWord_mem_ball _ hz), mobiusToZero_inv hR hz] at this

lemma eucWord_v0Word_6 (w : ℂ) : eucWord (v0Word 6) w = w := by
  have h6 : v0Word 6 = [2, 0, 2, 0, 2, 0] := by decide
  rw [h6]
  simpa only [eucWord_cons, eucWord_nil, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply, id_eq] using eucRefl_rot20_cube w

lemma eucWord_v0Word_12 (w : ℂ) : eucWord (v0Word 12) w = w := by
  have h12 : v0Word 12 = v0Word 6 ++ v0Word 6 := by decide
  rw [h12, eucWord_append, eucWord_v0Word_6, eucWord_v0Word_6]

lemma hypWord_v0Word_6_eq_halfTurn {z : ℂ} (hz : ‖z‖ < 1) :
    mobiusToZero (R : ℂ) (hypWord (v0Word 6) z) = -mobiusToZero (R : ℂ) z := by
  have hm := mobiusToZero_R_v0Word 6 hz
  simp only [Nat.reduceMod, ↓reduceIte] at hm
  have h6 : zeta12 ^ 6 = -1 := by
    rw [show zeta12 ^ 6 = (zeta12 ^ 2) ^ 3 by ring, zeta12_pow_six]
  rw [hm, h6, neg_one_mul]

lemma hypWord_v0Word_fix_R (k : ℕ) : hypWord (v0Word k) (vert1 0) = vert1 0 := by
  have hR : ‖vert1 0‖ < 1 := vert1_mem_ball 0
  have hR' : ‖(R : ℂ)‖ < 1 := by simpa [vert1] using hR
  have hm := mobiusToZero_R_v0Word k hR
  have hm0 : mobiusToZero (R : ℂ) (vert1 0) = 0 := by simp [mobiusToZero, vert1]
  rw [hm0, map_zero, mul_zero, ite_self] at hm
  have := congrArg (mobiusToZero (-(R : ℂ))) hm
  rw [mobiusToZero_inv hR' (hypWord_mem_ball _ hR), ← hm0, mobiusToZero_inv hR' hR] at this
  exact this

lemma eucWord_v0Word_fix_cAG (k : ℕ) : eucWord (v0Word k) (vert2 0) = vert2 0 := by
  have h0 : eucRefl 0 (vert2 0) = vert2 0 := by
    simp only [eucRefl, vert2, Fin.val_zero, pow_zero, one_mul, Complex.conj_ofReal]; ring
  have h2 : eucRefl 2 (vert2 0) = vert2 0 := by
    simp only [eucRefl, vert2, Fin.val_zero, pow_zero, one_mul, Complex.conj_ofReal]; ring
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [v0Word, eucWord_append, eucWord_cons, eucWord_nil]
    split_ifs <;> simp [h0, h2, ih]

lemma mem_v0Word_W0_iff (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    mobiusToZero (R : ℂ) (hypWord (v0Word k).reverse z) ∈ W0 ↔
      zeta12Inv ^ k * mobiusToZero (R : ℂ) z ∈ W0 := by
  have hr : ‖hypWord (v0Word k).reverse z‖ < 1 := hypWord_mem_ball _ hz
  have hm := mobiusToZero_R_v0Word k hr
  rw [hypWord_reverse_right (v0Word k) hz] at hm
  set w := mobiusToZero (R : ℂ) z
  set w' := mobiusToZero (R : ℂ) (hypWord (v0Word k).reverse z)
  have hmul : zeta12Inv ^ k * zeta12 ^ k = 1 := by
    rw [← mul_pow, mul_comm, zeta12_mul_conj, one_pow]
  by_cases hev : k % 2 = 0
  · simp only [hev, ↓reduceIte] at hm
    have hw' : w' = zeta12Inv ^ k * w := by rw [hm, ← mul_assoc, hmul, one_mul]
    rw [hw']
  · simp only [hev, ↓reduceIte] at hm
    have hw' : starRingEnd ℂ w' = zeta12Inv ^ k * w := by rw [hm, ← mul_assoc, hmul, one_mul]
    rw [← conj_mem_W0_iff, hw']

/-- Every complex number lies in one of the 12 rotated wedges `zeta12^k * W0`. -/
lemma exists_sector_W0 (w : ℂ) : ∃ k : Fin 12, zeta12Inv ^ (k : ℕ) * w ∈ W0 := by
  by_cases hw : w = 0
  · subst hw; exact ⟨0, by simp [W0]⟩
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set θ : ℝ := Complex.arg (-w)
  have hθ_gt : -Real.pi < θ := Complex.neg_pi_lt_arg (-w)
  have hθ_le : θ ≤ Real.pi := Complex.arg_le_pi (-w)
  have hpolar : w = -((‖w‖ : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
    have h1 := Complex.norm_mul_exp_arg_mul_I (-w)
    rw [norm_neg] at h1
    linear_combination h1
  -- Pick `m : ℤ = ⌊(θ + π / 12) / (π / 6)⌋` so `θ - m * (π / 6) ∈ [-π / 12, π / 12]`!
  set m : ℤ := ⌊(θ + Real.pi / 12) / (Real.pi / 6)⌋
  have hm_le : (m : ℝ) ≤ (θ + Real.pi / 12) / (Real.pi / 6) := Int.floor_le _
  have hm_gt : (θ + Real.pi / 12) / (Real.pi / 6) - 1 < (m : ℝ) := Int.sub_one_lt_floor _
  have hpi6 : 0 < Real.pi / 6 := by positivity
  set α : ℝ := θ - (m : ℝ) * (Real.pi / 6)
  have hα_lo : -(Real.pi / 12) ≤ α := by
    have : (m : ℝ) * (Real.pi / 6) ≤ θ + Real.pi / 12 := (le_div_iff₀ hpi6).mp hm_le
    dsimp only [α]; linarith
  have hα_hi : α ≤ Real.pi / 12 := by
    have : θ + Real.pi / 12 - Real.pi / 6 < (m : ℝ) * (Real.pi / 6) := by
      have := (div_lt_iff₀ hpi6).mp (by linarith : (θ + Real.pi / 12) / (Real.pi / 6) < (m : ℝ) + 1)
      linarith
    dsimp only [α]; linarith
  set k : Fin 12 := ⟨(m % 12).toNat, by
    have h1 : 0 ≤ m % 12 := Int.emod_nonneg m (by norm_num)
    have h2 : m % 12 < 12 := Int.emod_lt_of_pos m (by norm_num)
    omega⟩
  refine ⟨k, ?_⟩
  have hk_eq : zeta12Inv ^ (k : ℕ) = Complex.exp (((-(m : ℝ) * (Real.pi / 6) : ℝ) : ℂ) * I) := by
    rw [zeta12Inv_eq_exp, ← Complex.exp_nat_mul]
    have hmod : ∃ q : ℤ, (k : ℤ) - m = 12 * q := by
      refine ⟨-(m / 12), ?_⟩
      have h1 : (k : ℤ) = m % 12 := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))
      omega
    obtain ⟨q, hq⟩ := hmod
    have hdiff : ((k : ℕ) : ℂ) * ((-(Real.pi / 6) : ℝ) : ℂ) * I =
        ((-(m : ℝ) * (Real.pi / 6) : ℝ) : ℂ) * I + (-q : ℤ) * (2 * Real.pi * I) := by
      have hq' : ((k : ℕ) : ℂ) - (m : ℂ) = 12 * (q : ℂ) := by exact_mod_cast hq
      push_cast
      linear_combination -(Real.pi / 6 : ℂ) * I * hq'
    rw [← mul_assoc, hdiff, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hval : zeta12Inv ^ (k : ℕ) * w = -((‖w‖ : ℂ) * Complex.exp ((α : ℂ) * I)) := by
    conv_lhs => rw [hk_eq, hpolar]
    have : Complex.exp (((-(m : ℝ) * (Real.pi / 6) : ℝ) : ℂ) * I) *
        (-((‖w‖ : ℂ) * Complex.exp ((θ : ℂ) * I))) =
        -((‖w‖ : ℂ) * (Complex.exp (((-(m : ℝ) * (Real.pi / 6) : ℝ) : ℂ) * I) *
          Complex.exp ((θ : ℂ) * I))) := by ring
    rw [this, ← Complex.exp_add]
    have hexp_eq : Complex.exp (((-(m : ℝ) * (Real.pi / 6) : ℝ) : ℂ) * I + (θ : ℂ) * I) =
        Complex.exp ((α : ℂ) * I) := by
      congr 1; simp only [α]; push_cast; ring
    rw [hexp_eq]
  rw [hval]
  unfold W0; simp only [mem_ofPred_eq]
  have hsin_add : ∀ β : ℝ,
      ((-((‖w‖ : ℂ) * Complex.exp ((α : ℂ) * I))) * (1 + Complex.exp ((β : ℂ) * I))).im =
        -‖w‖ * (Real.sin α + Real.sin (α + β)) := by
    intro β
    have hcexp : Complex.exp ((α : ℂ) * I) * Complex.exp ((β : ℂ) * I) =
        Complex.exp (((α + β : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have h1 : (-((‖w‖ : ℂ) * Complex.exp ((α : ℂ) * I))) * (1 + Complex.exp ((β : ℂ) * I)) =
        -((‖w‖ : ℂ) * (Complex.exp ((α : ℂ) * I) + Complex.exp (((α + β : ℝ) : ℂ) * I))) := by
      linear_combination -((‖w‖ : ℂ) * hcexp)
    rw [h1, neg_im, Complex.im_ofReal_mul, add_im, Complex.exp_ofReal_mul_I_im,
      Complex.exp_ofReal_mul_I_im]
    ring
  constructor
  · rw [zeta12_eq_exp, hsin_add]
    have hsum : Real.sin α + Real.sin (α + Real.pi / 6) =
        2 * Real.sin (α + Real.pi / 12) * Real.cos (Real.pi / 12) := by
      rw [Real.sin_add_sin]
      have h1 : (α + (α + Real.pi / 6)) / 2 = α + Real.pi / 12 := by ring
      have h2 : (α - (α + Real.pi / 6)) / 2 = -(Real.pi / 12) := by ring
      rw [h1, h2, Real.cos_neg]
    rw [hsum]
    have hsin_nn : 0 ≤ Real.sin (α + Real.pi / 12) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
    have hcos_nn : 0 ≤ Real.cos (Real.pi / 12) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    nlinarith [mul_nonneg hsin_nn hcos_nn]
  · rw [zeta12Inv_eq_exp, hsin_add]
    have hsum : Real.sin α + Real.sin (α + -(Real.pi / 6)) =
        2 * Real.sin (α - Real.pi / 12) * Real.cos (Real.pi / 12) := by
      rw [Real.sin_add_sin]
      have h1 : (α + (α + -(Real.pi / 6))) / 2 = α - Real.pi / 12 := by ring
      have h2 : (α - (α + -(Real.pi / 6))) / 2 = Real.pi / 12 := by ring
      rw [h1, h2]
    rw [hsum]
    have hsin_np : Real.sin (α - Real.pi / 12) ≤ 0 := by
      have : Real.sin (Real.pi / 12 - α) ≥ 0 :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
      rw [show α - Real.pi / 12 = -(Real.pi / 12 - α) by ring, Real.sin_neg]
      linarith
    have hcos_nn : 0 ≤ Real.cos (Real.pi / 12) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hsin_np hcos_nn]

/-- If `w ≠ 0` lies in two distinct sectors `k₁, k₂ : Fin 12`, they must be adjacent (`k₂ = k₁ + 1` or `k₁ = k₂ + 1` mod 12),
    and `w` lies on their shared boundary ray. -/
lemma sector_W0_overlap {w : ℂ} (hw : w ≠ 0) {k₁ k₂ : Fin 12} (hne : k₁ ≠ k₂)
    (h1 : zeta12Inv ^ (k₁ : ℕ) * w ∈ W0) (h2 : zeta12Inv ^ (k₂ : ℕ) * w ∈ W0) :
    ((k₂.val = (k₁.val + 1) % 12) ∧ (zeta12Inv ^ (k₁ : ℕ) * w * (1 + zeta12Inv)).im = 0) ∨
    ((k₁.val = (k₂.val + 1) % 12) ∧ (zeta12Inv ^ (k₂ : ℕ) * w * (1 + zeta12Inv)).im = 0) := by
  -- Helper: any `v ∈ W0` with `v ≠ 0` has `arg (-v) ∈ [-π/12, π/12]`,
  -- and `(v * (1 + zeta12Inv)).im = 0 ↔ arg (-v) = π/12` (and `(v * (1 + zeta12)).im = 0 ↔ arg (-v) = -π/12`)!
  have harg_W0 : ∀ v : ℂ, v ≠ 0 → v ∈ W0 →
      -(Real.pi / 12) ≤ Complex.arg (-v) ∧ Complex.arg (-v) ≤ Real.pi / 12 ∧
      ((v * (1 + zeta12Inv)).im = 0 ↔ Complex.arg (-v) = Real.pi / 12) := by
    intro v hv hvW
    have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    set β : ℝ := Complex.arg (-v)
    have hβ_gt : -Real.pi < β := Complex.neg_pi_lt_arg (-v)
    have hβ_le : β ≤ Real.pi := Complex.arg_le_pi (-v)
    have hp : v = -((‖v‖ : ℂ) * Complex.exp ((β : ℂ) * I)) := by
      have := Complex.norm_mul_exp_arg_mul_I (-v); rw [norm_neg] at this; linear_combination this
    have hsin_id : ∀ γ : ℝ, (v * (1 + Complex.exp ((γ : ℂ) * I))).im =
        -‖v‖ * (Real.sin β + Real.sin (β + γ)) := by
      intro γ
      have hcexp : Complex.exp ((β : ℂ) * I) * Complex.exp ((γ : ℂ) * I) =
          Complex.exp (((β + γ : ℝ) : ℂ) * I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      have h1 : v * (1 + Complex.exp ((γ : ℂ) * I)) =
          -((‖v‖ : ℂ) * (Complex.exp ((β : ℂ) * I) + Complex.exp (((β + γ : ℝ) : ℂ) * I))) := by
        conv_lhs => rw [hp]
        linear_combination -((‖v‖ : ℂ) * hcexp)
      rw [h1, neg_im, Complex.im_ofReal_mul, add_im, Complex.exp_ofReal_mul_I_im,
        Complex.exp_ofReal_mul_I_im]; ring
    have hcos_pos : 0 < Real.cos (Real.pi / 12) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hW1 : 0 ≤ Real.sin (β + Real.pi / 12) := by
      have hv1 := hvW.1
      rw [zeta12_eq_exp, hsin_id, Real.sin_add_sin] at hv1
      have h1 : (β + (β + Real.pi / 6)) / 2 = β + Real.pi / 12 := by ring
      have h2 : (β - (β + Real.pi / 6)) / 2 = -(Real.pi / 12) := by ring
      rw [h1, h2, Real.cos_neg] at hv1
      nlinarith [mul_pos hnv hcos_pos]
    have hW2_eq : (v * (1 + zeta12Inv)).im = -2 * ‖v‖ * Real.cos (Real.pi / 12) * Real.sin (β - Real.pi / 12) := by
      rw [zeta12Inv_eq_exp, hsin_id, Real.sin_add_sin]
      have h1 : (β + (β + -(Real.pi / 6))) / 2 = β - Real.pi / 12 := by ring
      have h2 : (β - (β + -(Real.pi / 6))) / 2 = Real.pi / 12 := by ring
      rw [h1, h2]; ring
    have hW2 : Real.sin (β - Real.pi / 12) ≤ 0 := by
      have hv2 := hvW.2; rw [hW2_eq] at hv2; nlinarith [mul_pos hnv hcos_pos]
    -- Check `-(π/12) ≤ β ≤ π/12` from `sin(β + π/12) ≥ 0` and `sin(β - π/12) ≤ 0` and `β ∈ (-π, π]`!
    have hβ_lo : -(Real.pi / 12) ≤ β := by
      by_contra hlt; push Not at hlt
      by_cases hbig : -(11 * Real.pi / 12) ≤ β
      · have hneg : Real.sin (β + Real.pi / 12) < 0 := by
          rw [show β + Real.pi / 12 = -(-(β + Real.pi / 12)) by ring, Real.sin_neg]
          have := Real.sin_pos_of_pos_of_lt_pi (x := -(β + Real.pi / 12)) (by linarith) (by linarith)
          linarith
        linarith
      · push Not at hbig
        -- `β ∈ (-π, -11π/12)`: then `β - π/12 ∈ (-13π/12, -π)`, so `β - π/12 + 2π ∈ (11π/12, π)`, `sin > 0`!
        have hpos : 0 < Real.sin (β - Real.pi / 12) := by
          rw [show β - Real.pi / 12 = (β - Real.pi / 12 + 2 * Real.pi) - 2 * Real.pi by ring,
            Real.sin_sub_two_pi]
          exact Real.sin_pos_of_pos_of_lt_pi (x := β - Real.pi / 12 + 2 * Real.pi)
            (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        linarith
    have hβ_hi : β ≤ Real.pi / 12 := by
      by_contra hgt; push Not at hgt
      by_cases hsmall : β ≤ 11 * Real.pi / 12
      · have hpos : 0 < Real.sin (β - Real.pi / 12) :=
          Real.sin_pos_of_pos_of_lt_pi (x := β - Real.pi / 12) (by linarith) (by linarith)
        linarith
      · push Not at hsmall
        -- `β ∈ (11π/12, π]`: then `β + π/12 ∈ (π, 13π/12]`, `sin < 0`!
        have hneg : Real.sin (β + Real.pi / 12) < 0 := by
          rw [show β + Real.pi / 12 = (β + Real.pi / 12 - Real.pi) + Real.pi by ring, Real.sin_add_pi]
          have := Real.sin_pos_of_pos_of_lt_pi (x := β + Real.pi / 12 - Real.pi)
            (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
          linarith
        linarith
    refine ⟨hβ_lo, hβ_hi, ?_⟩
    rw [hW2_eq]
    constructor
    · intro hz0
      have hs0 : Real.sin (β - Real.pi / 12) = 0 := by
        have hcoef : -2 * ‖v‖ * Real.cos (Real.pi / 12) ≠ 0 := by nlinarith
        exact (mul_eq_zero.mp hz0).resolve_left hcoef
      by_contra hne_β
      have hlt : β < Real.pi / 12 := lt_of_le_of_ne hβ_hi hne_β
      have hneg : Real.sin (β - Real.pi / 12) < 0 := by
        rw [show β - Real.pi / 12 = -(Real.pi / 12 - β) by ring, Real.sin_neg]
        have := Real.sin_pos_of_pos_of_lt_pi (x := Real.pi / 12 - β) (by linarith) (by linarith [Real.pi_pos])
        linarith
      linarith
    · intro hβeq; rw [hβeq, sub_self, Real.sin_zero, mul_zero]
  have hne_z12 : zeta12Inv ≠ 0 := by
    intro h; have := zeta12_mul_conj; rw [h, mul_zero] at this; norm_num at this
  set v₁ := zeta12Inv ^ (k₁ : ℕ) * w
  set v₂ := zeta12Inv ^ (k₂ : ℕ) * w
  have hv1_ne : v₁ ≠ 0 := mul_ne_zero (pow_ne_zero _ hne_z12) hw
  have hv2_ne : v₂ ≠ 0 := mul_ne_zero (pow_ne_zero _ hne_z12) hw
  obtain ⟨h1_lo, h1_hi, h1_iff⟩ := harg_W0 v₁ hv1_ne h1
  obtain ⟨h2_lo, h2_hi, h2_iff⟩ := harg_W0 v₂ hv2_ne h2
  -- Relate `v₁` and `v₂`: `v₂ = zeta12Inv^(k₂ - k₁) * v₁`!
  set β₁ := Complex.arg (-v₁)
  set β₂ := Complex.arg (-v₂)
  have hrel : Complex.exp (((β₂ - β₁ : ℝ) : ℂ) * I) =
      Complex.exp (((((k₁.val : ℝ) - (k₂.val : ℝ)) * (Real.pi / 6) : ℝ) : ℂ) * I) := by
    have hnorm1 : ‖-v₁‖ = ‖w‖ := by
      rw [norm_neg, norm_mul, norm_pow]
      have hn : ‖zeta12Inv‖ = 1 := by rw [zeta12Inv_eq_exp, Complex.norm_exp_ofReal_mul_I]
      rw [hn, one_pow, one_mul]
    have hnorm2 : ‖-v₂‖ = ‖w‖ := by
      rw [norm_neg, norm_mul, norm_pow]
      have hn : ‖zeta12Inv‖ = 1 := by rw [zeta12Inv_eq_exp, Complex.norm_exp_ofReal_mul_I]
      rw [hn, one_pow, one_mul]
    have hp1 := Complex.norm_mul_exp_arg_mul_I (-v₁)
    have hp2 := Complex.norm_mul_exp_arg_mul_I (-v₂)
    rw [hnorm1] at hp1; rw [hnorm2] at hp2
    have hpow_rel : (-v₂) = Complex.exp (((((k₁.val : ℝ) - (k₂.val : ℝ)) * (Real.pi / 6) : ℝ) : ℂ) * I) * (-v₁) := by
      simp only [v₁, v₂, mul_neg, neg_inj, zeta12Inv_eq_exp, ← Complex.exp_nat_mul, ← mul_assoc,
        ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [← hp1, ← hp2] at hpow_rel
    have hnw_ne : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
    have hexp_eq : Complex.exp ((β₂ : ℂ) * I) =
        Complex.exp (((((k₁.val : ℝ) - (k₂.val : ℝ)) * (Real.pi / 6) : ℝ) : ℂ) * I) *
        Complex.exp ((β₁ : ℂ) * I) := by
      apply mul_left_cancel₀ hnw_ne
      linear_combination hpow_rel
    rw [show ((β₂ - β₁ : ℝ) : ℂ) * I = (β₂ : ℂ) * I + (-(β₁ : ℂ) * I) by push_cast; ring,
      Complex.exp_add, hexp_eq, mul_assoc, ← Complex.exp_add]
    simp
  -- Therefore `(β₂ - β₁) - (k₁ - k₂) * (π / 6) = 2 π * q` for some `q : ℤ`!
  have h2pi := Complex.exp_eq_exp_iff_exists_int.mp hrel
  obtain ⟨q, hq⟩ := h2pi
  have hreal : β₂ - β₁ = ((k₁.val : ℝ) - (k₂.val : ℝ)) * (Real.pi / 6) + (q : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im hq
    simp only [mul_im, ofReal_re, ofReal_im, I_re, I_im, add_im, intCast_re, intCast_im,
      mul_one, mul_zero, add_zero, zero_add, re_ofNat, im_ofNat, mul_re, sub_zero] at this
    linarith
  -- Multiply by `6 / π`: `(k₁ - k₂) + 12 q = 6 (β₂ - β₁) / π ∈ [-1, 1]`!
  set d : ℤ := (k₁.val : ℤ) - (k₂.val : ℤ) + 12 * q
  have hd_real : (d : ℝ) * (Real.pi / 6) = β₂ - β₁ := by
    simp only [d]; push_cast; linarith
  have hd_lo : -(1 : ℤ) ≤ d := by
    have : -(1 : ℝ) ≤ (d : ℝ) := by nlinarith [Real.pi_pos]
    exact_mod_cast this
  have hd_hi : d ≤ 1 := by
    have : (d : ℝ) ≤ 1 := by nlinarith [Real.pi_pos]
    exact_mod_cast this
  have hd_ne0 : d ≠ 0 := by
    intro hd0
    have hk1 := k₁.isLt; have hk2 := k₂.isLt
    have hkeq : k₁.val = k₂.val := by omega
    exact hne (Fin.ext hkeq)
  have hcases : d = -1 ∨ d = 1 := by omega
  rcases hcases with hd_neg | hd_pos
  · left
    have hmod : k₂.val = (k₁.val + 1) % 12 := by have := k₁.isLt; have := k₂.isLt; omega
    have hβ_diff : β₂ - β₁ = -(Real.pi / 6) := by rw [← hd_real, hd_neg]; push_cast; ring
    have hβ1 : β₁ = Real.pi / 12 := by linarith
    exact ⟨hmod, h1_iff.mpr hβ1⟩
  · right
    have hmod : k₁.val = (k₂.val + 1) % 12 := by have := k₁.isLt; have := k₂.isLt; omega
    have hβ_diff : β₂ - β₁ = Real.pi / 6 := by rw [← hd_real, hd_pos]; push_cast; ring
    have hβ2 : β₂ = Real.pi / 12 := by linarith
    exact ⟨hmod, h2_iff.mpr hβ2⟩

/-- Holomorphic extension of `φ` to a hyperbolic ball `hypBall (vert1 0) δ_v` around `vert1 0 = R`,
    with `deriv φ_v0 (vert1 0) = 0`. -/
lemma φ_vertex0_extension :
    ∃ (δ_v : ℝ) (φ_v0 : ℂ → ℂ), 0 < δ_v ∧ δ_v ≤ 1 / 4 ∧
      (∀ z ∈ hypBall (vert1 0) δ_v, ‖sideCenter 1‖ ^ 2 - 1 < ‖z - sideCenter 1‖ ^ 2) ∧
      (∀ k : Fin 3, k ≠ 0 → Disjoint (hypBall (vert1 0) δ_v) (hypBall (vert1 k) δ_v)) ∧
      DifferentiableOn ℂ φ_v0 (hypBall (vert1 0) δ_v) ∧
      deriv φ_v0 (vert1 0) = 0 ∧
      hypBall (vert1 0) δ_v ⊆ ⋃ (k : Fin 12), hypWord (v0Word k.val) '' Δ1 ∧
      (∀ (k : Fin 12) (z : ℂ), z ∈ hypBall (vert1 0) δ_v →
        z ∈ hypWord (v0Word k.val) '' Δ1 → φ_v0 z = chartMap (v0Word k.val) φ z) := by
  classical
  -- Step 1: Pick `δ_v ∈ (0, 1/4]` small enough that:
  -- (a) `hypBall (vert1 0) δ_v` stays strictly inside side 1;
  -- (b) `hypBall (vert1 0) δ_v` is disjoint from `hypBall (vert1 k) δ_v` for `k ≠ 0`!
  have hside1_open : IsOpen {z : ℂ | ‖sideCenter 1‖ ^ 2 - 1 < ‖z - sideCenter 1‖ ^ 2} :=
    isOpen_Ioi.preimage ((continuous_id.sub continuous_const).norm.pow 2)
  obtain ⟨r1, hr1_pos, hr1_sub⟩ := Metric.isOpen_iff.mp hside1_open (vert1 0) vert1_zero_strict_side1
  have hsep_v : 0 < min (hypDist (vert1 0) (vert1 1)) (hypDist (vert1 0) (vert1 2)) := by
    refine lt_min ?_ ?_
    · refine lt_of_le_of_ne (hypDist_nonneg _ _) (Ne.symm fun h0 => ?_)
      have heq := (hypDist_eq_zero_iff (vert1_mem_ball 0) (vert1_mem_ball 1)).mp h0
      have him := congrArg Complex.im heq
      simp only [vert1, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, ofReal_im, mul_im,
        ω_re, ω_im, ofReal_re, mul_zero] at him
      nlinarith [R_pos, sqrt3_pos]
    · refine lt_of_le_of_ne (hypDist_nonneg _ _) (Ne.symm fun h0 => ?_)
      have heq := (hypDist_eq_zero_iff (vert1_mem_ball 0) (vert1_mem_ball 2)).mp h0
      have him := congrArg Complex.im heq
      simp only [vert1, Fin.val_zero, Fin.val_two, pow_zero, one_mul, ofReal_im, ω_sq, mul_im,
        ofReal_re, mul_zero] at him
      nlinarith [R_pos, sqrt3_pos]
  set δ_v : ℝ := min (1 / 4) (min (r1 / 2) (min (hypDist (vert1 0) (vert1 1)) (hypDist (vert1 0) (vert1 2)) / 3))
  have hδ_pos : 0 < δ_v := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hδ_le : δ_v ≤ 1 / 4 := min_le_left _ _
  have hside1_hb : ∀ z ∈ hypBall (vert1 0) δ_v, ‖sideCenter 1‖ ^ 2 - 1 < ‖z - sideCenter 1‖ ^ 2 := by
    intro z ⟨hz1, hdist⟩
    refine hr1_sub ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have hden_le : ‖1 - starRingEnd ℂ (vert1 0) * z‖ ≤ 2 := by
      calc ‖1 - starRingEnd ℂ (vert1 0) * z‖ ≤ ‖(1 : ℂ)‖ + ‖starRingEnd ℂ (vert1 0) * z‖ := norm_sub_le _ _
        _ = 1 + ‖vert1 0‖ * ‖z‖ := by rw [norm_one, norm_mul, RCLike.norm_conj]
        _ ≤ 1 + 1 * 1 := by nlinarith [vert1_mem_ball 0, hz1, norm_nonneg (vert1 0), norm_nonneg z]
        _ = 2 := by norm_num
    have hden_pos : 0 < ‖1 - starRingEnd ℂ (vert1 0) * z‖ :=
      norm_pos_iff.mpr (one_sub_conj_mul_ne_zero hz1 (vert1_mem_ball 0))
    unfold hypDist at hdist
    rw [norm_div, div_lt_iff₀ hden_pos] at hdist
    have hle : δ_v ≤ r1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
    nlinarith
  have hdisj_v : ∀ k : Fin 3, k ≠ 0 → Disjoint (hypBall (vert1 0) δ_v) (hypBall (vert1 k) δ_v) := by
    intro k hk
    rw [Set.disjoint_iff]
    intro z ⟨⟨hz1, hd0⟩, ⟨_, hdk⟩⟩
    have htri := hypDist_triangle (vert1_mem_ball 0) hz1 (vert1_mem_ball k)
    rw [hypDist_comm (vert1 0) z] at htri
    have hle : 3 * δ_v ≤ hypDist (vert1 0) (vert1 k) := by
      have h1 : δ_v ≤ min (hypDist (vert1 0) (vert1 1)) (hypDist (vert1 0) (vert1 2)) / 3 :=
        (min_le_right _ _).trans (min_le_right _ _)
      fin_cases k
      · exact absurd rfl hk
      · change 3 * δ_v ≤ hypDist (vert1 0) (vert1 1)
        have := min_le_left (hypDist (vert1 0) (vert1 1)) (hypDist (vert1 0) (vert1 2)); linarith
      · change 3 * δ_v ≤ hypDist (vert1 0) (vert1 2)
        have := min_le_right (hypDist (vert1 0) (vert1 1)) (hypDist (vert1 0) (vert1 2)); linarith
    linarith
  -- Notice `hypBall (vert1 0) δ_v` is invariant under EVERY `hypWord (v0Word k)` and its reverse!
  have hhb_v0_inv : ∀ (k : ℕ) {z : ℂ}, z ∈ hypBall (vert1 0) δ_v →
      hypWord (v0Word k).reverse z ∈ hypBall (vert1 0) δ_v := by
    intro k z ⟨hz1, hdist⟩
    refine ⟨hypWord_mem_ball _ hz1, ?_⟩
    have hfix : hypWord (v0Word k).reverse (vert1 0) = vert1 0 := by
      have := congrArg (hypWord (v0Word k).reverse) (hypWord_v0Word_fix_R k)
      rw [hypWord_reverse_left _ (vert1_mem_ball 0)] at this
      exact this.symm
    rw [← hfix, hypDist_hypWord _ hz1 (vert1_mem_ball 0)]
    exact hdist
  -- Inside `hypBall (vert1 0) δ_v`, `z ∈ hypWord (v0Word k) '' Δ1` iff `zeta12Inv^k * mobiusToZero R z ∈ W0`!
  have hmem_sector_iff : ∀ (k : ℕ) {z : ℂ}, z ∈ hypBall (vert1 0) δ_v →
      (z ∈ hypWord (v0Word k) '' Δ1 ↔ zeta12Inv ^ k * mobiusToZero (R : ℂ) z ∈ W0) := by
    intro k z hz
    have hrev_hb := hhb_v0_inv k hz
    rw [← mem_v0Word_W0_iff k hz.1, mem_W0_iff_sides hrev_hb.1]
    constructor
    · rintro ⟨x, hxΔ, rfl⟩
      rw [hypWord_reverse_left _ hxΔ.1]
      exact ⟨hxΔ.2 0, hxΔ.2 2⟩
    · rintro ⟨hs0, hs2⟩
      refine ⟨hypWord (v0Word k).reverse z, ⟨hrev_hb.1, fun j => ?_⟩, hypWord_reverse_right _ hz.1⟩
      fin_cases j
      · exact hs0
      · exact (hside1_hb _ hrev_hb).le
      · exact hs2
  -- Covering property: `hypBall (vert1 0) δ_v ⊆ ⋃ k : Fin 12, hypWord (v0Word k) '' Δ1`!
  have hcov : hypBall (vert1 0) δ_v ⊆ ⋃ (k : Fin 12), hypWord (v0Word k.val) '' Δ1 := by
    intro z hz
    obtain ⟨k, hk⟩ := exists_sector_W0 (mobiusToZero (R : ℂ) z)
    exact mem_iUnion.mpr ⟨k, (hmem_sector_iff k.val hz).mpr hk⟩
  -- Key relation for adjacent sectors `k` and `(k + 1) % 12`:
  -- `j_k := if k % 2 = 0 then 2 else 0` satisfies `hypWord (v0Word ((k+1)%12)) = hypWord (v0Word k ++ [j_k])`
  -- and `eucWord (v0Word ((k+1)%12)) = eucWord (v0Word k ++ [j_k])`!
  have hadj_words : ∀ (k : Fin 12),
      let j : Fin 3 := if k.val % 2 = 0 then 2 else 0
      (∀ z : ℂ, ‖z‖ < 1 → hypWord (v0Word ((k.val + 1) % 12)) z = hypWord (v0Word k.val ++ [j]) z) ∧
      (∀ w : ℂ, eucWord (v0Word ((k.val + 1) % 12)) w = eucWord (v0Word k.val ++ [j]) w) := by
    intro k
    by_cases h11 : k.val = 11
    · simp only [h11, Nat.reduceAdd, Nat.mod_self, Nat.reduceMod]
      have h12_eq : v0Word 11 ++ [if 1 = 0 then (2 : Fin 3) else 0] = v0Word 12 := by decide
      refine ⟨fun z hz => by rw [h12_eq, hypWord_v0Word_12 hz]; rfl,
        fun w => by rw [h12_eq, eucWord_v0Word_12 w]; rfl⟩
    · have hlt : k.val + 1 < 12 := by have := k.isLt; omega
      rw [Nat.mod_eq_of_lt hlt]
      exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  -- Agreement of `chartMap (v0Word k₁) φ` and `chartMap (v0Word k₂) φ` on overlaps inside `hypBall (vert1 0) δ_v`!
  -- First prove: on side `j` of `Δ1`, `chartMap [j] φ x = φ x`!
  have hchart_side_eq : ∀ (j : Fin 3) {x : ℂ}, x ∈ Δ1 →
      ‖x - sideCenter j‖ ^ 2 = ‖sideCenter j‖ ^ 2 - 1 →
      chartMap [j] φ x = φ x := by
    intro j x hxΔ hsj
    by_cases hother : ∀ i : Fin 3, i ≠ j → ‖sideCenter i‖ ^ 2 - 1 < ‖x - sideCenter i‖ ^ 2
    · obtain ⟨ρ, ψ, hρ, _, _, _, _, hΔ, hR⟩ := φ_side_extension j hxΔ hsj hother
      have hx_hb : x ∈ hypBall x ρ := self_mem_hypBall hxΔ.1 hρ
      have hfix : hypRefl j x = x := (hypRefl_fixed_iff j hxΔ.1).mpr hsj
      have hxR : x ∈ hypRefl j '' Δ1 := ⟨x, hxΔ, hfix⟩
      rw [← hR x ⟨hx_hb, hxR⟩, hΔ x ⟨hx_hb, hxΔ⟩]
    · push Not at hother
      obtain ⟨i, hij, hle⟩ := hother
      have hsi : ‖x - sideCenter i‖ ^ 2 = ‖sideCenter i‖ ^ 2 - 1 := le_antisymm hle (hxΔ.2 i)
      -- `x` is a vertex on side `j`!
      have hv_case : (j = 0 ∧ (x = vert1 0 ∨ x = vert1 1)) ∨
          (j = 1 ∧ (x = vert1 1 ∨ x = vert1 2)) ∨
          (j = 2 ∧ (x = vert1 2 ∨ x = vert1 0)) := by
        fin_cases j <;> fin_cases i
        all_goals first
          | exact absurd rfl hij
          | exact Or.inl ⟨rfl, Or.inr (side0_inter_side1_eq_vert1 hxΔ.1 hsj hsi)⟩
          | exact Or.inl ⟨rfl, Or.inl ((side_inter_side_eq_vert1 (by decide : (2 : Fin 3) ≠ 0) hxΔ.1 hsi hsj).2.2 ⟨rfl, rfl⟩)⟩
          | exact Or.inr (Or.inl ⟨rfl, Or.inl (side0_inter_side1_eq_vert1 hxΔ.1 hsi hsj)⟩)
          | exact Or.inr (Or.inl ⟨rfl, Or.inr ((side_inter_side_eq_vert1 (by decide : (1 : Fin 3) ≠ 2) hxΔ.1 hsj hsi).2.1 ⟨rfl, rfl⟩)⟩)
          | exact Or.inr (Or.inr ⟨rfl, Or.inr ((side_inter_side_eq_vert1 (by decide : (2 : Fin 3) ≠ 0) hxΔ.1 hsj hsi).2.2 ⟨rfl, rfl⟩)⟩)
          | exact Or.inr (Or.inr ⟨rfl, Or.inl ((side_inter_side_eq_vert1 (by decide : (1 : Fin 3) ≠ 2) hxΔ.1 hsi hsj).2.1 ⟨rfl, rfl⟩)⟩)
      have hfix : hypRefl j x = x := (hypRefl_fixed_iff j hxΔ.1).mpr hsj
      simp only [chartMap, eucWord_cons, eucWord_nil, List.reverse_singleton, hypWord_cons,
        hypWord_nil, hfix]
      rcases hv_case with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩
      · rw [φ_vert 0]; simp [eucRefl, vert2]; ring
      · rw [φ_vert 1]; simp only [eucRefl, vert2, Fin.val_one, pow_one, map_mul, Complex.conj_ofReal,
          star_ω]; linear_combination -(cAG : ℂ) * ω_cube
      · rw [φ_vert 1]; simp only [eucRefl, vert2, Fin.val_one, pow_one, map_mul, Complex.conj_ofReal,
          star_ω]; linear_combination -(cAG : ℂ) * ω_sq_add_ω_add_one
      · rw [φ_vert 2]; simp only [eucRefl, vert2, Fin.val_two, map_mul, Complex.conj_ofReal,
          star_ω_sq]; linear_combination -(cAG : ℂ) * ω_sq_add_ω_add_one
      · rw [φ_vert 2]; simp only [eucRefl, vert2, Fin.val_two, map_mul, Complex.conj_ofReal,
          star_ω_sq]; linear_combination -(cAG : ℂ) * ω_cube
      · rw [φ_vert 0]; simp [eucRefl, vert2]; ring
  have hoverlap : ∀ (k₁ k₂ : Fin 12) {z : ℂ}, z ∈ hypBall (vert1 0) δ_v →
      z ∈ hypWord (v0Word k₁.val) '' Δ1 → z ∈ hypWord (v0Word k₂.val) '' Δ1 →
      chartMap (v0Word k₁.val) φ z = chartMap (v0Word k₂.val) φ z := by
    intro k₁ k₂ z hz h1 h2
    by_cases hzeq : z = vert1 0
    · subst hzeq
      have hfix : ∀ k : ℕ, chartMap (v0Word k) φ (vert1 0) = vert2 0 := by
        intro k
        have hrev : hypWord (v0Word k).reverse (vert1 0) = vert1 0 := by
          have := congrArg (hypWord (v0Word k).reverse) (hypWord_v0Word_fix_R k)
          rw [hypWord_reverse_left _ (vert1_mem_ball 0)] at this; exact this.symm
        simp only [chartMap, hrev, φ_vert 0, eucWord_v0Word_fix_cAG]
      rw [hfix, hfix]
    · by_cases hk : k₁ = k₂
      · rw [hk]
      · have hw_ne : mobiusToZero (R : ℂ) z ≠ 0 := by
          intro h0
          have hR' : ‖(R : ℂ)‖ < 1 := by simpa [vert1] using vert1_mem_ball 0
          have := congrArg (mobiusToZero (-(R : ℂ))) h0
          rw [mobiusToZero_inv hR' hz.1] at this
          simp only [mobiusToZero, zero_sub, neg_neg, mul_zero, sub_zero, div_one] at this
          exact hzeq (by simp [vert1, this])
        have hW1 := (hmem_sector_iff k₁.val hz).mp h1
        have hW2 := (hmem_sector_iff k₂.val hz).mp h2
        have hadj_case := sector_W0_overlap hw_ne hk hW1 hW2
        -- Helper: if `k' = (k + 1) % 12` and `(zeta12Inv^k * w * (1 + zeta12Inv)).im = 0`, then equal!
        have hstep : ∀ (ka kb : Fin 12), kb.val = (ka.val + 1) % 12 →
            (zeta12Inv ^ (ka : ℕ) * mobiusToZero (R : ℂ) z * (1 + zeta12Inv)).im = 0 →
            z ∈ hypWord (v0Word ka.val) '' Δ1 →
            chartMap (v0Word ka.val) φ z = chartMap (v0Word kb.val) φ z := by
          intro ka kb hkb him0 hka
          set j : Fin 3 := if ka.val % 2 = 0 then 2 else 0
          obtain ⟨hh, he⟩ := hadj_words ka
          have hkb_eq : v0Word kb.val = v0Word ((ka.val + 1) % 12) := by rw [hkb]
          set x := hypWord (v0Word ka.val).reverse z
          have hxΔ : x ∈ Δ1 := by
            obtain ⟨y, hyΔ, hyz⟩ := hka
            dsimp only [x]; rwa [← hyz, hypWord_reverse_left _ hyΔ.1]
          -- Show `x` lies on side `j` of `Δ1`!
          have hx_side : ‖x - sideCenter j‖ ^ 2 = ‖sideCenter j‖ ^ 2 - 1 := by
            have hm := mobiusToZero_R_v0Word ka.val hxΔ.1
            rw [show hypWord (v0Word ka.val) x = z from hypWord_reverse_right _ hz.1] at hm
            have hmul : zeta12Inv ^ (ka : ℕ) * zeta12 ^ (ka : ℕ) = 1 := by
              rw [← mul_pow, mul_comm, zeta12_mul_conj, one_pow]
            have hden_pos : 0 < ‖(1 : ℂ) + (R : ℂ) * mobiusToZero (R : ℂ) x‖ ^ 2 := by
              have hR' : ‖(R : ℂ)‖ < 1 := by simpa [vert1] using vert1_mem_ball 0
              have hRm : ‖-(R : ℂ)‖ < 1 := by simpa using hR'
              have hne : (1 : ℂ) + (R : ℂ) * mobiusToZero (R : ℂ) x ≠ 0 := by
                simpa [Complex.conj_ofReal] using one_sub_conj_mul_ne_zero (mobiusToZero_mem_ball hR' hxΔ.1) hRm
              positivity
            by_cases hev : ka.val % 2 = 0
            · simp only [hev, ↓reduceIte] at hm
              simp only [j, hev, ↓reduceIte]
              have hmx : mobiusToZero (R : ℂ) x = zeta12Inv ^ (ka : ℕ) * mobiusToZero (R : ℂ) z := by
                rw [hm, ← mul_assoc, hmul, one_mul]
              have hs2 := mobiusToZero_R_side2_sign hxΔ.1
              have hzero : (mobiusToZero (R : ℂ) x * (1 + zeta12Inv)).im = 0 := by rw [hmx, him0]
              rw [hzero, mul_zero] at hs2
              have := (mul_eq_zero.mp hs2).resolve_left hden_pos.ne'
              linarith
            · simp only [hev, ↓reduceIte] at hm
              simp only [j, hev, ↓reduceIte]
              have hmx : starRingEnd ℂ (mobiusToZero (R : ℂ) x) =
                  zeta12Inv ^ (ka : ℕ) * mobiusToZero (R : ℂ) z := by
                rw [hm, ← mul_assoc, hmul, one_mul]
              have him_x : (mobiusToZero (R : ℂ) x * (1 + zeta12)).im = 0 := by
                have hconj : starRingEnd ℂ (mobiusToZero (R : ℂ) x * (1 + zeta12)) =
                    starRingEnd ℂ (mobiusToZero (R : ℂ) x) * (1 + zeta12Inv) := by
                  have hst : starRingEnd ℂ zeta12 = zeta12Inv := by
                    rw [← star_zeta12Inv, RingHomCompTriple.comp_apply, RingHom.id_apply]
                  simp [hst]
                have := congrArg Complex.im hconj
                rw [conj_im, hmx, him0] at this; linarith
              have hs0 := mobiusToZero_R_side0_sign hxΔ.1
              rw [him_x, mul_zero] at hs0
              have := (mul_eq_zero.mp hs0).resolve_left hden_pos.ne'
              linarith
          -- Now `chartMap (v0Word kb) φ z = eucWord (v0Word ka) (chartMap [j] φ x) = eucWord (v0Word ka) (φ x)`!
          have hrev_kb : hypWord (v0Word kb.val).reverse z = hypRefl j x := by
            have h1 : hypWord (v0Word kb.val) (hypRefl j x) = z := by
              rw [hkb_eq, hh _ (hypRefl_mem_ball j hxΔ.1), hypWord_append, hypWord_cons, hypWord_nil,
                hypRefl_invol j hxΔ.1, hypWord_reverse_right _ hz.1]
            rw [← h1, hypWord_reverse_left _ (hypRefl_mem_ball j hxΔ.1)]
          simp only [chartMap]
          rw [hrev_kb, hkb_eq, he, eucWord_append, eucWord_cons, eucWord_nil]
          have hcs := hchart_side_eq j hxΔ hx_side
          simp only [chartMap, eucWord_cons, eucWord_nil, List.reverse_singleton, hypWord_cons,
            hypWord_nil] at hcs
          rw [hcs]
        rcases hadj_case with ⟨hmod, him0⟩ | ⟨hmod, him0⟩
        · exact hstep k₁ k₂ hmod him0 h1
        · exact (hstep k₂ k₁ hmod him0 h2).symm
  -- Define `φ_v0` on `hypBall (vert1 0) δ_v` via Classical.choose on the 12-sector cover!
  let φ_v0 : ℂ → ℂ := fun z =>
    if hz : z ∈ hypBall (vert1 0) δ_v then
      chartMap (v0Word (Classical.choose (mem_iUnion.mp (hcov hz))).val) φ z
    else 0
  have hφv0_eq : ∀ (k : Fin 12) (z : ℂ), z ∈ hypBall (vert1 0) δ_v →
      z ∈ hypWord (v0Word k.val) '' Δ1 → φ_v0 z = chartMap (v0Word k.val) φ z := by
    intro k z hz hk
    simp only [φ_v0, hz, ↓reduceDIte]
    exact hoverlap _ k hz (Classical.choose_spec (mem_iUnion.mp (hcov hz))) hk
  -- Continuity at `vert1 0` (finite union of 12 closed sectors!).
  have hcont0 : ContinuousAt φ_v0 (vert1 0) := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hval0 : φ_v0 (vert1 0) = vert2 0 := by
      rw [hφv0_eq 0 (vert1 0) (self_mem_hypBall (vert1_mem_ball 0) hδ_pos)
        ⟨vert1 0, vert1_mem_Δ1 0, rfl⟩]
      simp [v0Word, chartMap_nil, φ_vert 0]
    -- For each `k : Fin 12`, `chartMap (v0Word k) φ` is continuous on `hypWord (v0Word k) '' Δ1` at `vert1 0`!
    have hk_cont : ∀ k : Fin 12, ∃ r : ℝ, 0 < r ∧ ∀ z ∈ ball (vert1 0) r,
        z ∈ hypWord (v0Word k.val) '' Δ1 → dist (chartMap (v0Word k.val) φ z) (vert2 0) < ε := by
      intro k
      have hcomp_cont : ContinuousOn (chartMap (v0Word k.val) φ) (hypWord (v0Word k.val) '' Δ1) := by
        have hmaps : MapsTo (hypWord (v0Word k.val).reverse) (hypWord (v0Word k.val) '' Δ1) Δ1 := by
          rintro _ ⟨x, hxΔ, rfl⟩; rwa [hypWord_reverse_left _ hxΔ.1]
        have hsub : hypWord (v0Word k.val) '' Δ1 ⊆ ball 0 1 := by
          rintro _ ⟨x, hxΔ, rfl⟩
          simpa [Metric.mem_ball, dist_zero_right] using hypWord_mem_ball _ hxΔ.1
        exact (continuous_eucWord _).comp_continuousOn
          (φ_continuousOn.comp ((continuousOn_hypWord _).mono hsub) hmaps)
      have hv_mem : vert1 0 ∈ hypWord (v0Word k.val) '' Δ1 :=
        ⟨vert1 0, vert1_mem_Δ1 0, hypWord_v0Word_fix_R k.val⟩
      have hcw := hcomp_cont (vert1 0) hv_mem
      have hval_k : chartMap (v0Word k.val) φ (vert1 0) = vert2 0 := by
        have hrev : hypWord (v0Word k.val).reverse (vert1 0) = vert1 0 := by
          have := congrArg (hypWord (v0Word k.val).reverse) (hypWord_v0Word_fix_R k.val)
          rw [hypWord_reverse_left _ (vert1_mem_ball 0)] at this; exact this.symm
        simp only [chartMap, hrev, φ_vert 0, eucWord_v0Word_fix_cAG]
      rw [Metric.continuousWithinAt_iff] at hcw
      obtain ⟨r, hr, hball⟩ := hcw ε hε
      exact ⟨r, hr, fun z hz hzk => by rw [← hval_k]; exact hball hzk hz⟩
    choose rk hrk_pos hrk_dist using hk_cont
    obtain ⟨r_hb, hr_hb_pos, hr_hb_sub⟩ :=
      Metric.isOpen_iff.mp (isOpen_hypBall (vert1_mem_ball 0)) (vert1 0)
        (self_mem_hypBall (vert1_mem_ball 0) hδ_pos)
    set r_min : ℝ := min r_hb (Finset.univ.inf' Finset.univ_nonempty rk)
    have hr_min_pos : 0 < r_min := by
      refine lt_min hr_hb_pos ?_
      rw [Finset.lt_inf'_iff]; intro k _; exact hrk_pos k
    refine ⟨r_min, hr_min_pos, fun z hz => ?_⟩
    have hzhb : z ∈ hypBall (vert1 0) δ_v := hr_hb_sub (Metric.ball_subset_ball (min_le_left _ _) hz)
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov hzhb)
    rw [hval0, hφv0_eq k z hzhb hk]
    have hzk : z ∈ ball (vert1 0) (rk k) :=
      Metric.ball_subset_ball ((min_le_right _ _).trans (Finset.inf'_le rk (Finset.mem_univ k))) hz
    exact hrk_dist k z hzk hk
  -- Differentiability on `hypBall (vert1 0) δ_v \ {vert1 0}`!
  have hdiff_punc : DifferentiableOn ℂ φ_v0 (hypBall (vert1 0) δ_v \ {vert1 0}) := by
    intro z ⟨hzhb, hzne⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov hzhb)
    set x := hypWord (v0Word k.val).reverse z
    have hxΔ : x ∈ Δ1 := by
      obtain ⟨y, hyΔ, hyz⟩ := hk
      dsimp only [x]; rwa [← hyz, hypWord_reverse_left _ hyΔ.1]
    have hx_hb : x ∈ hypBall (vert1 0) δ_v := hhb_v0_inv k.val hzhb
    have hx_s1 : ‖sideCenter 1‖ ^ 2 - 1 < ‖x - sideCenter 1‖ ^ 2 := hside1_hb x hx_hb
    have hx_neR : x ≠ vert1 0 := by
      intro hxR; apply hzne
      dsimp only [x] at hxR
      rw [← hypWord_reverse_right (v0Word k.val) hzhb.1, hxR, hypWord_v0Word_fix_R]
      exact mem_singleton _
    by_cases hx_open : x ∈ Δ1Open
    · -- `z` lies in the open interior `hypWord (v0Word k) '' Δ1Open`!
      set Wz : Set ℂ := hypBall (vert1 0) δ_v ∩ hypWord (v0Word k.val).reverse ⁻¹' Δ1Open
      have hWz_open : IsOpen Wz :=
        ((continuousOn_hypWord _).mono (hypBall_subset_ball _ _)).isOpen_inter_preimage
          (isOpen_hypBall (vert1_mem_ball 0)) isOpen_Δ1Open
      have hz_Wz : z ∈ Wz := ⟨hzhb, hx_open⟩
      have heq_Wz : φ_v0 =ᶠ[𝓝 z] chartMap (v0Word k.val) φ := by
        filter_upwards [hWz_open.mem_nhds hz_Wz] with y ⟨hyhb, hyo⟩
        have hyΔ : hypWord (v0Word k.val).reverse y ∈ Δ1 := ⟨hyo.1, fun j => (hyo.2 j).le⟩
        exact hφv0_eq k y hyhb ⟨_, hyΔ, hypWord_reverse_right _ hyhb.1⟩
      have hdiff_c : DifferentiableAt ℂ (chartMap (v0Word k.val) φ) z :=
        chartMap_differentiableAt _ hzhb.1 (φ_differentiableOn.differentiableAt (isOpen_Δ1Open.mem_nhds hx_open))
      exact (hdiff_c.congr_of_eventuallyEq heq_Wz).differentiableWithinAt
    · -- `x ∈ Δ1 \ Δ1Open`, `x ≠ vert1 0`, strict side 1 -> `x` lies on open side 0 or open side 2!
      have hside02 : (‖x - sideCenter 0‖ ^ 2 = ‖sideCenter 0‖ ^ 2 - 1 ∧
            ‖sideCenter 2‖ ^ 2 - 1 < ‖x - sideCenter 2‖ ^ 2) ∨
          (‖x - sideCenter 2‖ ^ 2 = ‖sideCenter 2‖ ^ 2 - 1 ∧
            ‖sideCenter 0‖ ^ 2 - 1 < ‖x - sideCenter 0‖ ^ 2) := by
        have hnotall : ∃ j : Fin 3, ‖x - sideCenter j‖ ^ 2 = ‖sideCenter j‖ ^ 2 - 1 := by
          by_contra hall; push Not at hall
          exact hx_open ⟨hxΔ.1, fun j => lt_of_le_of_ne (hxΔ.2 j) (Ne.symm (hall j))⟩
        obtain ⟨j, hj⟩ := hnotall
        fin_cases j
        · left; refine ⟨hj, lt_of_le_of_ne (hxΔ.2 2) fun heq => hx_neR ?_⟩
          exact (side_inter_side_eq_vert1 (by decide : (2 : Fin 3) ≠ 0) hxΔ.1 heq.symm hj).2.2 ⟨rfl, rfl⟩
        · exact absurd hj hx_s1.ne'
        · right; refine ⟨hj, lt_of_le_of_ne (hxΔ.2 0) fun heq => hx_neR ?_⟩
          exact (side_inter_side_eq_vert1 (by decide : (2 : Fin 3) ≠ 0) hxΔ.1 hj heq.symm).2.2 ⟨rfl, rfl⟩
      -- Helper: given side `j ∈ {0, 2}` on which `x` lies strictly off other sides, use `φ_side_extension`!
      have hside_case : ∀ j : Fin 3, (j = 0 ∨ j = 2) →
          ‖x - sideCenter j‖ ^ 2 = ‖sideCenter j‖ ^ 2 - 1 →
          (∀ i : Fin 3, i ≠ j → ‖sideCenter i‖ ^ 2 - 1 < ‖x - sideCenter i‖ ^ 2) →
          DifferentiableWithinAt ℂ φ_v0 (hypBall (vert1 0) δ_v \ {vert1 0}) z := by
        intro j hj02 hxj hother
        obtain ⟨ρ, ψ, hρ, _, hψ_diff, _, hhb_cov, hψ_Δ1, hψ_R⟩ := φ_side_extension j hxΔ hxj hother
        -- Find the neighbor sector `k' : Fin 12` whose word acts as `v0Word k ++ [j]`!
        have hk'_ex : ∃ k' : Fin 12,
            (∀ u : ℂ, ‖u‖ < 1 → hypWord (v0Word k'.val) u = hypWord (v0Word k.val ++ [j]) u) ∧
            (∀ u : ℂ, eucWord (v0Word k'.val) u = eucWord (v0Word k.val ++ [j]) u) := by
          by_cases hmatch : (if k.val % 2 = 0 then (2 : Fin 3) else 0) = j
          · refine ⟨⟨(k.val + 1) % 12, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
            simpa only [hmatch] using hadj_words k
          · -- Then `j` is the OTHER generator: `k' = (k + 11) % 12`!
            set k' : Fin 12 := ⟨(k.val + 11) % 12, Nat.mod_lt _ (by norm_num)⟩
            have hstep' := hadj_words k'
            have hk_eq : (k'.val + 1) % 12 = k.val := by have := k.isLt; simp only [k']; omega
            have hj_eq : (if k'.val % 2 = 0 then (2 : Fin 3) else 0) = j := by
              rcases hj02 with rfl | rfl <;> fin_cases k <;> simp [k'] at hmatch ⊢
            rw [hk_eq, hj_eq] at hstep'
            refine ⟨k', fun u hu => ?_, fun u => ?_⟩
            · have h1 := hstep'.1 (hypRefl j u) (hypRefl_mem_ball j hu)
              rw [hypWord_append, hypWord_cons, hypWord_nil, hypRefl_invol j hu] at h1
              rw [hypWord_append, hypWord_cons, hypWord_nil, h1]
            · have h1 := hstep'.2 (eucRefl j u)
              rw [eucWord_append, eucWord_cons, eucWord_nil, eucRefl_invol j u] at h1
              rw [eucWord_append, eucWord_cons, eucWord_nil, h1]
        obtain ⟨k', hk'_h, hk'_e⟩ := hk'_ex
        -- On the open neighborhood `Wz := hypBall (vert1 0) δ_v ∩ hypBall z ρ`, `φ_v0 = chartMap (v0Word k) ψ`!
        set Wz : Set ℂ := hypBall (vert1 0) δ_v ∩ hypBall z ρ
        have hWz_open : IsOpen Wz := (isOpen_hypBall (vert1_mem_ball 0)).inter (isOpen_hypBall hzhb.1)
        have hz_Wz : z ∈ Wz := ⟨hzhb, self_mem_hypBall hzhb.1 hρ⟩
        have heq_Wz : φ_v0 =ᶠ[𝓝 z] chartMap (v0Word k.val) ψ := by
          filter_upwards [hWz_open.mem_nhds hz_Wz] with y ⟨hyhb, hyz⟩
          have hy'_hb : hypWord (v0Word k.val).reverse y ∈ hypBall x ρ := by
            refine ⟨hypWord_mem_ball _ hyhb.1, ?_⟩
            change hypDist (hypWord (v0Word k.val).reverse y) (hypWord (v0Word k.val).reverse z) < ρ
            rw [hypDist_hypWord (v0Word k.val).reverse hyhb.1 hzhb.1]
            exact hyz.2
          rcases hhb_cov hy'_hb with hy'Δ | hy'R
          · have hyk : y ∈ hypWord (v0Word k.val) '' Δ1 :=
              ⟨_, hy'Δ, hypWord_reverse_right _ hyhb.1⟩
            rw [hφv0_eq k y hyhb hyk]
            simp only [chartMap, hψ_Δ1 _ ⟨hy'_hb, hy'Δ⟩]
          · have hyk' : y ∈ hypWord (v0Word k'.val) '' Δ1 := by
              obtain ⟨u, huΔ, huy⟩ := hy'R
              refine ⟨u, huΔ, ?_⟩
              rw [hk'_h u huΔ.1, hypWord_append, hypWord_cons, hypWord_nil, huy,
                hypWord_reverse_right _ hyhb.1]
            rw [hφv0_eq k' y hyhb hyk']
            have hrev' : hypWord (v0Word k'.val).reverse y = hypRefl j (hypWord (v0Word k.val).reverse y) := by
              have h1 : hypWord (v0Word k'.val) (hypRefl j (hypWord (v0Word k.val).reverse y)) = y := by
                rw [hk'_h _ (hypRefl_mem_ball j (hypWord_mem_ball _ hyhb.1)), hypWord_append,
                  hypWord_cons, hypWord_nil, hypRefl_invol j (hypWord_mem_ball _ hyhb.1),
                  hypWord_reverse_right _ hyhb.1]
              conv_lhs => rw [← h1]
              exact hypWord_reverse_left _ (hypRefl_mem_ball j (hypWord_mem_ball _ hyhb.1))
            simp only [chartMap]
            rw [hrev', hk'_e, eucWord_append, eucWord_cons, eucWord_nil, hψ_R _ ⟨hy'_hb, hy'R⟩]
            simp only [chartMap, eucWord_cons, eucWord_nil, List.reverse_singleton, hypWord_cons,
              hypWord_nil]
        have hdiff_c : DifferentiableAt ℂ (chartMap (v0Word k.val) ψ) z :=
          chartMap_differentiableAt _ hzhb.1
            (hψ_diff.differentiableAt ((isOpen_hypBall hxΔ.1).mem_nhds (self_mem_hypBall hxΔ.1 hρ)))
        exact (hdiff_c.congr_of_eventuallyEq heq_Wz).differentiableWithinAt
      rcases hside02 with ⟨hs0, hs2⟩ | ⟨hs2, hs0⟩
      · exact hside_case 0 (Or.inl rfl) hs0 fun i hi => by fin_cases i <;> simp_all
      · exact hside_case 2 (Or.inr rfl) hs2 fun i hi => by fin_cases i <;> simp_all
  -- Apply Riemann's Removable Singularity Theorem at `vert1 0`!
  have hdiff_v0 : DifferentiableOn ℂ φ_v0 (hypBall (vert1 0) δ_v) :=
    (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      ((isOpen_hypBall (vert1_mem_ball 0)).mem_nhds (self_mem_hypBall (vert1_mem_ball 0) hδ_pos))).mp
      ⟨hdiff_punc, hcont0⟩
  -- Prove `deriv φ_v0 (vert1 0) = 0` via the 180° half-turn `τ = hypWord (v0Word 6)`!
  have hderiv0 : deriv φ_v0 (vert1 0) = 0 := by
    let τ : ℂ → ℂ := hypWord (v0Word 6)
    have hτ_inv : ∀ z ∈ hypBall (vert1 0) δ_v, φ_v0 (τ z) = φ_v0 z := by
      intro z hz
      have hτ_hb : τ z ∈ hypBall (vert1 0) δ_v := by
        refine ⟨hypWord_mem_ball _ hz.1, ?_⟩
        have hfix := hypWord_v0Word_fix_R 6
        rw [← hfix, hypDist_hypWord _ hz.1 (vert1_mem_ball 0)]
        exact hz.2
      obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov hz)
      set k' : Fin 12 := ⟨(k.val + 6) % 12, Nat.mod_lt _ (by norm_num)⟩
      -- Show `τ ∘ hypWord (v0Word k) = hypWord (v0Word k')` and `eucWord (v0Word k') = eucWord (v0Word k)`!
      have h6_h : ∀ u : ℂ, ‖u‖ < 1 → τ (hypWord (v0Word k.val) u) = hypWord (v0Word k'.val) u := by
        intro u hu
        have hR' : ‖(R : ℂ)‖ < 1 := by simpa [vert1] using vert1_mem_ball 0
        have hm1 := mobiusToZero_R_v0Word k.val hu
        have hm2 := mobiusToZero_R_v0Word k'.val hu
        have hmτ := hypWord_v0Word_6_eq_halfTurn (hypWord_mem_ball (v0Word k.val) hu)
        have hpow : -zeta12 ^ k.val = zeta12 ^ k'.val := by
          have h6 : zeta12 ^ 6 = -1 := by rw [show zeta12 ^ 6 = (zeta12 ^ 2) ^ 3 by ring, zeta12_pow_six]
          have h12 : zeta12 ^ 12 = 1 := by rw [show zeta12 ^ 12 = (zeta12 ^ 6) ^ 2 by ring, h6]; norm_num
          by_cases hlt : k.val < 6
          · have hk' : k'.val = k.val + 6 := by simp only [k']; omega
            rw [hk', pow_add, h6]; ring
          · have hk' : k'.val + 6 = k.val := by have := k.isLt; simp only [k']; omega
            rw [← hk', pow_add, h6]; ring
        have hpar : k'.val % 2 = k.val % 2 := by have := k.isLt; simp only [k']; omega
        have heq_m : mobiusToZero (R : ℂ) (τ (hypWord (v0Word k.val) u)) =
            mobiusToZero (R : ℂ) (hypWord (v0Word k'.val) u) := by
          rw [hmτ, hm1, hm2, hpar]
          split_ifs
          · rw [← neg_mul, hpow]
          · rw [← neg_mul, hpow]
        have := congrArg (mobiusToZero (-(R : ℂ))) heq_m
        rwa [mobiusToZero_inv hR' (hypWord_mem_ball _ (hypWord_mem_ball _ hu)),
          mobiusToZero_inv hR' (hypWord_mem_ball _ hu)] at this
      have h6_e : ∀ w : ℂ, eucWord (v0Word k'.val) w = eucWord (v0Word k.val) w := by
        intro w
        have h1 : ∀ m : ℕ, eucWord (v0Word (m + 6)) w = eucWord (v0Word m) w := by
          intro m
          have hcat : v0Word (m + 6) = v0Word 6 ++ v0Word m := by
            induction m with
            | zero => simp [v0Word]
            | succ m ih =>
              have hpar : (m + 6) % 2 = m % 2 := by omega
              change v0Word (m + 6) ++ [if (m + 6) % 2 = 0 then 2 else 0] =
                v0Word 6 ++ (v0Word m ++ [if m % 2 = 0 then 2 else 0])
              rw [ih, hpar, List.append_assoc]
          rw [hcat, eucWord_append, eucWord_v0Word_6]
        by_cases hlt : k.val < 6
        · have hk' : k'.val = k.val + 6 := by simp only [k']; omega
          rw [hk']; exact h1 k.val
        · have hk' : k.val = k'.val + 6 := by have := k.isLt; simp only [k']; omega
          rw [hk']; exact (h1 k'.val).symm
      obtain ⟨x, hxΔ, hxz⟩ := hk
      have hτk' : τ z ∈ hypWord (v0Word k'.val) '' Δ1 := ⟨x, hxΔ, by rw [← hxz, h6_h x hxΔ.1]⟩
      rw [hφv0_eq k z hz ⟨x, hxΔ, hxz⟩, hφv0_eq k' (τ z) hτ_hb hτk']
      have hrev1 : hypWord (v0Word k.val).reverse z = x := by rw [← hxz, hypWord_reverse_left _ hxΔ.1]
      have hrev2 : hypWord (v0Word k'.val).reverse (τ z) = x := by
        rw [← hxz, h6_h x hxΔ.1, hypWord_reverse_left _ hxΔ.1]
      simp only [chartMap, hrev1, hrev2, h6_e]
    -- Differentiate `φ_v0 ∘ τ = φ_v0` at `vert1 0` using `mobiusToZero R (τ z) = -mobiusToZero R z`!
    have hR' : ‖(R : ℂ)‖ < 1 := by simpa [vert1] using vert1_mem_ball 0
    have hmob_d : HasDerivAt (mobiusToZero (R : ℂ)) ((1 - (R : ℂ) ^ 2)⁻¹) (vert1 0) := by
      unfold mobiusToZero
      have hden_ne : (1 : ℂ) - starRingEnd ℂ (R : ℂ) * vert1 0 ≠ 0 :=
        one_sub_conj_mul_ne_zero (vert1_mem_ball 0) hR'
      have h1 : HasDerivAt (fun z => z - (R : ℂ)) 1 (vert1 0) := (hasDerivAt_id _).sub_const _
      have h2 : HasDerivAt (fun z => 1 - starRingEnd ℂ (R : ℂ) * z) (-(R : ℂ)) (vert1 0) := by
        simpa [Complex.conj_ofReal] using ((hasDerivAt_id _).const_mul (R : ℂ)).const_sub 1
      refine (h1.div h2 hden_ne).congr_deriv ?_
      simp only [vert1, Fin.val_zero, pow_zero, one_mul, Complex.conj_ofReal, sub_self, zero_mul,
        sub_zero, one_mul]
      have hne : (1 : ℂ) - (R : ℂ) ^ 2 ≠ 0 := by
        exact_mod_cast (by nlinarith [R_pos, R_lt_one] : (1 : ℝ) - R ^ 2 ≠ 0)
      field_simp [hne]
    have hmob_inv_d : HasDerivAt (mobiusToZero (-(R : ℂ))) (1 - (R : ℂ) ^ 2) 0 := by
      unfold mobiusToZero
      have h1 : HasDerivAt (fun w => w - -(R : ℂ)) 1 0 := (hasDerivAt_id _).sub_const _
      have h2 : HasDerivAt (fun w => 1 - starRingEnd ℂ (-(R : ℂ)) * w) (R : ℂ) 0 := by
        simpa [Complex.conj_ofReal] using ((hasDerivAt_id _).const_mul (-(R : ℂ))).const_sub 1
      refine (h1.div h2 (by simp)).congr_deriv ?_
      ring
    have hτ_eq_nhds : τ =ᶠ[𝓝 (vert1 0)] fun z => mobiusToZero (-(R : ℂ)) (-mobiusToZero (R : ℂ) z) := by
      have hv_ball : vert1 0 ∈ ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right]; exact vert1_mem_ball 0
      filter_upwards [isOpen_ball.mem_nhds hv_ball] with z hz
      have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
      have hm := hypWord_v0Word_6_eq_halfTurn hz1
      have := congrArg (mobiusToZero (-(R : ℂ))) hm
      rwa [mobiusToZero_inv hR' (hypWord_mem_ball _ hz1)] at this
    have hτ_d : HasDerivAt τ (-1) (vert1 0) := by
      have hm0 : -mobiusToZero (R : ℂ) (vert1 0) = 0 := by simp [mobiusToZero, vert1]
      have hmob_inv_d' : HasDerivAt (mobiusToZero (-(R : ℂ))) (1 - (R : ℂ) ^ 2)
          (-mobiusToZero (R : ℂ) (vert1 0)) := by rwa [hm0]
      have hcomp := hmob_inv_d'.comp (vert1 0) hmob_d.neg
      have hne : (1 : ℂ) - (R : ℂ) ^ 2 ≠ 0 := by
        exact_mod_cast (by nlinarith [R_pos, R_lt_one] : (1 : ℝ) - R ^ 2 ≠ 0)
      refine ((hcomp.congr_of_eventuallyEq hτ_eq_nhds).congr_deriv ?_)
      field_simp [hne]
    have hφ_d : HasDerivAt φ_v0 (deriv φ_v0 (vert1 0)) (vert1 0) :=
      (hdiff_v0.differentiableAt ((isOpen_hypBall (vert1_mem_ball 0)).mem_nhds
        (self_mem_hypBall (vert1_mem_ball 0) hδ_pos))).hasDerivAt
    have hτ0 : τ (vert1 0) = vert1 0 := hypWord_v0Word_fix_R 6
    have hφ_d' : HasDerivAt φ_v0 (deriv φ_v0 (vert1 0)) (τ (vert1 0)) := by rwa [hτ0]
    have hcomp_d : HasDerivAt (fun z => φ_v0 (τ z)) (deriv φ_v0 (vert1 0) * (-1)) (vert1 0) :=
      hφ_d'.comp (vert1 0) hτ_d
    have hcomp_eq : (fun z => φ_v0 (τ z)) =ᶠ[𝓝 (vert1 0)] φ_v0 := by
      filter_upwards [(isOpen_hypBall (vert1_mem_ball 0)).mem_nhds
        (self_mem_hypBall (vert1_mem_ball 0) hδ_pos)] with z hz
      exact hτ_inv z hz
    have huniq := (hcomp_d.congr_of_eventuallyEq hcomp_eq.symm).unique hφ_d
    linear_combination -huniq / 2
  exact ⟨δ_v, φ_v0, hδ_pos, hδ_le, hside1_hb, hdisj_v, hdiff_v0, hderiv0, hcov, hφv0_eq⟩

/- ## 6. Assembly of `φ_ext` on `U` and the Uniform Continuation Property -/

/-- Full holomorphic extension `φ_ext` of `φ` on a uniform hyperbolic `ρ₀`-neighborhood `U` of `Δ1`,
    with `deriv φ_ext 0 = 1`, `deriv φ_ext (vert1 k) = 0`, and the uniform continuation property. -/
theorem φ_ext_exists :
    ∃ (ρ₀ : ℝ) (φ_ext : ℂ → ℂ), 0 < ρ₀ ∧ ρ₀ ≤ 1 / 4 ∧
      let U : Set ℂ := {z : ℂ | ‖z‖ < 1 ∧ ∃ x ∈ Δ1, hypDist x z < ρ₀}
      IsOpen U ∧
      DifferentiableOn ℂ φ_ext U ∧
      (∀ z ∈ Δ1, φ_ext z = φ z) ∧
      deriv φ_ext 0 = 1 ∧
      (∀ k : Fin 3, deriv φ_ext (vert1 k) = 0) ∧
      (∀ y : ℂ, ‖y‖ < 1 → (∃ x ∈ Δ1, hypDist x y < ρ₀ / 2) →
        ∃ u : List (Fin 3), y ∈ hypWord u '' Δ1 ∧
          ∀ z ∈ hypBall y (ρ₀ / 2), chartMap u φ_ext z = φ_ext z) := by
  classical
  obtain ⟨δ_v, φ_v0, hδ_pos, hδ_le, hside1_hb, hdisj_v0, hdiff_v0, hderiv_v0, hcov_v0, hφv0_eq⟩ :=
    φ_vertex0_extension
  -- Rotate `φ_v0` by `ω^k` to define `φ_vk` on `hypBall (vert1 k) δ_v` for all `k : Fin 3`!
  let rotPow : Fin 3 → ℂ → ℂ := fun k z => ω ^ (k : ℕ) * z
  let rotInv : Fin 3 → ℂ → ℂ := fun k z => ω ^ ((3 - k.val) % 3) * z
  have hrot_cancel : ∀ (k : Fin 3) (z : ℂ), rotPow k (rotInv k z) = z := by
    intro k z; fin_cases k <;> simp only [rotPow, rotInv, Nat.reduceSub, Nat.reduceMod, pow_zero,
      pow_one, one_mul]
    · linear_combination z * ω_cube
    · linear_combination z * ω_cube
  have hrot_cancel' : ∀ (k : Fin 3) (z : ℂ), rotInv k (rotPow k z) = z := by
    intro k z; fin_cases k <;> simp only [rotPow, rotInv, Nat.reduceSub, Nat.reduceMod, pow_zero,
      pow_one, one_mul]
    · linear_combination z * ω_cube
    · linear_combination z * ω_cube
  have hrot_hypDist : ∀ (k : Fin 3) {z w : ℂ}, hypDist (rotInv k z) (rotInv k w) = hypDist z w := by
    intro k z w
    unfold hypDist rotInv
    have hmul : starRingEnd ℂ (ω ^ ((3 - k.val) % 3)) * ω ^ ((3 - k.val) % 3) = 1 := by
      rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm, norm_ω_pow]; norm_num
    rw [← mul_sub, map_mul, show starRingEnd ℂ (ω ^ ((3 - k.val) % 3)) * starRingEnd ℂ w *
        (ω ^ ((3 - k.val) % 3) * z) =
        (starRingEnd ℂ (ω ^ ((3 - k.val) % 3)) * ω ^ ((3 - k.val) % 3)) * (starRingEnd ℂ w * z) by ring,
      hmul, one_mul, norm_div, norm_mul, norm_ω_pow, one_mul, ← norm_div]
  have hrot_vert : ∀ k : Fin 3, rotInv k (vert1 k) = vert1 0 := by
    intro k; simp only [vert1, rotInv, Fin.val_zero, pow_zero, one_mul]
    fin_cases k
    · simp
    · simp only [Nat.reduceSub, Nat.reduceMod, pow_one]; linear_combination (R : ℂ) * ω_cube
    · simp only [Nat.reduceSub, Nat.reduceMod, pow_one]; linear_combination (R : ℂ) * ω_cube
  have hrot_hb : ∀ (k : Fin 3) {z : ℂ}, z ∈ hypBall (vert1 k) δ_v →
      rotInv k z ∈ hypBall (vert1 0) δ_v := by
    intro k z ⟨hz1, hdist⟩
    refine ⟨by simp only [rotInv, norm_mul, norm_ω_pow, one_mul]; exact hz1, ?_⟩
    rw [← hrot_vert k, hrot_hypDist k]; exact hdist
  have hrotWord0 : ∀ w : List (Fin 3), rotWord 0 w = w := by
    intro w; induction w with
    | nil => rfl
    | cons j js ih =>
      change ⟨(j.val + 0) % 3, _⟩ :: rotWord 0 js = j :: js
      rw [ih]; congr 1; ext; simp [Nat.mod_eq_of_lt j.isLt]
  have hrotWord2 : ∀ w : List (Fin 3), rotWord 2 w = rotWord 1 (rotWord 1 w) := by
    intro w; induction w with
    | nil => rfl
    | cons j js ih =>
      change ⟨(j.val + 2) % 3, _⟩ :: rotWord 2 js = ⟨((j.val + 1) % 3 + 1) % 3, _⟩ :: rotWord 1 (rotWord 1 js)
      rw [ih]; congr 1; fin_cases j <;> decide
  have hrot_hypWord : ∀ (k : Fin 3) (w : List (Fin 3)) (z : ℂ),
      hypWord (rotWord k.val w) (rotPow k z) = rotPow k (hypWord w z) := by
    intro k w z
    fin_cases k
    · simp only [rotPow, pow_zero, one_mul]; rw [hrotWord0]
    · dsimp only [rotPow]; simp only [pow_one]; exact hypWord_rotWord1 w z
    · dsimp only [rotPow]
      rw [hrotWord2, show ω ^ 2 * z = ω * (ω * z) by ring, hypWord_rotWord1, hypWord_rotWord1]; ring
  have hrot_eucWord : ∀ (k : Fin 3) (w : List (Fin 3)) (z : ℂ),
      eucWord (rotWord k.val w) (rotPow k z) = rotPow k (eucWord w z) := by
    intro k w z
    fin_cases k
    · simp only [rotPow, pow_zero, one_mul]; rw [hrotWord0]
    · dsimp only [rotPow]; simp only [pow_one]; exact eucWord_rotWord1 w z
    · dsimp only [rotPow]
      rw [hrotWord2, show ω ^ 2 * z = ω * (ω * z) by ring, eucWord_rotWord1, eucWord_rotWord1]; ring
  have hrot_Δ1 : ∀ (k : Fin 3) {z : ℂ}, z ∈ Δ1 → rotPow k z ∈ Δ1 := by
    intro k z hz
    fin_cases k
    · simpa [rotPow] using hz
    · simpa [rotPow] using Δ1_rot_mem hz
    · simpa [rotPow, sq, mul_assoc] using Δ1_rot_mem (Δ1_rot_mem hz)
  have hrot_φ : ∀ (k : Fin 3) {z : ℂ}, z ∈ Δ1 → φ (rotPow k z) = rotPow k (φ z) := by
    intro k z hz
    fin_cases k
    · simp [rotPow]
    · simpa [rotPow] using φ_rot hz
    · simpa [rotPow, sq, mul_assoc] using (φ_rot (Δ1_rot_mem hz)).trans (by rw [φ_rot hz])
  let φ_vk : Fin 3 → ℂ → ℂ := fun k z => rotPow k (φ_v0 (rotInv k z))
  -- Properties of `φ_vk`:
  have hvk_diff : ∀ k : Fin 3, DifferentiableOn ℂ (φ_vk k) (hypBall (vert1 k) δ_v) := fun k z hz =>
    ((hdiff_v0.differentiableAt ((isOpen_hypBall (vert1_mem_ball 0)).mem_nhds (hrot_hb k hz))).comp z
      (differentiableAt_id.const_mul _)).const_mul _ |>.differentiableWithinAt
  have hvk_deriv : ∀ k : Fin 3, deriv (φ_vk k) (vert1 k) = 0 := by
    intro k
    have h1 : HasDerivAt (rotInv k) (ω ^ ((3 - k.val) % 3)) (vert1 k) := by
      simpa [rotInv] using (hasDerivAt_id (vert1 k)).const_mul (ω ^ ((3 - k.val) % 3))
    have h2 : HasDerivAt φ_v0 0 (vert1 0) := by
      rw [← hderiv_v0]
      exact (hdiff_v0.differentiableAt ((isOpen_hypBall (vert1_mem_ball 0)).mem_nhds
        (self_mem_hypBall (vert1_mem_ball 0) hδ_pos))).hasDerivAt
    have h3 : HasDerivAt (φ_vk k) (ω ^ (k : ℕ) * (0 * ω ^ ((3 - k.val) % 3))) (vert1 k) := by
      have hc := (hrot_vert k ▸ h2).comp (vert1 k) h1
      simpa only [φ_vk, rotPow, Function.comp_def] using hc.const_mul (ω ^ (k : ℕ))
    rw [h3.deriv]; ring
  have hvk_cov : ∀ (k : Fin 3),
      hypBall (vert1 k) δ_v ⊆ ⋃ (m : Fin 12), hypWord (rotWord k.val (v0Word m.val)) '' Δ1 := by
    intro k z hz
    obtain ⟨m, x, hxΔ, hxm⟩ := mem_iUnion.mp (hcov_v0 (hrot_hb k hz))
    refine mem_iUnion.mpr ⟨m, rotPow k x, hrot_Δ1 k hxΔ, ?_⟩
    rw [hrot_hypWord, hxm, hrot_cancel]
  have hvk_eq : ∀ (k : Fin 3) (m : Fin 12) (z : ℂ), z ∈ hypBall (vert1 k) δ_v →
      z ∈ hypWord (rotWord k.val (v0Word m.val)) '' Δ1 →
      φ_vk k z = chartMap (rotWord k.val (v0Word m.val)) φ z := by
    intro k m z hz ⟨x, hxΔ, hxz⟩
    have hx' : rotInv k x ∈ Δ1 := by
      fin_cases k
      · simpa [rotInv] using hxΔ
      · simpa [rotInv, sq, mul_assoc] using Δ1_rot_mem (Δ1_rot_mem hxΔ)
      · simpa [rotInv] using Δ1_rot_mem hxΔ
    have hmem0 : rotInv k z ∈ hypWord (v0Word m.val) '' Δ1 := by
      refine ⟨rotInv k x, hx', ?_⟩
      have h1 := hrot_hypWord k (v0Word m.val) (rotInv k x)
      rw [hrot_cancel k x, hxz] at h1
      have := congrArg (rotInv k) h1
      rw [hrot_cancel' k] at this; exact this.symm
    simp only [φ_vk]
    rw [hφv0_eq m (rotInv k z) (hrot_hb k hz) hmem0]
    have hrev_eq : hypWord (rotWord k.val (v0Word m.val)).reverse z = x := by
      rw [← hxz, hypWord_reverse_left _ hxΔ.1]
    have hrev0 : hypWord (v0Word m.val).reverse (rotInv k z) = rotInv k x := by
      have h1 : hypWord (v0Word m.val) (rotInv k x) = rotInv k z := by
        have := hrot_hypWord k (v0Word m.val) (rotInv k x)
        rw [hrot_cancel k x, hxz] at this
        have h2 := congrArg (rotInv k) this
        rw [hrot_cancel' k] at h2; exact h2.symm
      rw [← h1, hypWord_reverse_left _ hx'.1]
    simp only [chartMap, hrev_eq, hrev0]
    rw [← hrot_eucWord k (v0Word m.val), ← hrot_φ k hx', hrot_cancel k x]
  -- Also record: `φ_vk k` equals `φ` on `Δ1`, equals `chartMap [j] φ` on `hypRefl j '' Δ1`
  -- when `j = k` or `j = (k+2)%3`, and stays strictly inside side `(k+1)%3`!
  have hvk_opp_side : ∀ (k : Fin 3) (z : ℂ), z ∈ hypBall (vert1 k) δ_v →
      ‖sideCenter ⟨(k.val + 1) % 3, Nat.mod_lt _ (by norm_num)⟩‖ ^ 2 - 1 <
        ‖z - sideCenter ⟨(k.val + 1) % 3, Nat.mod_lt _ (by norm_num)⟩‖ ^ 2 := by
    intro k z hz
    have h1 := hside1_hb (rotInv k z) (hrot_hb k hz)
    have hsc : sideCenter ⟨(k.val + 1) % 3, Nat.mod_lt _ (by norm_num)⟩ = rotPow k (sideCenter 1) := by
      fin_cases k <;> simp only [sideCenter, rotPow, Fin.val_one, Nat.reduceAdd, Nat.reduceMod,
        pow_zero, pow_one, one_mul]
      · ring
      · linear_combination -a0 * ω_cube
    rw [hsc, ← hrot_cancel k z, ← show rotPow k (rotInv k z - sideCenter 1) =
        rotPow k (rotInv k z) - rotPow k (sideCenter 1) by simp [rotPow, mul_sub]]
    simp only [rotPow, norm_mul, norm_ω_pow, one_mul]
    exact h1
  have hvk_disj : ∀ (k₁ k₂ : Fin 3), k₁ ≠ k₂ →
      Disjoint (hypBall (vert1 k₁) δ_v) (hypBall (vert1 k₂) δ_v) := by
    intro k₁ k₂ hne
    rw [Set.disjoint_iff]
    intro z ⟨h1, h2⟩
    set k' : Fin 3 := ⟨(k₂.val + 3 - k₁.val) % 3, Nat.mod_lt _ (by norm_num)⟩
    have hk'_ne : k' ≠ 0 := by fin_cases k₁ <;> fin_cases k₂ <;> simp_all [k']
    have hm1 : rotInv k₁ z ∈ hypBall (vert1 0) δ_v := hrot_hb k₁ h1
    have hm2 : rotInv k₁ z ∈ hypBall (vert1 k') δ_v := by
      refine ⟨hm1.1, ?_⟩
      have hvk' : rotInv k₁ (vert1 k₂) = vert1 k' := by
        dsimp only [k', rotInv, vert1]
        fin_cases k₁ <;> fin_cases k₂
        · exact absurd rfl hne
        · simp
        · simp
        · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, pow_zero, one_mul]
        · exact absurd rfl hne
        · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, pow_one]; linear_combination ω * (R : ℂ) * ω_cube
        · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, pow_zero, pow_one, one_mul]
        · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, pow_one]; ring
        · exact absurd rfl hne
      rw [← hvk', hrot_hypDist k₁]; exact h2.2
    exact Set.disjoint_left.mp (hdisj_v0 k' hk'_ne) hm1 hm2
  have hvk_on_Δ1 : ∀ (k : Fin 3) (z : ℂ), z ∈ hypBall (vert1 k) δ_v → z ∈ Δ1 → φ_vk k z = φ z := by
    intro k z hz hzΔ
    have h0 : rotWord k.val (v0Word (0 : Fin 12).val) = [] := rfl
    have heq := hvk_eq k 0 z hz (by rw [h0]; exact ⟨z, hzΔ, rfl⟩)
    rwa [h0, chartMap_nil] at heq
  have hvk_on_refl : ∀ (k j : Fin 3) (z : ℂ), z ∈ hypBall (vert1 k) δ_v → z ∈ hypRefl j '' Δ1 →
      (j.val = k.val ∨ j.val = (k.val + 2) % 3) → φ_vk k z = chartMap [j] φ z := by
    intro k j z hz ⟨x, hxΔ, hxz⟩ hjk
    rcases hjk with hjk0 | hjk2
    · -- `j = k`: corresponds to `m = 11` (`v0Word 11` acts as `[0]`)!
      have hj_eq : j = k := Fin.ext hjk0
      subst j
      have h11_act : ∀ u : ℂ, ‖u‖ < 1 → hypWord (v0Word 11) u = hypRefl 0 u := by
        intro u hu
        have h12 : v0Word 11 ++ [(0 : Fin 3)] = v0Word 12 := by decide
        have h1 := hypWord_v0Word_12 (hypRefl_mem_ball 0 hu)
        rw [← h12, hypWord_append, hypWord_cons, hypWord_nil, hypRefl_invol 0 hu] at h1
        exact h1
      have h11_euc : ∀ w : ℂ, eucWord (v0Word 11) w = eucRefl 0 w := by
        intro w
        have h12 : v0Word 11 ++ [(0 : Fin 3)] = v0Word 12 := by decide
        have h1 := eucWord_v0Word_12 (eucRefl 0 w)
        rw [← h12, eucWord_append, eucWord_cons, eucWord_nil, eucRefl_invol 0 w] at h1
        exact h1
      have hrot11_h : ∀ u : ℂ, ‖u‖ < 1 → hypWord (rotWord k.val (v0Word 11)) u = hypRefl k u := by
        intro u hu
        have h1 := hrot_hypWord k (v0Word 11) (rotInv k u)
        rw [hrot_cancel k u, h11_act _ (by simp only [rotInv, norm_mul, norm_ω_pow, one_mul]; exact hu)] at h1
        rw [h1]
        have hrot0 : hypWord (rotWord k.val [0]) u = hypRefl k u := by
          fin_cases k <;> simp [rotWord]
        have h2 := hrot_hypWord k [0] (rotInv k u)
        rw [hrot_cancel k u] at h2
        simpa [hrot0] using h2.symm
      have hrot11_e : ∀ w : ℂ, eucWord (rotWord k.val (v0Word 11)) w = eucRefl k w := by
        intro w
        have h1 := hrot_eucWord k (v0Word 11) (rotInv k w)
        rw [hrot_cancel k w, h11_euc] at h1
        rw [h1]
        have hrot0 : eucWord (rotWord k.val [0]) w = eucRefl k w := by
          fin_cases k <;> simp [rotWord]
        have h2 := hrot_eucWord k [0] (rotInv k w)
        rw [hrot_cancel k w] at h2
        simpa [hrot0] using h2.symm
      have hmem11 : z ∈ hypWord (rotWord k.val (v0Word 11)) '' Δ1 :=
        ⟨x, hxΔ, by rw [hrot11_h x hxΔ.1, hxz]⟩
      rw [hvk_eq k ⟨11, by norm_num⟩ z hz hmem11]
      have hrev11 : hypWord (rotWord k.val (v0Word 11)).reverse z = x := by
        have : hypWord (rotWord k.val (v0Word 11)) x = z := by rw [hrot11_h x hxΔ.1, hxz]
        rw [← this, hypWord_reverse_left _ hxΔ.1]
      have hrevk : hypWord [k].reverse z = x := by
        simp only [List.reverse_singleton, hypWord_cons, hypWord_nil, ← hxz, hypRefl_invol k hxΔ.1]
      simp only [chartMap, hrev11, hrevk, hrot11_e, eucWord_cons, eucWord_nil]
    · -- `j = (k + 2) % 3`: corresponds to `m = 1` (`v0Word 1 = [2]`, rotated by `k` gives `[j]`)!
      have hrot1 : rotWord k.val (v0Word 1) = [j] := by
        have hj : j = ⟨(2 + k.val) % 3, Nat.mod_lt _ (by norm_num)⟩ :=
          Fin.ext (by show j.val = (2 + k.val) % 3; omega)
        rw [hj]; rfl
      have hmem1 : z ∈ hypWord (rotWord k.val (v0Word 1)) '' Δ1 := by
        rw [hrot1]; exact ⟨x, hxΔ, hxz⟩
      rw [hvk_eq k ⟨1, by norm_num⟩ z hz hmem1, hrot1]
  -- Now construct a uniform cover of compact `Δ1`!
  -- Every `x ∈ Δ1` gets a chart `(r_x, ψ_x, W_x)` on `hypBall x r_x` with `r_x ∈ (0, 1/4]`:
  -- Type A (`x ∈ hypBall (vert1 k) (δ_v / 2)`): chart is `φ_vk k` on `hypBall x (δ_v / 2) ⊆ hypBall (vert1 k) δ_v`.
  -- Type B (`x ∈ Δ1Open` not in Type A): chart is `φ` on `hypBall x r_x ⊆ Δ1Open`.
  -- Type C (`x` on open side `j` not in Type A): chart is `ψ_side` from `φ_side_extension` on `hypBall x r_x`.
  -- ALL charts agree POINTWISE on every overlap!!
  -- Let's package the exact compatibility predicate for a local chart `(r, ψ, words)` at `x ∈ Δ1`:
  -- Even cleaner: build ONE global canonical function `φ_ext` directly by case-splitting on `z ∈ ball 0 1`:
  -- Wait: EVERY `z` in `U_cov := Δ1Open ∪ (⋃ k, hypBall (vert1 k) δ_v) ∪ (⋃ x ∈ K_side, hypBall x r_x)`
  -- has a WELL-DEFINED value because ALL these open sets agree pointwise on overlaps!
  -- Let's verify this explicitly!
  -- Define `K_side := Δ1 \ (Δ1Open ∪ ⋃ k : Fin 3, hypBall (vert1 k) (δ_v / 2))`:
  -- Every `x ∈ K_side` lies on a unique open side `j_x`!
  have hK_side : ∀ x ∈ Δ1, x ∉ Δ1Open → (∀ k : Fin 3, x ∉ hypBall (vert1 k) (δ_v / 2)) →
      ∃ (j : Fin 3) (ρ : ℝ) (ψ : ℂ → ℂ), 0 < ρ ∧ ρ ≤ 1 / 4 ∧
        DifferentiableOn ℂ ψ (hypBall x ρ) ∧
        (∀ y ∈ hypBall x ρ, ∀ i : Fin 3, i ≠ j → ‖sideCenter i‖ ^ 2 - 1 < ‖y - sideCenter i‖ ^ 2) ∧
        hypBall x ρ ⊆ Δ1 ∪ hypRefl j '' Δ1 ∧
        (∀ y ∈ hypBall x ρ ∩ Δ1, ψ y = φ y) ∧
        (∀ y ∈ hypBall x ρ ∩ hypRefl j '' Δ1, ψ y = chartMap [j] φ y) := by
    intro x hxΔ hno hnv
    have hex_j : ∃ j : Fin 3, ‖x - sideCenter j‖ ^ 2 = ‖sideCenter j‖ ^ 2 - 1 := by
      by_contra hall; push Not at hall
      exact hno ⟨hxΔ.1, fun j => lt_of_le_of_ne (hxΔ.2 j) (Ne.symm (hall j))⟩
    obtain ⟨j, hj⟩ := hex_j
    have hother : ∀ i : Fin 3, i ≠ j → ‖sideCenter i‖ ^ 2 - 1 < ‖x - sideCenter i‖ ^ 2 := by
      intro i hij
      refine lt_of_le_of_ne (hxΔ.2 i) fun heq => ?_
      have hv_ex : ∃ k : Fin 3, x = vert1 k := by
        fin_cases j <;> fin_cases i
        all_goals first
          | exact absurd rfl hij
          | exact ⟨1, side0_inter_side1_eq_vert1 hxΔ.1 hj heq.symm⟩
          | exact ⟨0, (side_inter_side_eq_vert1 (by decide : (2 : Fin 3) ≠ 0) hxΔ.1 heq.symm hj).2.2 ⟨rfl, rfl⟩⟩
          | exact ⟨1, side0_inter_side1_eq_vert1 hxΔ.1 heq.symm hj⟩
          | exact ⟨2, (side_inter_side_eq_vert1 (by decide : (1 : Fin 3) ≠ 2) hxΔ.1 hj heq.symm).2.1 ⟨rfl, rfl⟩⟩
          | exact ⟨0, (side_inter_side_eq_vert1 (by decide : (2 : Fin 3) ≠ 0) hxΔ.1 hj heq.symm).2.2 ⟨rfl, rfl⟩⟩
          | exact ⟨2, (side_inter_side_eq_vert1 (by decide : (1 : Fin 3) ≠ 2) hxΔ.1 heq.symm hj).2.1 ⟨rfl, rfl⟩⟩
      obtain ⟨k, rfl⟩ := hv_ex
      exact hnv k (self_mem_hypBall (vert1_mem_ball k) (by linarith))
    obtain ⟨ρ, ψ, hρ, _, hψ_diff, hoth, hcov, hΔ, hR⟩ := φ_side_extension j hxΔ hj hother
    set ρ' := min ρ (1 / 4)
    have hsub : hypBall x ρ' ⊆ hypBall x ρ := fun y hy => ⟨hy.1, lt_of_lt_of_le hy.2 (min_le_left _ _)⟩
    exact ⟨j, ρ', ψ, lt_min hρ (by norm_num), min_le_right _ _, hψ_diff.mono hsub,
      fun y hy => hoth y (hsub hy), hsub.trans hcov,
      fun y ⟨hy, hyΔ⟩ => hΔ y ⟨hsub hy, hyΔ⟩, fun y ⟨hy, hyR⟩ => hR y ⟨hsub hy, hyR⟩⟩
  -- For EVERY `x ∈ Δ1`, package a chart `(r_x, ψ_x, W_x)` on `hypBall x r_x` with the uniform
  -- pointwise compatibility property:
  -- (P1) `∀ y ∈ hypBall x r_x ∩ Δ1, ψ_x y = φ y`
  -- (P2) `∀ j : Fin 3, ∀ y ∈ hypBall x r_x ∩ hypRefl j '' Δ1, ψ_x y = chartMap [j] φ y`
  -- (P3) `∀ k : Fin 3, ∀ y ∈ hypBall x r_x ∩ hypBall (vert1 k) δ_v, ψ_x y = φ_vk k y`
  -- (P4) `hypBall x r_x ⊆ ⋃ u ∈ W_x, hypWord u '' Δ1` and `∀ u ∈ W_x, ∀ y ∈ hypBall x r_x ∩ hypWord u '' Δ1, ψ_x y = chartMap u φ y`!
  -- WAIT: check (P2) for `φ_vk k`: if `z ∈ hypBall (vert1 k) δ_v ∩ hypRefl j '' Δ1`, can `j = (k + 1) % 3`?
  -- NO!! Because `hvk_opp_side` says `z` satisfies STRICT side `(k+1)%3`, whereas if `z = hypRefl j x` with `x ∈ Δ1`
  -- and `z ∉ Δ1`, `hypRefl_side_sign` forces `‖z - sideCenter j‖^2 ≤ ‖sideCenter j‖^2 - 1`, CONTRADICTION!!
  -- And if `z ∈ Δ1`, then `z ∈ Δ1 ∩ hypRefl j '' Δ1`, so `z` lies on side `j`, where `chartMap [j] φ z = φ z = φ_vk k z`!
  -- WAIT A SECOND!! Check that! For EVERY chart (Type A, B, or C), `ψ_x` satisfies a SINGLE canonical formula on `hypBall x r_x`:
  -- - On `Δ1`: `φ`
  -- - On `hypRefl j '' Δ1 \ Δ1`: `chartMap [j] φ`
  -- - On `hypBall (vert1 k) δ_v`: `φ_vk k`!
  -- Let's define `φ_ext : ℂ → ℂ` EXPLICITLY using those 3 cases — ZERO choice needed for gluing!!
  let φ_ext : ℂ → ℂ := fun z =>
    if z ∈ Δ1 then φ z
    else if h0 : z ∈ hypBall (vert1 0) δ_v then φ_vk 0 z
    else if h1 : z ∈ hypBall (vert1 1) δ_v then φ_vk 1 z
    else if h2 : z ∈ hypBall (vert1 2) δ_v then φ_vk 2 z
    else if z ∈ hypRefl 0 '' Δ1 then chartMap [0] φ z
    else if z ∈ hypRefl 1 '' Δ1 then chartMap [1] φ z
    else if z ∈ hypRefl 2 '' Δ1 then chartMap [2] φ z
    else 0
  have hφext_Δ1 : ∀ z ∈ Δ1, φ_ext z = φ z := fun z hz => by simp [φ_ext, hz]
  have hφext_vk : ∀ (k : Fin 3) (z : ℂ), z ∈ hypBall (vert1 k) δ_v → φ_ext z = φ_vk k z := by
    intro k z hz
    by_cases hzΔ : z ∈ Δ1
    · rw [hφext_Δ1 z hzΔ, hvk_on_Δ1 k z hz hzΔ]
    · fin_cases k
      · have hz0 : z ∈ hypBall (vert1 0) δ_v := hz
        simp [φ_ext, hzΔ, hz0]
      · have hz1 : z ∈ hypBall (vert1 1) δ_v := hz
        have hnd0 : z ∉ hypBall (vert1 0) δ_v := fun h => Set.disjoint_left.mp (hvk_disj 0 1 (by decide)) h hz1
        simp [φ_ext, hzΔ, hnd0, hz1]
      · have hz2 : z ∈ hypBall (vert1 2) δ_v := hz
        have hnd0 : z ∉ hypBall (vert1 0) δ_v := fun h => Set.disjoint_left.mp (hvk_disj 0 2 (by decide)) h hz2
        have hnd1 : z ∉ hypBall (vert1 1) δ_v := fun h => Set.disjoint_left.mp (hvk_disj 1 2 (by decide)) h hz2
        simp [φ_ext, hzΔ, hnd0, hnd1, hz2]
  have hφext_side : ∀ (j : Fin 3) (z : ℂ), z ∈ ball (0 : ℂ) 1 →
      (∀ i : Fin 3, i ≠ j → ‖sideCenter i‖ ^ 2 - 1 < ‖z - sideCenter i‖ ^ 2) →
      z ∈ hypRefl j '' Δ1 → φ_ext z = chartMap [j] φ z := by
    intro j z hz1 hother hzR
    have hz1' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz1
    by_cases hzΔ : z ∈ Δ1
    · -- `z ∈ Δ1 ∩ hypRefl j '' Δ1` -> `z` is on side `j`, where `φ z = chartMap [j] φ z`!
      rw [hφext_Δ1 z hzΔ]
      have hsj : ‖z - sideCenter j‖ ^ 2 = ‖sideCenter j‖ ^ 2 - 1 := by
        obtain ⟨x, hxΔ, hxz⟩ := hzR
        have hx_le := hxΔ.2 j
        have hsign := hypRefl_side_sign j hz1'
        rw [← hxz, hypRefl_invol j hxΔ.1, hxz] at hsign
        have hnum_pos : 0 < ‖sideCenter j‖ ^ 2 - 1 := sideCenter_sq_sub_one_pos j
        have hden_pos : 0 < ‖z - sideCenter j‖ ^ 2 := by
          have hne : z - sideCenter j ≠ 0 := by
            intro h0; have := congrArg (starRingEnd ℂ) h0
            simp only [map_sub, map_zero] at this
            exact conj_sub_conj_sideCenter_ne_zero j hz1' this
          positivity
        have hfrac : 0 < (‖sideCenter j‖ ^ 2 - 1) / ‖z - sideCenter j‖ ^ 2 := div_pos hnum_pos hden_pos
        have hle : ‖z - sideCenter j‖ ^ 2 ≤ ‖sideCenter j‖ ^ 2 - 1 := by nlinarith
        exact le_antisymm hle (hzΔ.2 j)
      obtain ⟨ρ, ψ, hρ, _, _, _, _, hΔ, hR⟩ := φ_side_extension j hzΔ hsj hother
      rw [← hΔ z ⟨self_mem_hypBall hz1' hρ, hzΔ⟩, hR z ⟨self_mem_hypBall hz1' hρ, hzR⟩]
    · -- `z ∉ Δ1`: check whether `z ∈ hypBall (vert1 k) δ_v` for some `k`!
      have hviol_j : ‖z - sideCenter j‖ ^ 2 < ‖sideCenter j‖ ^ 2 - 1 := by
        by_contra hge; push Not at hge
        refine hzΔ ⟨hz1', fun i => ?_⟩
        by_cases hij : i = j
        · exact hij ▸ hge
        · exact (hother i hij).le
      -- If `z ∈ hypBall (vert1 k) δ_v`, then `j` CANNOT be `(k + 1) % 3` (by `hvk_opp_side`)!
      have hvk_case : ∀ k : Fin 3, z ∈ hypBall (vert1 k) δ_v → φ_vk k z = chartMap [j] φ z := by
        intro k hzk
        have hopp := hvk_opp_side k z hzk
        have hne_opp : j.val ≠ (k.val + 1) % 3 := fun heq => by
          have hj_eq : j = ⟨(k.val + 1) % 3, Nat.mod_lt _ (by norm_num)⟩ := Fin.ext heq
          rw [hj_eq] at hviol_j; linarith
        have hjk : j.val = k.val ∨ j.val = (k.val + 2) % 3 := by
          have := j.isLt; have := k.isLt; omega
        exact hvk_on_refl k j z hzk hzR hjk
      -- If `z` is in none of the `hypBall (vert1 k) δ_v`, `z` cannot be in `hypRefl i '' Δ1` for `i ≠ j`!
      have hnot_other : ∀ i : Fin 3, i ≠ j → z ∉ hypRefl i '' Δ1 := by
        intro i hij ⟨x, hxΔ, hxz⟩
        have hstrict := hother i hij
        have hsign := hypRefl_side_sign i hz1'
        rw [← hxz, hypRefl_invol i hxΔ.1, hxz] at hsign
        have hnum_pos : 0 < ‖sideCenter i‖ ^ 2 - 1 := sideCenter_sq_sub_one_pos i
        have hden_pos : 0 < ‖z - sideCenter i‖ ^ 2 := by
          have hne : z - sideCenter i ≠ 0 := by
            intro h0; have := congrArg (starRingEnd ℂ) h0
            simp only [map_sub, map_zero] at this
            exact conj_sub_conj_sideCenter_ne_zero i hz1' this
          positivity
        have hfrac : 0 < (‖sideCenter i‖ ^ 2 - 1) / ‖z - sideCenter i‖ ^ 2 := div_pos hnum_pos hden_pos
        have := hxΔ.2 i
        nlinarith
      by_cases h0 : z ∈ hypBall (vert1 0) δ_v
      · rw [hφext_vk 0 z h0, hvk_case 0 h0]
      · by_cases h1 : z ∈ hypBall (vert1 1) δ_v
        · rw [hφext_vk 1 z h1, hvk_case 1 h1]
        · by_cases h2 : z ∈ hypBall (vert1 2) δ_v
          · rw [hφext_vk 2 z h2, hvk_case 2 h2]
          · fin_cases j
            · have hzR0 : z ∈ hypRefl 0 '' Δ1 := hzR
              simp only [φ_ext, hzΔ, h0, h1, h2, hzR0, ↓reduceDIte, ↓reduceIte]; rfl
            · have hzR1 : z ∈ hypRefl 1 '' Δ1 := hzR
              have hn0 : z ∉ hypRefl 0 '' Δ1 := hnot_other 0 (by decide)
              simp only [φ_ext, hzΔ, h0, h1, h2, hn0, hzR1, ↓reduceDIte, ↓reduceIte]; rfl
            · have hzR2 : z ∈ hypRefl 2 '' Δ1 := hzR
              have hn0 : z ∉ hypRefl 0 '' Δ1 := hnot_other 0 (by decide)
              have hn1 : z ∉ hypRefl 1 '' Δ1 := hnot_other 1 (by decide)
              simp only [φ_ext, hzΔ, h0, h1, h2, hn0, hn1, hzR2, ↓reduceDIte, ↓reduceIte]; rfl
  -- Now EVERY `x ∈ Δ1` has a radius `rx ∈ (0, 1/4]` such that on `hypBall x rx`:
  -- (1) `φ_ext` is holomorphic on `hypBall x rx`, AND
  -- (2) `∃ Wx : List (List (Fin 3)), hypBall x rx ⊆ ⋃ u ∈ Wx, hypWord u '' Δ1 ∧ ∀ u ∈ Wx, ∀ y ∈ hypBall x rx ∩ hypWord u '' Δ1, φ_ext y = chartMap u φ y`!
  have hlocal_chart : ∀ x ∈ Δ1, ∃ (rx : ℝ) (Wx : List (List (Fin 3))), 0 < rx ∧ rx ≤ 1 / 4 ∧
      DifferentiableOn ℂ φ_ext (hypBall x rx) ∧
      hypBall x rx ⊆ ⋃ u ∈ Wx, hypWord u '' Δ1 ∧
      (∀ u ∈ Wx, ∀ y ∈ hypBall x rx ∩ hypWord u '' Δ1, φ_ext y = chartMap u φ y) := by
    intro x hxΔ
    by_cases hv : ∃ k : Fin 3, x ∈ hypBall (vert1 k) (δ_v / 2)
    · obtain ⟨k, hxk⟩ := hv
      refine ⟨δ_v / 2, (List.finRange 12).map (fun m => rotWord k.val (v0Word m.val)),
        by linarith, by linarith, ?_, ?_, ?_⟩
      · have hsub : hypBall x (δ_v / 2) ⊆ hypBall (vert1 k) δ_v := by
          intro y ⟨hy1, hyd⟩
          refine ⟨hy1, ?_⟩
          have htri := hypDist_triangle hy1 hxΔ.1 (vert1_mem_ball k)
          linarith [hxk.2]
        refine (hvk_diff k).mono hsub |>.congr fun y hy => hφext_vk k y (hsub hy)
      · intro y hy
        have hyk : y ∈ hypBall (vert1 k) δ_v :=
          ⟨hy.1, lt_of_le_of_lt (hypDist_triangle hy.1 hxΔ.1 (vert1_mem_ball k)) (by linarith [hy.2, hxk.2])⟩
        obtain ⟨m, hm⟩ := mem_iUnion.mp (hvk_cov k hyk)
        exact mem_iUnion₂.mpr ⟨rotWord k.val (v0Word m.val),
          List.mem_map.mpr ⟨m, List.mem_finRange m, rfl⟩, hm⟩
      · intro u hu y ⟨hy, hyu⟩
        obtain ⟨m, _, rfl⟩ := List.mem_map.mp hu
        have hyk : y ∈ hypBall (vert1 k) δ_v :=
          ⟨hy.1, lt_of_le_of_lt (hypDist_triangle hy.1 hxΔ.1 (vert1_mem_ball k)) (by linarith [hy.2, hxk.2])⟩
        rw [hφext_vk k y hyk, hvk_eq k m y hyk hyu]
    · push Not at hv
      by_cases ho : x ∈ Δ1Open
      · obtain ⟨r, hr, hbr⟩ := Metric.isOpen_iff.mp isOpen_Δ1Open x ho
        set rx := min (1 / 4) (r / 2)
        have hsub : hypBall x rx ⊆ Δ1Open := by
          intro y ⟨hy1, hyd⟩
          refine hbr ?_
          rw [Metric.mem_ball, dist_eq_norm]
          have hden_le : ‖1 - starRingEnd ℂ x * y‖ ≤ 2 := by
            calc ‖1 - starRingEnd ℂ x * y‖ ≤ ‖(1 : ℂ)‖ + ‖starRingEnd ℂ x * y‖ := norm_sub_le _ _
              _ = 1 + ‖x‖ * ‖y‖ := by rw [norm_one, norm_mul, RCLike.norm_conj]
              _ ≤ 1 + 1 * 1 := by nlinarith [hxΔ.1, hy1, norm_nonneg x, norm_nonneg y]
              _ = 2 := by norm_num
          have hden_pos : 0 < ‖1 - starRingEnd ℂ x * y‖ :=
            norm_pos_iff.mpr (one_sub_conj_mul_ne_zero hy1 hxΔ.1)
          unfold hypDist at hyd; rw [norm_div, div_lt_iff₀ hden_pos] at hyd
          have : rx ≤ r / 2 := min_le_right _ _
          nlinarith
        refine ⟨rx, [[]], lt_min (by norm_num) (by linarith), min_le_left _ _, ?_, ?_, ?_⟩
        · exact (φ_differentiableOn.mono hsub).congr fun y hy =>
            hφext_Δ1 y ⟨(hsub hy).1, fun j => ((hsub hy).2 j).le⟩
        · intro y hy
          exact mem_iUnion₂.mpr ⟨[], List.mem_singleton_self [],
            ⟨y, ⟨(hsub hy).1, fun j => ((hsub hy).2 j).le⟩, rfl⟩⟩
        · intro u hu y ⟨hy, _⟩
          rw [List.mem_singleton.mp hu, chartMap_nil]
          exact hφext_Δ1 y ⟨(hsub hy).1, fun j => ((hsub hy).2 j).le⟩
      · obtain ⟨j, rx, ψ, hrx_pos, hrx_le, hψ_diff, hoth, hcov, hψ_Δ, hψ_R⟩ := hK_side x hxΔ ho hv
        have hψ_eq_ext : ∀ y ∈ hypBall x rx, φ_ext y = ψ y := by
          intro y hy
          rcases hcov hy with hyΔ | hyR
          · rw [hφext_Δ1 y hyΔ, hψ_Δ y ⟨hy, hyΔ⟩]
          · rw [hφext_side j y (by simpa [Metric.mem_ball, dist_zero_right] using hy.1) (hoth y hy) hyR,
              hψ_R y ⟨hy, hyR⟩]
        refine ⟨rx, [[], [j]], hrx_pos, hrx_le, hψ_diff.congr hψ_eq_ext, ?_, ?_⟩
        · intro y hy
          rcases hcov hy with hyΔ | hyR
          · exact mem_iUnion₂.mpr ⟨[], by simp, ⟨y, hyΔ, rfl⟩⟩
          · exact mem_iUnion₂.mpr ⟨[j], by simp, hyR⟩
        · intro u hu y ⟨hy, hyu⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · obtain ⟨z, hzΔ, hzy⟩ := hyu
            simp only [hypWord_nil] at hzy
            subst hzy
            rw [hφext_Δ1 z hzΔ, chartMap_nil]
          · rw [hφext_side j y (by simpa [Metric.mem_ball, dist_zero_right] using hy.1) (hoth y hy) hyu]
  -- Extract a finite subcover of compact `Δ1` by half-radius balls `hypBall x (rx / 2)`!
  choose rx Wx hrx_pos hrx_le hrx_diff hrx_cov hrx_eq using hlocal_chart
  have hcov_Δ1 : Δ1 ⊆ ⋃ (x : Δ1), hypBall x.1 (rx x.1 x.2 / 2) := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, self_mem_hypBall hx.1 (by linarith [hrx_pos x hx])⟩
  obtain ⟨t, ht⟩ := isCompact_Δ1.elim_finite_subcover
    (fun x : Δ1 => hypBall x.1 (rx x.1 x.2 / 2))
    (fun x => isOpen_hypBall x.2.1) hcov_Δ1
  have ht_ne : t.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 : (0 : ℂ) ∈ Δ1 := ⟨zero_mem_Δ1Open.1, fun j => (zero_mem_Δ1Open.2 j).le⟩
    have := ht h0; simp [hemp] at this
  set ρ₀ : ℝ := t.inf' ht_ne (fun p => rx p.1 p.2 / 2)
  have hρ₀_pos : 0 < ρ₀ := by
    rw [Finset.lt_inf'_iff]; intro p _; linarith [hrx_pos p.1 p.2]
  have hρ₀_le : ρ₀ ≤ 1 / 4 := by
    obtain ⟨p, hp⟩ := ht_ne
    have h1 : ρ₀ ≤ rx p.1 p.2 / 2 := Finset.inf'_le _ hp
    linarith [hrx_le p.1 p.2]
  -- Key property of `ρ₀`: for EVERY `x ∈ Δ1`, there is `p ∈ t` such that `hypBall x ρ₀ ⊆ hypBall p.1 (rx p.1 p.2)`!
  have hball_in_chart : ∀ x ∈ Δ1, ∃ p ∈ t, hypBall x ρ₀ ⊆ hypBall p.1 (rx p.1 p.2) := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (ht hx)
    refine ⟨p, hp, fun z ⟨hz1, hdz⟩ => ⟨hz1, ?_⟩⟩
    have htri := hypDist_triangle hz1 hx.1 p.2.1
    have hρ_le_p : ρ₀ ≤ rx p.1 p.2 / 2 := Finset.inf'_le _ hp
    linarith [hxp.2]
  set U : Set ℂ := {z : ℂ | ‖z‖ < 1 ∧ ∃ x ∈ Δ1, hypDist x z < ρ₀}
  have hU_open : IsOpen U := by
    have hU_eq : U = ⋃ (x : Δ1), hypBall x.1 ρ₀ := by
      ext z
      simp only [U, mem_ofPred_eq, mem_iUnion, hypBall, Subtype.exists]
      constructor
      · rintro ⟨hz1, x, hx, hd⟩; exact ⟨x, hx, hz1, by rwa [hypDist_comm]⟩
      · rintro ⟨x, hx, hz1, hd⟩; exact ⟨hz1, x, hx, by rwa [hypDist_comm]⟩
    rw [hU_eq]
    exact isOpen_iUnion fun x => isOpen_hypBall x.2.1
  have hφext_diff : DifferentiableOn ℂ φ_ext U := by
    intro z ⟨hz1, x, hx, hdz⟩
    obtain ⟨p, _, hsub⟩ := hball_in_chart x hx
    have hz_hb : z ∈ hypBall x ρ₀ := ⟨hz1, by rwa [hypDist_comm]⟩
    have hz_p : z ∈ hypBall p.1 (rx p.1 p.2) := hsub hz_hb
    exact ((hrx_diff p.1 p.2).differentiableAt
      ((isOpen_hypBall p.2.1).mem_nhds hz_p)).differentiableWithinAt
  have hderiv0 : deriv φ_ext 0 = 1 := by
    have heq : φ_ext =ᶠ[𝓝 (0 : ℂ)] φ := by
      filter_upwards [isOpen_Δ1Open.mem_nhds zero_mem_Δ1Open] with z hz
      exact hφext_Δ1 z ⟨hz.1, fun j => (hz.2 j).le⟩
    rw [heq.deriv_eq, deriv_φ_zero]
  have hderiv_v : ∀ k : Fin 3, deriv φ_ext (vert1 k) = 0 := by
    intro k
    have heq : φ_ext =ᶠ[𝓝 (vert1 k)] φ_vk k := by
      filter_upwards [(isOpen_hypBall (vert1_mem_ball k)).mem_nhds
        (self_mem_hypBall (vert1_mem_ball k) hδ_pos)] with z hz
      exact hφext_vk k z hz
    rw [heq.deriv_eq, hvk_deriv k]
  -- Uniform continuation property on `hypBall y (ρ₀ / 2)`!
  have hcont_prop : ∀ y : ℂ, ‖y‖ < 1 → (∃ x ∈ Δ1, hypDist x y < ρ₀ / 2) →
      ∃ u : List (Fin 3), y ∈ hypWord u '' Δ1 ∧
        ∀ z ∈ hypBall y (ρ₀ / 2), chartMap u φ_ext z = φ_ext z := by
    intro y hy1 ⟨x, hxΔ, hxy⟩
    obtain ⟨p, _, hsub_p⟩ := hball_in_chart x hxΔ
    have hy_hb : y ∈ hypBall x ρ₀ := ⟨hy1, by rw [hypDist_comm]; linarith⟩
    have hy_p : y ∈ hypBall p.1 (rx p.1 p.2) := hsub_p hy_hb
    obtain ⟨u, huW, hyu⟩ := mem_iUnion₂.mp (hrx_cov p.1 p.2 hy_p)
    refine ⟨u, hyu, ?_⟩
    -- Show `hypBall y (ρ₀ / 2) ⊆ hypBall p.1 (rx p.1 p.2) ⊆ U`!
    have hhb_y_sub_x : hypBall y (ρ₀ / 2) ⊆ hypBall x ρ₀ := by
      intro z ⟨hz1, hzy⟩
      refine ⟨hz1, ?_⟩
      have htri := hypDist_triangle hz1 hy1 hxΔ.1
      rw [hypDist_comm x y] at hxy
      linarith
    have hhb_y_sub_p : hypBall y (ρ₀ / 2) ⊆ hypBall p.1 (rx p.1 p.2) :=
      hhb_y_sub_x.trans hsub_p
    have hhb_y_sub_U : hypBall y (ρ₀ / 2) ⊆ U := fun z hz =>
      ⟨hz.1, x, hxΔ, by rw [hypDist_comm]; exact (hhb_y_sub_x hz).2⟩
    -- Show `hypWord u.reverse '' hypBall y (ρ₀ / 2) ⊆ U`!
    obtain ⟨x', hx'Δ, hx'y⟩ := hyu
    have hrev_y : hypWord u.reverse y = x' := by rw [← hx'y, hypWord_reverse_left _ hx'Δ.1]
    have hrev_sub_U : ∀ z ∈ hypBall y (ρ₀ / 2), hypWord u.reverse z ∈ U := by
      intro z ⟨hz1, hzy⟩
      refine ⟨hypWord_mem_ball _ hz1, x', hx'Δ, ?_⟩
      rw [← hrev_y, hypDist_hypWord u.reverse hy1 hz1, hypDist_comm]
      linarith
    -- Both `chartMap u φ_ext` and `φ_ext` are analytic on connected open `hypBall y (ρ₀ / 2)`!
    have hdiff_L : DifferentiableOn ℂ (chartMap u φ_ext) (hypBall y (ρ₀ / 2)) := by
      intro z hz
      exact (chartMap_differentiableAt u hz.1
        (hφext_diff.differentiableAt (hU_open.mem_nhds (hrev_sub_U z hz)))).differentiableWithinAt
    have hdiff_R : DifferentiableOn ℂ φ_ext (hypBall y (ρ₀ / 2)) := hφext_diff.mono hhb_y_sub_U
    have han_L : AnalyticOnNhd ℂ (chartMap u φ_ext) (hypBall y (ρ₀ / 2)) :=
      hdiff_L.analyticOnNhd (isOpen_hypBall hy1)
    have han_R : AnalyticOnNhd ℂ φ_ext (hypBall y (ρ₀ / 2)) :=
      hdiff_R.analyticOnNhd (isOpen_hypBall hy1)
    -- Find an interior point `z₀ ∈ hypBall y (ρ₀ / 2) ∩ hypWord u '' Δ1Open`!
    have hx'_cl : x' ∈ closure Δ1Open := closure_Δ1Open ▸ hx'Δ
    have hopen_x' : IsOpen (hypBall x' (ρ₀ / 2)) := isOpen_hypBall hx'Δ.1
    obtain ⟨z₀', hz₀'_hb, hz₀'_open⟩ :=
      mem_closure_iff.mp hx'_cl (hypBall x' (ρ₀ / 2)) hopen_x' (self_mem_hypBall hx'Δ.1 (by linarith))
    set z₀ := hypWord u z₀'
    have hz₀_hb : z₀ ∈ hypBall y (ρ₀ / 2) := by
      refine ⟨hypWord_mem_ball _ hz₀'_hb.1, ?_⟩
      rw [← hx'y, hypDist_hypWord u hz₀'_hb.1 hx'Δ.1]
      exact hz₀'_hb.2
    -- On the open neighborhood `W0 := hypBall y (ρ₀ / 2) ∩ hypWord u.reverse ⁻¹' Δ1Open` of `z₀`,
    -- `chartMap u φ_ext = chartMap u φ = φ_ext`!
    set Wz0 : Set ℂ := hypBall y (ρ₀ / 2) ∩ hypWord u.reverse ⁻¹' Δ1Open
    have hWz0_open : IsOpen Wz0 :=
      ((continuousOn_hypWord u.reverse).mono (hypBall_subset_ball _ _)).isOpen_inter_preimage
        (isOpen_hypBall hy1) isOpen_Δ1Open
    have hz₀_Wz0 : z₀ ∈ Wz0 := by
      refine ⟨hz₀_hb, ?_⟩
      change hypWord u.reverse (hypWord u z₀') ∈ Δ1Open
      rwa [hypWord_reverse_left _ hz₀'_hb.1]
    have hev : chartMap u φ_ext =ᶠ[𝓝 z₀] φ_ext := by
      filter_upwards [hWz0_open.mem_nhds hz₀_Wz0] with z ⟨hzhb, hzrev⟩
      have hzrevΔ : hypWord u.reverse z ∈ Δ1 := ⟨hzrev.1, fun j => (hzrev.2 j).le⟩
      have hzu : z ∈ hypWord u '' Δ1 := ⟨hypWord u.reverse z, hzrevΔ, hypWord_reverse_right _ hzhb.1⟩
      rw [hrx_eq p.1 p.2 u huW z ⟨hhb_y_sub_p hzhb, hzu⟩]
      simp only [chartMap, hφext_Δ1 _ hzrevΔ]
    have hconn : IsPreconnected (hypBall y (ρ₀ / 2)) :=
      isPreconnected_hypBall hy1 (by linarith) (by linarith)
    exact han_L.eqOn_of_preconnected_of_eventuallyEq han_R hconn hz₀_hb hev
  exact ⟨ρ₀, φ_ext, hρ₀_pos, hρ₀_le, hU_open, hφext_diff, hφext_Δ1, hderiv0, hderiv_v, hcont_prop⟩

end

end BlochAG

/- ==================== Bloch_Part4.lean ==================== -/
/-
# Ahlfors-Grunsky Upper Bound for Bloch's Constant - Part 4

Global holomorphic continuation `f : ball 0 1 → ℂ` via 1D radial ladder monodromy,
lattice criticality, and final theorem `OMA.solution : OMA.R_Bloch_blochConstant_upper_bound_R1.H1`.
-/

namespace BlochAG

open Complex Real Set Metric Filter Topology

noncomputable section

/- ## 1. Hyperbolic Distance Bound on Subdisks -/

lemma hypDist_le_norm_div {u v : ℂ} {r : ℝ} (hu : ‖u‖ ≤ r) (hv : ‖v‖ ≤ r) (hr : r < 1) :
    hypDist u v ≤ ‖u - v‖ / (1 - r ^ 2) := by
  have hr0 : 0 ≤ r := le_trans (norm_nonneg u) hu
  have h1r : 0 < 1 - r ^ 2 := by nlinarith
  have hden_ge : 1 - r ^ 2 ≤ ‖(1 : ℂ) - starRingEnd ℂ v * u‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) (starRingEnd ℂ v * u)
    rw [norm_one, norm_mul, RCLike.norm_conj] at htri
    have hmul : ‖v‖ * ‖u‖ ≤ r ^ 2 := by nlinarith [norm_nonneg u, norm_nonneg v]
    linarith
  have hden_pos : 0 < ‖(1 : ℂ) - starRingEnd ℂ v * u‖ := lt_of_lt_of_le h1r hden_ge
  unfold hypDist
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) h1r hden_ge

/- ## 2. Valid Continuation Chains and 1D Ladder Monodromy -/

/-- A valid step chain of reflection charts along a discrete path `p : ℕ → ℂ` of length `N`. -/
def ValidChain (φ_ext : ℂ → ℂ) (ρ₀ : ℝ) (p : ℕ → ℂ) (N : ℕ) (W : ℕ → List (Fin 3)) : Prop :=
  W 0 = [] ∧
  (∀ k ≤ N, p k ∈ hypWord (W k) '' Δ1) ∧
  (∀ k < N, ∀ z ∈ hypBall (p (k + 1)) (ρ₀ / 2),
    chartMap (W (k + 1)) φ_ext z = chartMap (W k) φ_ext z)

/-- Radial subdivision path from `0` to `z` in `N` steps. -/
def radPath (z : ℂ) (N k : ℕ) : ℂ :=
  (((k : ℝ) / (N : ℝ) : ℝ) : ℂ) * z

lemma radPath_zero (z : ℂ) (N : ℕ) : radPath z N 0 = 0 := by
  simp [radPath]

lemma radPath_end (z : ℂ) {N : ℕ} (hN : 1 ≤ N) : radPath z N N = z := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp [radPath, div_self hN0]

lemma radPath_norm_le (z : ℂ) {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    ‖radPath z N k‖ ≤ ‖z‖ := by
  unfold radPath
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hN0 : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfrac : (k : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast hk)
  nlinarith [norm_nonneg z]

lemma radPath_sub_norm (z : ℂ) (N k : ℕ) :
    ‖radPath z N k - radPath z N (k + 1)‖ = ‖z‖ / (N : ℝ) := by
  unfold radPath
  rw [← sub_mul, norm_mul]
  have hsub : ((((k : ℝ) / (N : ℝ) : ℝ) : ℂ) - ((((k + 1 : ℕ) : ℝ) / (N : ℝ) : ℝ) : ℂ)) =
      (((-(1 : ℝ) / (N : ℝ) : ℝ) : ℂ)) := by
    push_cast; ring
  rw [hsub, Complex.norm_real, neg_div, norm_neg, Real.norm_of_nonneg (by positivity)]
  ring

/-- Step-size condition ensuring every radial step from `0` to `z` has hyperbolic length `< ρ₀ / 4`. -/
def ValidRadN (ρ₀ : ℝ) (z : ℂ) (N : ℕ) : Prop :=
  1 ≤ N ∧ 1 / ((N : ℝ) * (1 - ‖z‖ ^ 2)) < ρ₀ / 4

lemma exists_validRadN {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ N : ℕ, ValidRadN ρ₀ z N := by
  have hden : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  obtain ⟨N0, hN0⟩ := exists_nat_gt (4 / (ρ₀ * (1 - ‖z‖ ^ 2)))
  refine ⟨max 1 N0, le_max_left _ _, ?_⟩
  have hN_ge : (N0 : ℝ) ≤ ((max 1 N0 : ℕ) : ℝ) := by exact_mod_cast le_max_right 1 N0
  have hN_gt : 4 / (ρ₀ * (1 - ‖z‖ ^ 2)) < ((max 1 N0 : ℕ) : ℝ) := lt_of_lt_of_le hN0 hN_ge
  have hN_pos : (0 : ℝ) < ((max 1 N0 : ℕ) : ℝ) := by
    have : 1 ≤ max 1 N0 := le_max_left _ _
    exact Nat.cast_pos.mpr (by omega)
  have hprod : 0 < ((max 1 N0 : ℕ) : ℝ) * (1 - ‖z‖ ^ 2) := mul_pos hN_pos hden
  rw [div_lt_iff₀ hprod]
  have h1 : 4 < ((max 1 N0 : ℕ) : ℝ) * (ρ₀ * (1 - ‖z‖ ^ 2)) := by
    rwa [div_lt_iff₀ (mul_pos hρ₀ hden)] at hN_gt
  linarith

lemma radPath_step_hypDist {ρ₀ : ℝ} {z : ℂ} (hz : ‖z‖ < 1) {N : ℕ} (hN : ValidRadN ρ₀ z N)
    {k : ℕ} (hk : k < N) :
    hypDist (radPath z N k) (radPath z N (k + 1)) < ρ₀ / 4 := by
  have hu : ‖radPath z N k‖ ≤ ‖z‖ := radPath_norm_le z hN.1 hk.le
  have hv : ‖radPath z N (k + 1)‖ ≤ ‖z‖ := radPath_norm_le z hN.1 hk
  have hle := hypDist_le_norm_div hu hv hz
  rw [radPath_sub_norm z N k] at hle
  have hden : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have h1 : ‖z‖ / (N : ℝ) / (1 - ‖z‖ ^ 2) ≤ 1 / ((N : ℝ) * (1 - ‖z‖ ^ 2)) := by
    rw [div_div]
    exact div_le_div_of_nonneg_right hz.le (mul_pos hN_pos hden).le
  linarith [hN.2]

lemma subdiv_validChain {φ_ext : ℂ → ℂ} {ρ₀ : ℝ} {p : ℕ → ℂ} {N M : ℕ} {W : ℕ → List (Fin 3)}
    (hM : 1 ≤ M) (hW : ValidChain φ_ext ρ₀ p N W) :
    ValidChain φ_ext ρ₀ (fun j => p (j / M)) (M * N) (fun j => W (j / M)) := by
  refine ⟨by simp [hW.1], ?_, ?_⟩
  · intro j hj
    have hdiv : j / M ≤ N := by
      have : j / M ≤ (M * N) / M := Nat.div_le_div_right hj
      rwa [Nat.mul_div_right N (by omega)] at this
    exact hW.2.1 (j / M) hdiv
  · intro j hj z hz
    have hstep : (j + 1) / M = j / M ∨ (j + 1) / M = j / M + 1 := by
      have hdiv : (j + 1) / M = j / M + if M ∣ j + 1 then 1 else 0 := Nat.succ_div
      split_ifs at hdiv <;> omega
    rcases hstep with heq | hsucc
    · simp only [heq]
    · have hlt : j / M < N := Nat.div_lt_of_lt_mul hj
      dsimp only at hz ⊢
      rw [hsucc] at hz ⊢
      exact hW.2.2 (j / M) hlt z hz

/- ## 3. Global Construction of `f` and Proof of `H1` -/

theorem exists_ahlfors_grunsky_func :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) ∧ deriv f 0 = 1 ∧
      ∀ z ∈ ball (0 : ℂ) 1, f z ∈ targetLattice → deriv f z = 0 := by
  classical
  obtain ⟨ρ₀, φ_ext, hρ₀_pos, hρ₀_le, hU_open, hφext_diff, hφext_Δ1, hderiv0, hderiv_v, hcont_prop⟩ :=
    φ_ext_exists
  set U : Set ℂ := {z : ℂ | ‖z‖ < 1 ∧ ∃ x ∈ Δ1, hypDist x z < ρ₀}
  -- Helper: any chart `chartMap w φ_ext` is holomorphic on `hypBall c r` when `y ∈ hypWord w '' Δ1`
  -- and `hypDist c y + r ≤ ρ₀`.
  have hchart_diff_hb : ∀ (w : List (Fin 3)) {c y : ℂ} {r : ℝ},
      ‖c‖ < 1 → y ∈ hypWord w '' Δ1 → hypDist c y + r ≤ ρ₀ →
      DifferentiableOn ℂ (chartMap w φ_ext) (hypBall c r) := by
    intro w c y r hc hy hrad z hz
    obtain ⟨x, hxΔ, hxy⟩ := hy
    have hy1 : ‖y‖ < 1 := by rw [← hxy]; exact hypWord_mem_ball w hxΔ.1
    have hrev_y : hypWord w.reverse y = x := by rw [← hxy, hypWord_reverse_left w hxΔ.1]
    have hzy : hypDist z y < ρ₀ := by
      have htri := hypDist_triangle hz.1 hc hy1
      linarith [hz.2]
    have hrev_U : hypWord w.reverse z ∈ U := by
      refine ⟨hypWord_mem_ball _ hz.1, x, hxΔ, ?_⟩
      rw [← hrev_y, hypDist_hypWord w.reverse hy1 hz.1, hypDist_comm]
      exact hzy
    exact (chartMap_differentiableAt w hz.1
      (hφext_diff.differentiableAt (hU_open.mem_nhds hrev_U))).differentiableWithinAt
  -- Helper: existence of a `ValidChain` along any discrete path with steps `< ρ₀ / 2`.
  have hexists_chain : ∀ (p : ℕ → ℂ) (N : ℕ),
      p 0 = 0 → (∀ k ≤ N, ‖p k‖ < 1) → (∀ k < N, hypDist (p k) (p (k + 1)) < ρ₀ / 2) →
      ∃ W : ℕ → List (Fin 3), ValidChain φ_ext ρ₀ p N W := by
    intro p N
    induction N with
    | zero =>
      intro hp0 _ _
      refine ⟨fun _ => [], rfl, ?_, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      rw [hp0]
      exact ⟨0, ⟨zero_mem_Δ1Open.1, fun j => (zero_mem_Δ1Open.2 j).le⟩, rfl⟩
    | succ N ih =>
      intro hp0 hnorm hstep
      obtain ⟨W, hW0, hWmem, hWagree⟩ :=
        ih hp0 (fun k hk => hnorm k (Nat.le_succ_of_le hk))
          (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
      set w := W N
      obtain ⟨x, hxΔ, hxN⟩ := hWmem N le_rfl
      have hrevN : hypWord w.reverse (p N) = x := by rw [← hxN, hypWord_reverse_left w hxΔ.1]
      set y' := hypWord w.reverse (p (N + 1))
      have hy'1 : ‖y'‖ < 1 := hypWord_mem_ball w.reverse (hnorm (N + 1) le_rfl)
      have hxy' : hypDist x y' < ρ₀ / 2 := by
        rw [← hrevN, hypDist_hypWord w.reverse (hnorm N (Nat.le_succ N)) (hnorm (N + 1) le_rfl)]
        exact hstep N (Nat.lt_succ_self N)
      obtain ⟨u, hy'u, hu_eq⟩ := hcont_prop y' hy'1 ⟨x, hxΔ, hxy'⟩
      refine ⟨fun k => if k ≤ N then W k else w ++ u, ?_, ?_, ?_⟩
      · simp [hW0]
      · intro k hk
        by_cases hkN : k ≤ N
        · simpa [hkN] using hWmem k hkN
        · have hk_eq : k = N + 1 := by omega
          subst k
          simp only [show ¬(N + 1 ≤ N) by omega, ↓reduceIte]
          obtain ⟨x', hx'Δ, hx'y'⟩ := hy'u
          refine ⟨x', hx'Δ, ?_⟩
          dsimp only
          rw [hypWord_append, hx'y', hypWord_reverse_right w (hnorm (N + 1) le_rfl)]
      · intro k hk z hz
        by_cases hkN : k < N
        · have hk1 : k + 1 ≤ N := hkN
          have hk0 : k ≤ N := hkN.le
          simp only [hk1, hk0, ↓reduceIte]
          exact hWagree k hkN z hz
        · have hk_eq : k = N := by omega
          subst k
          simp only [show ¬(N + 1 ≤ N) by omega, le_rfl, ↓reduceIte]
          rw [chartMap_append]
          change eucWord w (chartMap u φ_ext (hypWord w.reverse z)) =
            eucWord w (φ_ext (hypWord w.reverse z))
          congr 1
          apply hu_eq
          refine ⟨hypWord_mem_ball w.reverse hz.1, ?_⟩
          rw [hypDist_hypWord w.reverse hz.1 (hnorm (N + 1) le_rfl)]
          exact hz.2
  -- Key 1D Ladder Lemma: two `N`-step chains within `ρ₀ / 4` at every index define the SAME germ!
  have hladder : ∀ (p q : ℕ → ℂ) (N : ℕ) (W W' : ℕ → List (Fin 3)),
      (∀ k ≤ N, ‖p k‖ < 1 ∧ ‖q k‖ < 1 ∧ hypDist (p k) (q k) < ρ₀ / 4) →
      (∀ k < N, hypDist (p k) (p (k + 1)) < ρ₀ / 4) →
      ValidChain φ_ext ρ₀ p N W →
      ValidChain φ_ext ρ₀ q N W' →
      ∀ k ≤ N, ∀ z ∈ hypBall (p k) (ρ₀ / 4),
        chartMap (W k) φ_ext z = chartMap (W' k) φ_ext z := by
    intro p q N W W' hpq hp_step hW hW' k
    induction k with
    | zero =>
      intro _ z _
      rw [hW.1, hW'.1]
    | succ k ih =>
      intro hk
      have hk_lt : k < N := hk
      have hih := ih (Nat.le_of_succ_le hk)
      have hp1 : ‖p (k + 1)‖ < 1 := (hpq (k + 1) hk).1
      have hq1 : ‖q (k + 1)‖ < 1 := (hpq (k + 1) hk).2.1
      have hpq1 : hypDist (p (k + 1)) (q (k + 1)) < ρ₀ / 4 := (hpq (k + 1) hk).2.2
      have hpk1 : ‖p k‖ < 1 := (hpq k (Nat.le_of_succ_le hk)).1
      set S : Set ℂ := hypBall (p (k + 1)) (ρ₀ / 4)
      have hS_open : IsOpen S := isOpen_hypBall hp1
      have hS_conn : IsPreconnected S := isPreconnected_hypBall hp1 (by linarith) (by linarith)
      have hdiff_L : DifferentiableOn ℂ (chartMap (W (k + 1)) φ_ext) S :=
        hchart_diff_hb (W (k + 1)) hp1 (hW.2.1 (k + 1) hk) (by rw [hypDist_self]; linarith)
      have hdiff_R : DifferentiableOn ℂ (chartMap (W' (k + 1)) φ_ext) S :=
        hchart_diff_hb (W' (k + 1)) hp1 (hW'.2.1 (k + 1) hk) (by linarith)
      have han_L : AnalyticOnNhd ℂ (chartMap (W (k + 1)) φ_ext) S := hdiff_L.analyticOnNhd hS_open
      have han_R : AnalyticOnNhd ℂ (chartMap (W' (k + 1)) φ_ext) S := hdiff_R.analyticOnNhd hS_open
      set z₀ := p (k + 1)
      have hz₀_S : z₀ ∈ S := self_mem_hypBall hp1 (by linarith)
      have hz₀_pk : z₀ ∈ hypBall (p k) (ρ₀ / 4) :=
        ⟨hp1, by rw [hypDist_comm]; exact hp_step k hk_lt⟩
      have hev : chartMap (W (k + 1)) φ_ext =ᶠ[𝓝 z₀] chartMap (W' (k + 1)) φ_ext := by
        filter_upwards [((isOpen_hypBall hpk1).inter hS_open).mem_nhds ⟨hz₀_pk, hz₀_S⟩] with z ⟨hz_pk, hz_S⟩
        have hz_p1_half : z ∈ hypBall (p (k + 1)) (ρ₀ / 2) := ⟨hz_S.1, by linarith [hz_S.2]⟩
        have hz_q1_half : z ∈ hypBall (q (k + 1)) (ρ₀ / 2) := by
          refine ⟨hz_S.1, ?_⟩
          have htri := hypDist_triangle hz_S.1 hp1 hq1
          linarith [hz_S.2]
        rw [hW.2.2 k hk_lt z hz_p1_half, hih z hz_pk, ← hW'.2.2 k hk_lt z hz_q1_half]
      exact han_L.eqOn_of_preconnected_of_eventuallyEq han_R hS_conn hz₀_S hev
  -- Radial step-count invariance: ANY two valid radial chains for `z` agree on `hypBall z (ρ₀ / 4)`!
  have hrad_subdiv_eq : ∀ {z : ℂ} (hz : ‖z‖ < 1) {N M : ℕ} (hN : ValidRadN ρ₀ z N) (hM : 1 ≤ M)
      {W₁ W₂ : ℕ → List (Fin 3)},
      ValidChain φ_ext ρ₀ (radPath z N) N W₁ →
      ValidChain φ_ext ρ₀ (radPath z (M * N)) (M * N) W₂ →
      ∀ x ∈ hypBall z (ρ₀ / 4), chartMap (W₁ N) φ_ext x = chartMap (W₂ (M * N)) φ_ext x := by
    intro z hz N M hN hM W₁ W₂ hW₁ hW₂ x hx
    have hMN : ValidRadN ρ₀ z (M * N) := by
      refine ⟨by nlinarith [hN.1, hM], ?_⟩
      have hden : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by have := hN.1; omega)
      have hM_ge : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hle : (N : ℝ) * (1 - ‖z‖ ^ 2) ≤ ((M * N : ℕ) : ℝ) * (1 - ‖z‖ ^ 2) := by
        push_cast; exact mul_le_mul_of_nonneg_right (by nlinarith) hden.le
      exact lt_of_le_of_lt (div_le_div_of_nonneg_left zero_le_one (mul_pos hN_pos hden) hle) hN.2
    have hW₁_rep := subdiv_validChain hM hW₁
    have hMN_ne : M * N ≠ 0 := by nlinarith [hN.1, hM]
    have hpq : ∀ j ≤ M * N, ‖radPath z (M * N) j‖ < 1 ∧ ‖radPath z N (j / M)‖ < 1 ∧
        hypDist (radPath z (M * N) j) (radPath z N (j / M)) < ρ₀ / 4 := by
      intro j hj
      have hj_div : j / M ≤ N := by
        have := Nat.div_le_div_right (c := M) hj
        rwa [Nat.mul_div_right N (by omega)] at this
      have hu : ‖radPath z (M * N) j‖ ≤ ‖z‖ := radPath_norm_le z hMN.1 hj
      have hv : ‖radPath z N (j / M)‖ ≤ ‖z‖ := radPath_norm_le z hN.1 hj_div
      refine ⟨lt_of_le_of_lt hu hz, lt_of_le_of_lt hv hz, ?_⟩
      have hle := hypDist_le_norm_div hu hv hz
      have hdiff : ‖radPath z (M * N) j - radPath z N (j / M)‖ ≤ ‖z‖ / (N : ℝ) := by
        unfold radPath
        rw [← sub_mul, norm_mul]
        have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
        have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by have := hN.1; omega)
        have hmod_eq : (j : ℝ) = (M : ℝ) * ((j / M : ℕ) : ℝ) + ((j % M : ℕ) : ℝ) := by
          have := (Nat.div_add_mod j M).symm
          exact_mod_cast this
        have hsub : ((((j : ℝ) / ((M * N : ℕ) : ℝ) : ℝ) : ℂ) -
            ((((j / M : ℕ) : ℝ) / (N : ℝ) : ℝ) : ℂ)) =
            (((((j % M : ℕ) : ℝ) / ((M : ℝ) * (N : ℝ)) : ℝ) : ℂ)) := by
          have hsub_r : (j : ℝ) / ((M * N : ℕ) : ℝ) - ((j / M : ℕ) : ℝ) / (N : ℝ) =
              ((j % M : ℕ) : ℝ) / ((M : ℝ) * (N : ℝ)) := by
            push_cast
            rw [hmod_eq]
            field_simp [hM_pos.ne', hN_pos.ne']
            ring
          exact_mod_cast hsub_r
        rw [hsub, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hmod_lt : ((j % M : ℕ) : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast (Nat.mod_lt j (by omega : 0 < M)).le
        have hfrac : ((j % M : ℕ) : ℝ) / ((M : ℝ) * (N : ℝ)) ≤ 1 / (N : ℝ) := by
          rw [div_le_div_iff₀ (mul_pos hM_pos hN_pos) hN_pos]; nlinarith
        calc ((j % M : ℕ) : ℝ) / ((M : ℝ) * (N : ℝ)) * ‖z‖
            ≤ (1 / (N : ℝ)) * ‖z‖ := mul_le_mul_of_nonneg_right hfrac (norm_nonneg z)
          _ = ‖z‖ / (N : ℝ) := by ring
      have hden : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by have := hN.1; omega)
      have h1 : ‖radPath z (M * N) j - radPath z N (j / M)‖ / (1 - ‖z‖ ^ 2) ≤
          1 / ((N : ℝ) * (1 - ‖z‖ ^ 2)) := by
        calc ‖radPath z (M * N) j - radPath z N (j / M)‖ / (1 - ‖z‖ ^ 2)
            ≤ (‖z‖ / (N : ℝ)) / (1 - ‖z‖ ^ 2) := div_le_div_of_nonneg_right hdiff hden.le
          _ = ‖z‖ / ((N : ℝ) * (1 - ‖z‖ ^ 2)) := by rw [div_div]
          _ ≤ 1 / ((N : ℝ) * (1 - ‖z‖ ^ 2)) :=
              div_le_div_of_nonneg_right hz.le (mul_pos hN_pos hden).le
      linarith [hN.2]
    have hstep : ∀ j < M * N, hypDist (radPath z (M * N) j) (radPath z (M * N) (j + 1)) < ρ₀ / 4 :=
      fun j hj => radPath_step_hypDist hz hMN hj
    have heq := hladder (radPath z (M * N)) (fun j => radPath z N (j / M)) (M * N) W₂
      (fun j => W₁ (j / M)) hpq hstep hW₂ hW₁_rep (M * N) le_rfl x
      (by rwa [radPath_end z hMN.1])
    rw [Nat.mul_div_right N (by omega)] at heq
    exact heq.symm
  have hrad_indep : ∀ {z : ℂ} (hz : ‖z‖ < 1) {N₁ N₂ : ℕ}
      (hN₁ : ValidRadN ρ₀ z N₁) (hN₂ : ValidRadN ρ₀ z N₂)
      {W₁ W₂ : ℕ → List (Fin 3)},
      ValidChain φ_ext ρ₀ (radPath z N₁) N₁ W₁ →
      ValidChain φ_ext ρ₀ (radPath z N₂) N₂ W₂ →
      ∀ x ∈ hypBall z (ρ₀ / 4), chartMap (W₁ N₁) φ_ext x = chartMap (W₂ N₂) φ_ext x := by
    intro z hz N₁ N₂ hN₁ hN₂ W₁ W₂ hW₁ hW₂ x hx
    have hN12 : ValidRadN ρ₀ z (N₂ * N₁) := by
      refine ⟨by nlinarith [hN₁.1, hN₂.1], ?_⟩
      have hden : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have hN1_pos : (0 : ℝ) < (N₁ : ℝ) := Nat.cast_pos.mpr (by have := hN₁.1; omega)
      have hN2_ge : (1 : ℝ) ≤ (N₂ : ℝ) := by exact_mod_cast hN₂.1
      have hle : (N₁ : ℝ) * (1 - ‖z‖ ^ 2) ≤ ((N₂ * N₁ : ℕ) : ℝ) * (1 - ‖z‖ ^ 2) := by
        push_cast; exact mul_le_mul_of_nonneg_right (by nlinarith) hden.le
      exact lt_of_le_of_lt (div_le_div_of_nonneg_left zero_le_one (mul_pos hN1_pos hden) hle) hN₁.2
    obtain ⟨W12, hW12⟩ := hexists_chain (radPath z (N₂ * N₁)) (N₂ * N₁) (radPath_zero z _)
      (fun k hk => lt_of_le_of_lt (radPath_norm_le z hN12.1 hk) hz)
      (fun k hk => by linarith [radPath_step_hypDist hz hN12 hk])
    have h1 := hrad_subdiv_eq hz hN₁ hN₂.1 hW₁ hW12 x hx
    have hW12' : ValidChain φ_ext ρ₀ (radPath z (N₁ * N₂)) (N₁ * N₂) W12 := by
      rwa [mul_comm]
    have h2 := hrad_subdiv_eq hz hN₂ hN₁.1 hW₂ hW12' x hx
    rw [mul_comm] at h2
    exact h1.trans h2.symm
  -- Existence of a canonical radial chain for every `z ∈ ball 0 1`!
  have hrad_exists : ∀ z : ℂ, ‖z‖ < 1 →
      ∃ (N : ℕ) (W : ℕ → List (Fin 3)), ValidRadN ρ₀ z N ∧ ValidChain φ_ext ρ₀ (radPath z N) N W := by
    intro z hz
    obtain ⟨N, hN⟩ := exists_validRadN hρ₀_pos hz
    obtain ⟨W, hW⟩ := hexists_chain (radPath z N) N (radPath_zero z N)
      (fun k hk => lt_of_le_of_lt (radPath_norm_le z hN.1 hk) hz)
      (fun k hk => by linarith [radPath_step_hypDist hz hN hk])
    exact ⟨N, W, hN, hW⟩
  choose N_ch W_ch hN_ch hW_ch using hrad_exists
  -- Define the global holomorphic function `f : ℂ → ℂ`!
  let f : ℂ → ℂ := fun z =>
    if hz : ‖z‖ < 1 then chartMap (W_ch z hz (N_ch z hz)) φ_ext z else 0
  have hf_eq_any : ∀ {z : ℂ} (hz : ‖z‖ < 1) {N : ℕ} {W : ℕ → List (Fin 3)},
      ValidRadN ρ₀ z N → ValidChain φ_ext ρ₀ (radPath z N) N W →
      f z = chartMap (W N) φ_ext z := by
    intro z hz N W hN hW
    simp only [f, hz, ↓reduceDIte]
    exact hrad_indep hz (hN_ch z hz) hN (hW_ch z hz) hW z (self_mem_hypBall hz (by linarith))
  -- Key local representation: around EVERY `z₀ ∈ ball 0 1`, `f` agrees on a neighborhood with `chartMap w₀ φ_ext`!
  have hf_local : ∀ z₀ : ℂ, ‖z₀‖ < 1 →
      ∃ w₀ : List (Fin 3), z₀ ∈ hypWord w₀ '' Δ1 ∧ f =ᶠ[𝓝 z₀] chartMap w₀ φ_ext := by
    intro z₀ hz₀
    set r : ℝ := (1 + ‖z₀‖) / 2
    have hz₀_lt_r : ‖z₀‖ < r := by simp only [r]; linarith
    have hr_lt_1 : r < 1 := by simp only [r]; linarith
    have h1r2_pos : 0 < 1 - r ^ 2 := by have : 0 ≤ r := le_trans (norm_nonneg z₀) hz₀_lt_r.le; nlinarith
    obtain ⟨N0, hN0⟩ := exists_nat_gt (4 / (ρ₀ * (1 - r ^ 2)))
    set N : ℕ := max 1 N0
    have hN_ge1 : 1 ≤ N := le_max_left _ _
    have hN_bound : 1 / ((N : ℝ) * (1 - r ^ 2)) < ρ₀ / 4 := by
      have hN_gt : 4 / (ρ₀ * (1 - r ^ 2)) < (N : ℝ) :=
        lt_of_lt_of_le hN0 (by exact_mod_cast le_max_right 1 N0)
      have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
      rw [div_lt_iff₀ (mul_pos hN_pos h1r2_pos)]
      have h1 : 4 < (N : ℝ) * (ρ₀ * (1 - r ^ 2)) := by
        rwa [div_lt_iff₀ (mul_pos hρ₀_pos h1r2_pos)] at hN_gt
      linarith
    have hValid_of_le_r : ∀ {z : ℂ}, ‖z‖ ≤ r → ValidRadN ρ₀ z N := by
      intro z hzr
      refine ⟨hN_ge1, ?_⟩
      have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
      have hden_le : 1 - r ^ 2 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      exact lt_of_le_of_lt
        (div_le_div_of_nonneg_left zero_le_one (mul_pos hN_pos h1r2_pos) (by nlinarith))
        hN_bound
    have hN_z₀ : ValidRadN ρ₀ z₀ N := hValid_of_le_r hz₀_lt_r.le
    obtain ⟨W₀, hW₀⟩ := hexists_chain (radPath z₀ N) N (radPath_zero z₀ N)
      (fun k hk => lt_of_le_of_lt (radPath_norm_le z₀ hN_ge1 hk) hz₀)
      (fun k hk => by linarith [radPath_step_hypDist hz₀ hN_z₀ hk])
    refine ⟨W₀ N, by simpa [radPath_end z₀ hN_ge1] using hW₀.2.1 N le_rfl, ?_⟩
    set δ : ℝ := min ((1 - ‖z₀‖) / 2) ((ρ₀ / 4) * (1 - r ^ 2))
    have hδ_pos : 0 < δ := lt_min (by linarith) (mul_pos (by linarith) h1r2_pos)
    filter_upwards [Metric.ball_mem_nhds z₀ hδ_pos] with z hz_ball
    rw [Metric.mem_ball, dist_eq_norm] at hz_ball
    have hz_r : ‖z‖ ≤ r := by
      have htri := norm_sub_norm_le z z₀
      have hδ1 : δ ≤ (1 - ‖z₀‖) / 2 := min_le_left _ _
      simp only [r]; linarith
    have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz_r hr_lt_1
    have hN_z : ValidRadN ρ₀ z N := hValid_of_le_r hz_r
    obtain ⟨Wz, hWz⟩ := hexists_chain (radPath z N) N (radPath_zero z N)
      (fun k hk => lt_of_le_of_lt (radPath_norm_le z hN_ge1 hk) hz1)
      (fun k hk => by linarith [radPath_step_hypDist hz1 hN_z hk])
    have hpq : ∀ k ≤ N, ‖radPath z₀ N k‖ < 1 ∧ ‖radPath z N k‖ < 1 ∧
        hypDist (radPath z₀ N k) (radPath z N k) < ρ₀ / 4 := by
      intro k hk
      have hu : ‖radPath z₀ N k‖ ≤ r := le_trans (radPath_norm_le z₀ hN_ge1 hk) hz₀_lt_r.le
      have hv : ‖radPath z N k‖ ≤ r := le_trans (radPath_norm_le z hN_ge1 hk) hz_r
      refine ⟨lt_of_le_of_lt hu hr_lt_1, lt_of_le_of_lt hv hr_lt_1, ?_⟩
      have hle := hypDist_le_norm_div hu hv hr_lt_1
      have hsub : ‖radPath z₀ N k - radPath z N k‖ ≤ ‖z - z₀‖ := by
        unfold radPath
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
          norm_sub_rev]
        have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
        have hfrac : (k : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hN_pos).mpr (by exact_mod_cast hk)
        nlinarith [norm_nonneg (z - z₀)]
      have hδ2 : δ ≤ (ρ₀ / 4) * (1 - r ^ 2) := min_le_right _ _
      have hlt : ‖z - z₀‖ / (1 - r ^ 2) < ρ₀ / 4 := by
        rw [div_lt_iff₀ h1r2_pos]; linarith
      have hdiv_le : ‖radPath z₀ N k - radPath z N k‖ / (1 - r ^ 2) ≤ ‖z - z₀‖ / (1 - r ^ 2) :=
        div_le_div_of_nonneg_right hsub h1r2_pos.le
      linarith
    have hz_in_hb : z ∈ hypBall z₀ (ρ₀ / 4) := by
      refine ⟨hz1, ?_⟩
      have hN_pair := (hpq N le_rfl).2.2
      rw [radPath_end z₀ hN_ge1, radPath_end z hN_ge1, hypDist_comm] at hN_pair
      exact hN_pair
    have heq := hladder (radPath z₀ N) (radPath z N) N W₀ Wz hpq
      (fun k hk => radPath_step_hypDist hz₀ hN_z₀ hk) hW₀ hWz N le_rfl z
      (by rwa [radPath_end z₀ hN_ge1])
    rw [hf_eq_any hz1 hN_z hWz, ← heq]
  -- Now verify the three properties of `f`:
  refine ⟨f, ?_, ?_, ?_⟩
  · -- (1) `DifferentiableOn ℂ f (ball 0 1)`
    intro z₀ hz₀
    have hz₀' : ‖z₀‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz₀
    obtain ⟨w₀, hz₀_w, hev⟩ := hf_local z₀ hz₀'
    have hdiff_w : DifferentiableAt ℂ (chartMap w₀ φ_ext) z₀ :=
      (hchart_diff_hb w₀ (r := ρ₀ / 4) hz₀' hz₀_w (by rw [hypDist_self]; linarith)).differentiableAt
        ((isOpen_hypBall hz₀').mem_nhds (self_mem_hypBall hz₀' (by linarith)))
    exact (hdiff_w.congr_of_eventuallyEq hev).differentiableWithinAt
  · -- (2) `deriv f 0 = 1`
    have hnil_eq : f =ᶠ[𝓝 (0 : ℂ)] φ_ext := by
      set r : ℝ := 1 / 2
      have h1r2_pos : (0 : ℝ) < 1 - r ^ 2 := by norm_num [r]
      obtain ⟨N0, hN0⟩ := exists_nat_gt (4 / (ρ₀ * (1 - r ^ 2)))
      set M : ℕ := max 1 N0
      have hM_ge1 : 1 ≤ M := le_max_left _ _
      have hM_bound : 1 / ((M : ℝ) * (1 - r ^ 2)) < ρ₀ / 4 := by
        have hM_gt : 4 / (ρ₀ * (1 - r ^ 2)) < (M : ℝ) :=
          lt_of_lt_of_le hN0 (by exact_mod_cast le_max_right 1 N0)
        have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
        rw [div_lt_iff₀ (mul_pos hM_pos h1r2_pos)]
        have h1 : 4 < (M : ℝ) * (ρ₀ * (1 - r ^ 2)) := by
          rwa [div_lt_iff₀ (mul_pos hρ₀_pos h1r2_pos)] at hM_gt
        have h2 : (M : ℝ) * (ρ₀ * (1 - r ^ 2)) = 4 * (ρ₀ / 4 * ((M : ℝ) * (1 - r ^ 2))) := by ring
        rw [h2] at h1; linarith
      have hW0_nil : ValidChain φ_ext ρ₀ (radPath 0 M) M (fun _ => []) := by
        refine ⟨rfl, ?_, fun k _ z _ => rfl⟩
        intro k _
        simp only [radPath, mul_zero, hypWord_nil]
        exact ⟨0, ⟨zero_mem_Δ1Open.1, fun j => (zero_mem_Δ1Open.2 j).le⟩, rfl⟩
      set δ : ℝ := min (1 / 2) ((ρ₀ / 4) * (1 - r ^ 2))
      have hδ_pos : 0 < δ := lt_min (by norm_num) (mul_pos (by linarith) h1r2_pos)
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ_pos] with z hz_ball
      rw [Metric.mem_ball, dist_zero_right] at hz_ball
      have hz_r : ‖z‖ ≤ r := le_trans hz_ball.le (min_le_left _ _)
      have hz1 : ‖z‖ < 1 := by simp only [r] at hz_r; linarith
      have hM_z : ValidRadN ρ₀ z M := by
        refine ⟨hM_ge1, ?_⟩
        have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
        have hden_le : 1 - r ^ 2 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
        exact lt_of_le_of_lt
          (div_le_div_of_nonneg_left zero_le_one (mul_pos hM_pos h1r2_pos) (by nlinarith))
          hM_bound
      obtain ⟨Wz, hWz⟩ := hexists_chain (radPath z M) M (radPath_zero z M)
        (fun k hk => lt_of_le_of_lt (radPath_norm_le z hM_ge1 hk) hz1)
        (fun k hk => by linarith [radPath_step_hypDist hz1 hM_z hk])
      have hpq : ∀ k ≤ M, ‖radPath 0 M k‖ < 1 ∧ ‖radPath z M k‖ < 1 ∧
          hypDist (radPath 0 M k) (radPath z M k) < ρ₀ / 4 := by
        intro k hk
        have hu : ‖radPath 0 M k‖ ≤ r := by simp [radPath, r]
        have hv : ‖radPath z M k‖ ≤ r := le_trans (radPath_norm_le z hM_ge1 hk) hz_r
        refine ⟨by simp [radPath], lt_of_le_of_lt hv (by norm_num [r]), ?_⟩
        have hle := hypDist_le_norm_div hu hv (by norm_num [r])
        have hsub : ‖radPath 0 M k - radPath z M k‖ ≤ ‖z‖ := by
          simp only [radPath, mul_zero, zero_sub, norm_neg]
          exact radPath_norm_le z hM_ge1 hk
        have hδ2 : δ ≤ (ρ₀ / 4) * (1 - r ^ 2) := min_le_right _ _
        have hlt : ‖z‖ / (1 - r ^ 2) < ρ₀ / 4 := by
          rw [div_lt_iff₀ h1r2_pos]; linarith
        have hdiv_le : ‖radPath 0 M k - radPath z M k‖ / (1 - r ^ 2) ≤ ‖z‖ / (1 - r ^ 2) :=
          div_le_div_of_nonneg_right hsub h1r2_pos.le
        linarith
      have hz_hb0 : z ∈ hypBall (radPath 0 M M) (ρ₀ / 4) := by
        refine ⟨hz1, ?_⟩
        have h := (hpq M le_rfl).2.2
        rw [radPath_end z hM_ge1, hypDist_comm] at h
        exact h
      have heq := hladder (radPath 0 M) (radPath z M) M (fun _ => []) Wz hpq
        (fun k _ => by simp [radPath, hypDist]; linarith) hW0_nil hWz M le_rfl z hz_hb0
      rw [hf_eq_any hz1 hM_z hWz, ← heq, chartMap_nil]
    rw [hnil_eq.deriv_eq, hderiv0]
  · -- (3) Lattice criticality
    intro z₀ hz₀ hlat
    have hz₀' : ‖z₀‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz₀
    obtain ⟨w₀, hz₀_w, hev⟩ := hf_local z₀ hz₀'
    obtain ⟨x, hxΔ, hxw⟩ := hz₀_w
    have hrev : hypWord w₀.reverse z₀ = x := by rw [← hxw, hypWord_reverse_left w₀ hxΔ.1]
    have hf_val : f z₀ = eucWord w₀ (φ x) := by
      have hself := hev.self_of_nhds
      rw [hself]
      simp only [chartMap, hrev, hφext_Δ1 x hxΔ]
    have hφx_lat : φ x ∈ targetLattice := by
      have h1 := eucWord_preserves_lattice w₀.reverse hlat
      rwa [hf_val, eucWord_reverse_left] at h1
    have hφx_Δ2 : φ x ∈ Δ2 := φ_mapsTo hxΔ
    have hvert2 : ∃ k : Fin 3, φ x = vert2 k := by
      rcases lattice_inter_Δ2 hφx_lat hφx_Δ2 with h0 | h1 | h2
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
    obtain ⟨k, hk⟩ := hvert2
    have hx_vert : x = vert1 k := (φ_eq_vert2_iff hxΔ k).mp hk
    have hφext_diff_x : DifferentiableAt ℂ φ_ext (hypWord w₀.reverse z₀) := by
      rw [hrev]
      exact hφext_diff.differentiableAt (hU_open.mem_nhds ⟨hxΔ.1, x, hxΔ, by rw [hypDist_self]; exact hρ₀_pos⟩)
    rw [hev.deriv_eq, chartMap_deriv_eq_zero_iff w₀ hz₀' hφext_diff_x, hrev, hx_vert]
    exact hderiv_v k

end

end BlochAG

theorem OMA.solution : OMA.R_Bloch_blochConstant_upper_bound_R1.H1 := by
  obtain ⟨f, hdiff, hderiv0, hlat⟩ := BlochAG.exists_ahlfors_grunsky_func
  refine ⟨f, hdiff, hderiv0, fun z hz h => hlat z hz ?_⟩
  exact h
