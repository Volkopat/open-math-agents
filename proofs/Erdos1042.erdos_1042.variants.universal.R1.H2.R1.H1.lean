import OMAReductions.R_Erdos1042_erdos_1042_variants_universal_R1_H2_R1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

-- Credit: @Alewawa
-- uses note #34440

/-!
A compact planar set of diameter at most two has transfinite diameter below one if a triangle
in the set fits in no closed unit disk. The triangle forces a uniform bias in the mean of the
sample points projected onto an interval, for a positive measure of directions. A fractional
linear map converts this bias to a strict loss in the Vandermonde bound. The directional
logarithmic integral transfers the loss back to the planar sample.
-/

open Filter Finset MeasureTheory Set Metric Polynomial
open scoped ENNReal Interval Real Topology

namespace OMA.Capacity

private def pairSum {n : ℕ} (f : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Ioi i, f i j

private theorem pairSum_diag {n : ℕ} (f : Fin n → ℝ) :
    pairSum (fun i j => f i + f j) = ((n : ℝ) - 1) * ∑ i, f i := by
  classical
  unfold pairSum
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul]
  have hflip : (∑ i : Fin n, ∑ j ∈ Ioi i, f j) = ∑ j : Fin n, ∑ i ∈ Iio j, f j :=
    sum_comm' (fun i j => by simp)
  rw [hflip, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [sum_const, nsmul_eq_mul, ← add_mul, Fin.card_Ioi, Fin.card_Iio, ← Nat.cast_add]
  have hi := i.isLt
  rw [Nat.sub_add_cancel (by omega : (i : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
  norm_num

private theorem pairSum_const {n : ℕ} (c : ℝ) :
    pairSum (n := n) (fun _ _ => c) = (n.choose 2 : ℝ) * c := by
  have hs := pairSum_diag (fun _ : Fin n => c)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [Nat.cast_choose_two]
  have htwo : pairSum (fun _ _ : Fin n => c + c) = 2 * pairSum (fun _ _ : Fin n => c) := by
    simp [pairSum, two_mul, sum_add_distrib]
  rw [htwo] at hs
  linarith

-- The determinant bound and the final root limit follow @Salofe's corresponding arguments in
-- proofs/Erdos1042.erdos_1042.variants.universal.R1.H1.R1.H1.lean.
private theorem vdm_bound {n : ℕ} {P : ℕ → ℝ[X]}
    (hP : ∀ j, (P j).Monic ∧ (P j).natDegree = j)
    (B : ℕ → ℝ) (hB0 : ∀ j, 0 < B j) (x : Fin n → ℝ)
    (hB : ∀ i j, |(P j).eval (x i)| ≤ B j) :
    |(Matrix.vandermonde x).det| ≤ n.factorial * ∏ j : Fin n, B j := by
  classical
  have hdet := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x (fun j : Fin n => P j)
    (fun j => (hP j).2) (fun j => (hP j).1)
  let N : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => (P j).eval (x i) / B j)
  have hMN : (Matrix.of (fun i j : Fin n => (P j).eval (x i))) =
      Matrix.of (fun (i j : Fin n) => B j * N i j) := by
    ext i j
    simp only [N, Matrix.of_apply]
    field_simp [(hB0 j).ne']
  rw [hdet, hMN, Matrix.det_mul_row]
  have hN : ∀ i j, (IsAbsoluteValue.toAbsoluteValue (abs : ℝ → ℝ)) (N i j) ≤ 1 := by
    intro i j
    change |(P j).eval (x i) / B j| ≤ 1
    rw [abs_div, abs_of_pos (hB0 j), div_le_one (hB0 j)]
    exact hB i j
  have hle := Matrix.det_le hN
  change |N.det| ≤ _ at hle
  simp only [Fintype.card_fin, one_pow, nsmul_eq_mul, mul_one] at hle
  rw [abs_mul, abs_of_nonneg (prod_nonneg fun j : Fin n => fun _ => (hB0 j).le), mul_comm]
  exact mul_le_mul_of_nonneg_right hle (prod_nonneg fun j _ => (hB0 j).le)

private theorem interval_vdm {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    |(Matrix.vandermonde x).det| ≤ (2 * (n : ℝ)) ^ n * (1 / 2 : ℝ) ^ n.choose 2 := by
  let P : ℕ → ℝ[X] := fun j => C ((2 : ℝ) ^ (j - 1))⁻¹ * Chebyshev.T ℝ (j : ℤ)
  have hP (j : ℕ) : (P j).Monic ∧ (P j).natDegree = j := by
    constructor
    · unfold Monic
      simp [P, leadingCoeff_mul, pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
    · simp [P, natDegree_C_mul, pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
  let B : ℕ → ℝ := fun j => 2 * (1 / 2) ^ j
  have hB (i : Fin n) (j : ℕ) : |(P j).eval (x i)| ≤ B j := by
    simp only [P, eval_mul, eval_C, abs_mul, abs_inv, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc _ ≤ ((2 : ℝ) ^ (j - 1))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (Chebyshev.abs_eval_T_real_le_one j (hx i)) (by positivity)
      _ ≤ B j := by
        cases j with
        | zero => norm_num [B]
        | succ j => simp [B, pow_succ]
  have hs : ∑ j : Fin n, (j : ℕ) = n.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => j) n, sum_range_id, Nat.choose_two_right]
  have hp : ∏ j : Fin n, B j = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n.choose 2 := by
    simp only [B, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
      prod_pow_eq_pow_sum, hs]
  have hf : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc _ ≤ n.factorial * ∏ j : Fin n, B j :=
          vdm_bound hP B (fun _ => by positivity) x hB
    _ ≤ _ := by
      rw [hp, mul_pow, mul_comm (2 ^ n) ((n : ℝ) ^ n), mul_assoc]
      exact mul_le_mul_of_nonneg_right hf (by positivity)

private theorem log_det {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) :
    Real.log |(Matrix.vandermonde x).det| = pairSum (fun i j => Real.log (x i - x j)) := by
  rw [Matrix.det_vandermonde, Real.log_abs, Real.log_prod]
  · unfold pairSum
    refine sum_congr rfl fun i _ => ?_
    rw [Real.log_prod (fun j hj => sub_ne_zero.mpr (hx.ne (mem_Ioi.mp hj).ne'))]
    apply sum_congr rfl
    intro j _
    rw [← neg_sub, Real.log_neg_eq_log]
  · exact fun i _ => prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr (hx.ne (mem_Ioi.mp hj).ne')

private theorem interval_log_vdm {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hi : Function.Injective x) :
    pairSum (fun i j => Real.log (x i - x j)) ≤
        Real.log ((2 * (n : ℝ)) ^ n) - (n.choose 2 : ℝ) * Real.log 2 := by
  have hpos : 0 < |(Matrix.vandermonde x).det| := by
    rw [Matrix.det_vandermonde]
    exact abs_pos.mpr (prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun j hj =>
      sub_ne_zero.mpr (hi.ne (mem_Ioi.mp hj).ne'))
  rw [← log_det hi]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := Real.log_le_log hpos (interval_vdm x hx)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow ((1 / 2 : ℝ)), Real.log_div (by norm_num)
    (by norm_num), Real.log_one, zero_sub, mul_neg, ← sub_eq_add_neg] at h
  exact h

/-- An off-center mean strengthens the interval Vandermonde bound by a quadratic loss. -/
private theorem biased_interval_log_vdm {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hi : Function.Injective x) (m : ℝ)
    (hm : ∑ i, x i = n * m) :
    pairSum (fun i j => Real.log (x i - x j)) ≤
        Real.log ((2 * (n : ℝ)) ^ n) - (n.choose 2 : ℝ) * (Real.log 2 + m ^ 2) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hem (f : Fin n → ℝ) (hf : ∀ i, f i ≤ 1) (hfi : Function.Injective f) :
      ∑ i, f i < n := by
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
    have hex : ∃ k, f k < 1 := by
      by_contra! h
      exact hfi.ne hij ((le_antisymm (hf i) (h i)).trans (le_antisymm (hf j) (h j)).symm)
    obtain ⟨k, hk⟩ := hex
    calc ∑ i, f i < ∑ _ : Fin n, (1 : ℝ) := sum_lt_sum (fun i _ => hf i) ⟨k, mem_univ _, hk⟩
      _ = n := by simp
  have hm1 : |m| < 1 := by
    have h₁ := hem x (fun i => (abs_le.mp (hx i)).2) hi
    have h₂ := hem (fun i => -x i) (fun i => by linarith [(abs_le.mp (hx i)).1])
      (fun i j h => hi (neg_inj.mp h))
    rw [hm] at h₁
    rw [sum_neg_distrib, hm, ← mul_neg] at h₂
    exact abs_lt.mpr ⟨by linarith [(mul_lt_mul_iff_of_pos_left hnR).mp (show (n : ℝ) * -m < n * 1 by simpa using h₂)], by
      simpa using (mul_lt_mul_iff_of_pos_left hnR).mp (show (n : ℝ) * m < n * 1 by simpa using h₁)⟩
  let d : Fin n → ℝ := fun i => 1 - m * x i
  let a : ℝ := 1 - m ^ 2
  have ha : 0 < a := by
    dsimp [a]
    have h := (abs_lt.mp hm1)
    nlinarith [mul_pos (sub_pos.mpr h.2) (by linarith : 0 < 1 + m)]
  have hd (i : Fin n) : 0 < d i := by
    have h : |m * x i| < 1 := by
      calc |m * x i| = |m| * |x i| := abs_mul _ _
        _ ≤ |m| * 1 := mul_le_mul_of_nonneg_left (hx i) (abs_nonneg _)
        _ < 1 := by simpa using hm1
    exact sub_pos.mpr (abs_lt.mp h).2
  let y : Fin n → ℝ := fun i => (x i - m) / d i
  have hy (i : Fin n) : |y i| ≤ 1 := by
    rw [abs_le]
    have h := abs_le.mp (hx i)
    have hm' := abs_lt.mp hm1
    constructor
    · rw [show y i = (x i - m) / d i by rfl, le_div_iff₀ (hd i)]
      dsimp [d]
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - m) (by linarith : 0 ≤ 1 + x i)]
    · rw [show y i = (x i - m) / d i by rfl, div_le_iff₀ (hd i)]
      dsimp [d]
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + m) (by linarith : 0 ≤ 1 - x i)]
  have hdiff (i j : Fin n) : y i - y j = a * (x i - x j) / (d i * d j) := by
    dsimp only [y]
    field_simp [(hd i).ne', (hd j).ne']
    dsimp [a, d]
    ring
  have hyi : Function.Injective y := by
    intro i j hij
    apply hi
    have h : y i - y j = 0 := sub_eq_zero.mpr hij
    rw [hdiff, div_eq_zero_iff, mul_eq_zero] at h
    exact sub_eq_zero.mp (h.resolve_right (mul_ne_zero (hd i).ne' (hd j).ne') |>.resolve_left ha.ne')
  have hds : ∑ i, d i = n * a := by
    simp only [d, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, ← mul_sum, hm, a]
    ring
  -- The mean of the denominators is a. Apply log v ≤ v - 1 to their normalized values.
  have hlogs : ∑ i, Real.log (d i) ≤ (n : ℝ) * Real.log a := by
    have h := sum_le_sum (s := (univ : Finset (Fin n))) fun i _ =>
      Real.log_le_sub_one_of_pos (div_pos (hd i) ha)
    simp only [Real.log_div (hd _).ne' ha.ne'] at h
    rw [sum_sub_distrib, sum_sub_distrib, ← sum_div, hds] at h
    simp [ha.ne'] at h
    linarith
  have hterm (i j : Fin n) (hij : i < j) :
      Real.log (x i - x j) =
      Real.log (y i - y j) + (Real.log (d i) + Real.log (d j)) - Real.log a := by
    rw [hdiff, Real.log_div (mul_ne_zero ha.ne' (sub_ne_zero.mpr (hi.ne hij.ne)))
      (mul_ne_zero (hd i).ne' (hd j).ne'), Real.log_mul ha.ne' (sub_ne_zero.mpr (hi.ne hij.ne)),
      Real.log_mul (hd i).ne' (hd j).ne']
    ring
  have hs : pairSum (fun i j => Real.log (x i - x j)) =
      pairSum (fun i j => Real.log (y i - y j)) +
        ((n : ℝ) - 1) * ∑ i, Real.log (d i) - (n.choose 2 : ℝ) * Real.log a := by
    rw [← pairSum_diag, ← pairSum_const]
    unfold pairSum
    simp only [← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j hj => hterm i j (mem_Ioi.mp hj)
  have hchoose := Nat.cast_choose_two (K := ℝ) n
  have hn1 : 0 ≤ (n : ℝ) - 1 := by
    have h : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    linarith
  have hlog := mul_le_mul_of_nonneg_left hlogs hn1
  have hb := interval_log_vdm hn y hy hyi
  have haLog : Real.log a ≤ -(m ^ 2) := by linarith [Real.log_le_sub_one_of_pos ha]
  have hfin := mul_le_mul_of_nonneg_left haLog (Nat.cast_nonneg (n.choose 2) : (0 : ℝ) ≤ _)
  rw [hs]
  nlinarith [congrArg (fun v : ℝ => v * Real.log a) hchoose]

private noncomputable def projection (θ : ℝ) (w : ℂ) : ℝ :=
  (Complex.exp ((θ : ℂ) * Complex.I) * w).re

private theorem projection_sub (θ : ℝ) (z w : ℂ) :
    projection θ (z - w) = projection θ z - projection θ w := by
  simp [projection, mul_sub]

private theorem projection_le (θ : ℝ) (w : ℂ) : projection θ w ≤ ‖w‖ := by
  unfold projection
  exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans_eq
    (by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]))

private theorem projection_eq_cos (θ : ℝ) (w : ℂ) :
    projection θ w = ‖w‖ * Real.cos (θ + w.arg) := by
  have h : Complex.exp ((θ : ℂ) * Complex.I) * w =
      (‖w‖ : ℂ) * Complex.exp (((θ + w.arg : ℝ) : ℂ) * Complex.I) := by
    calc _ = Complex.exp ((θ : ℂ) * Complex.I) *
          ((‖w‖ : ℂ) * Complex.exp ((w.arg : ℂ) * Complex.I)) := by
            rw [Complex.norm_mul_exp_arg_mul_I]
      _ = _ := by
        rw [mul_left_comm, ← Complex.exp_add, Complex.ofReal_add, add_mul]
  rw [projection, h, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

private theorem ae_cos_nonzero (s : ℝ) :
    ∀ᵐ θ : ℝ, Real.cos (θ + s) ≠ 0 := by
  have hc : (Set.range (fun k : ℤ => (2 * (k : ℝ) + 1) * Real.pi / 2 - s)).Countable :=
    countable_range _
  filter_upwards [hc.ae_notMem volume] with θ hθ hz
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hz
  exact hθ ⟨k, by linarith⟩

private theorem ae_projection_nonzero (s : ℝ) {w : ℂ} (hw : w ≠ 0) :
    ∀ᵐ θ : ℝ, projection (θ + s) w ≠ 0 := by
  filter_upwards [ae_cos_nonzero (s + w.arg)] with θ hθ
  rw [projection_eq_cos, add_assoc]
  exact mul_ne_zero (norm_ne_zero_iff.mpr hw) hθ

private theorem ae_log_projection (s : ℝ) {w : ℂ} (hw : w ≠ 0) :
    (fun θ => Real.log (projection (θ + s) w)) =ᵐ[volume]
      (fun θ => Real.log ‖w‖ + Real.log (Real.cos (θ + (s + w.arg)))) := by
  filter_upwards [ae_cos_nonzero (s + w.arg)] with θ hθ
  rw [projection_eq_cos, add_assoc, Real.log_mul (norm_ne_zero_iff.mpr hw) hθ]

private theorem shifted_log_cos_integrable (s a b : ℝ) :
    IntervalIntegrable (fun θ => Real.log (Real.cos (θ + s))) volume a b := by
  simpa [Function.comp_def] using
    (intervalIntegrable_log_cos (a := a + s) (b := b + s)).comp_add_right s

private theorem projection_integrable (s : ℝ) {w : ℂ} (hw : w ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun θ => Real.log (projection (θ + s) w)) volume a b :=
  ((intervalIntegrable_const).add (shifted_log_cos_integrable (s + w.arg) a b)).congr_ae
    (ae_log_projection s hw).symm.restrict

/-- Integrating the log of a projected length over a half-turn subtracts log 2 from its mean. -/
private theorem integral_log_projection (s : ℝ) {w : ℂ} (hw : w ≠ 0) :
    ∫ θ in 0..Real.pi, Real.log (projection (θ + s) w) =
      Real.pi * (Real.log ‖w‖ - Real.log 2) := by
  have hcongr := ae_log_projection s hw
  rw [intervalIntegral.integral_congr_ae (hcongr.mono fun _ h _ => h)]
  let t := s + w.arg + Real.pi / 2
  have hper : Function.Periodic (fun θ => Real.log (Real.sin θ)) Real.pi := by
    intro θ
    simp [Real.sin_add_pi, Real.log_neg_eq_log]
  have hcos : (fun θ => Real.log (Real.cos (θ + (s + w.arg)))) =
      fun θ => Real.log (Real.sin (θ + t)) := by
    funext θ
    rw [← Real.sin_add_pi_div_two, add_assoc]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (shifted_log_cos_integrable (s + w.arg) 0 Real.pi),
    intervalIntegral.integral_const, hcos,
    intervalIntegral.integral_comp_add_right (fun θ => Real.log (Real.sin θ)) t, zero_add,
    add_comm Real.pi t, hper.intervalIntegral_add_eq t 0, zero_add, integral_log_sin_zero_pi]
  simp [smul_eq_mul]
  ring

private theorem triangle_margin (T : Finset ℂ) (hT : T.card = 3)
    (hcover : ∀ c : ℂ, ¬ (T : Set ℂ) ⊆ closedBall c 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : ℂ, ‖c‖ ≤ 2 → ∃ t ∈ T, 1 + ε ≤ ‖t - c‖ := by
  classical
  obtain ⟨u, v, w, _, _, _, ht⟩ := Finset.card_eq_three.mp hT
  let F (c : ℂ) := max ‖u - c‖ (max ‖v - c‖ ‖w - c‖)
  have hc : Continuous F := by unfold F; fun_prop
  have hhit (c : ℂ) : ∃ t ∈ T, F c = ‖t - c‖ := by
    rcases max_cases ‖u - c‖ (max ‖v - c‖ ‖w - c‖) with h | h
    · exact ⟨u, by simp [ht], h.1⟩
    · rcases max_cases ‖v - c‖ ‖w - c‖ with h' | h'
      · exact ⟨v, by simp [ht], h.1.trans h'.1⟩
      · exact ⟨w, by simp [ht], h.1.trans h'.1⟩
  have hgt (c : ℂ) : 1 < F c := by
    by_contra! h
    apply hcover c
    intro t ht'
    change t ∈ T at ht'
    rw [ht, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ht'
    have h' := max_le_iff.mp h
    rw [mem_closedBall, dist_eq_norm]
    rcases ht' with rfl | rfl | rfl
    · exact h'.1
    · exact (max_le_iff.mp h'.2).1
    · exact (max_le_iff.mp h'.2).2
  obtain ⟨c₀, _, hc₀⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_isMinOn
    ⟨0, mem_closedBall_self (by norm_num)⟩ hc.continuousOn
  refine ⟨F c₀ - 1, sub_pos.mpr (hgt c₀), fun c hcn => ?_⟩
  obtain ⟨t, ht, hFt⟩ := hhit c
  refine ⟨t, ht, ?_⟩
  have hmin := (isMinOn_iff.mp hc₀) c (by simpa [mem_closedBall, dist_zero_right] using hcn)
  linarith

private theorem angular_margin {ε : ℝ} (he : 0 < ε) :
    ∃ α : ℝ, 0 < α ∧ α < Real.pi ∧
      ∀ θ ∈ Set.Icc 0 α, 1 + ε / 2 ≤ (1 + ε) * Real.cos θ := by
  have hcont : ContinuousAt (fun θ : ℝ => (1 + ε) * Real.cos θ) 0 :=
    (continuous_const.mul Real.continuous_cos).continuousAt
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hcont (ε / 2) (by positivity)
  let α := min (δ / 2) (Real.pi / 2)
  have ha : 0 < α := lt_min (by positivity) (by positivity)
  have hapi : α < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  refine ⟨α, ha, hapi, fun θ hθ => ?_⟩
  have hdist : dist θ 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hθ.1]
    exact hθ.2.trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have h := hnear hdist
  rw [Real.dist_eq, Real.cos_zero, mul_one] at h
  linarith [(abs_lt.mp h).1]

private theorem normalized_projection (G : Set ℂ) (hG : IsCompact G) (h0 : (0:ℂ) ∈ G)
    (hdiam : ∀ z ∈ G, ∀ w ∈ G, dist z w ≤ 2)
    {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℂ) (hz : ∀ i, z i ∈ G)
    (t : ℂ) (ht : t ∈ G) (θ : ℝ) :
    ∃ b : ℝ, projection θ t ≤ b ∧ (∀ i, |projection θ (z i) - b + 1| ≤ 1) ∧
      ∑ i, (projection θ (z i) - b + 1) =
        n * (projection θ (((n : ℝ)⁻¹ : ℂ) * ∑ i, z i) - b + 1) := by
  have hcont : Continuous (projection θ) := by unfold projection; fun_prop
  obtain ⟨zₘ, hzm, hmax⟩ := hG.exists_isMaxOn ⟨0, h0⟩ hcont.continuousOn
  let b := projection θ zₘ
  refine ⟨b, isMaxOn_iff.mp hmax t ht, fun i => ?_, ?_⟩
  · have hupper := isMaxOn_iff.mp hmax (z i) (hz i)
    have hlower : projection θ (zₘ - z i) ≤ 2 := (projection_le θ (zₘ - z i)).trans (by
      rw [← dist_eq_norm]; exact hdiam zₘ hzm (z i) (hz i))
    rw [projection_sub] at hlower
    exact abs_le.mpr ⟨by dsimp [b]; linarith, by dsimp [b]; linarith⟩
  · have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have havg : projection θ (((n : ℝ)⁻¹ : ℂ) * ∑ i, z i) =
        (n : ℝ)⁻¹ * ∑ i, projection θ (z i) := by
      unfold projection
      rw [mul_left_comm, ← Complex.ofReal_inv, Complex.re_ofReal_mul, mul_sum, Complex.re_sum]
    rw [havg]
    simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    field_simp

private theorem inner_pair_integrable {n : ℕ} {z : Fin n → ℂ} (hi : Function.Injective z)
    (s a b : ℝ) (i : Fin n) : IntervalIntegrable
      (fun θ => ∑ j ∈ Ioi i, Real.log (projection (θ + s) (z i - z j))) volume a b := by
  have heq : (fun θ : ℝ => ∑ j ∈ Ioi i, Real.log (projection (θ + s) (z i - z j))) =
      ∑ j ∈ Ioi i, fun θ : ℝ => Real.log (projection (θ + s) (z i - z j)) := by
    funext θ
    rw [Finset.sum_apply]
  rw [heq]
  exact IntervalIntegrable.sum (Ioi i) (fun j hj =>
    projection_integrable s (sub_ne_zero.mpr (hi.ne (Finset.mem_Ioi.mp hj).ne)) a b)

private theorem pair_integrable {n : ℕ} {z : Fin n → ℂ} (hi : Function.Injective z)
    (s a b : ℝ) :
    IntervalIntegrable (fun θ => pairSum (fun i j => Real.log (projection (θ + s) (z i - z j))))
      volume a b := by
  have heq : (fun θ : ℝ => pairSum (fun i j => Real.log (projection (θ + s) (z i - z j)))) =
      ∑ i : Fin n, fun θ : ℝ => ∑ j ∈ Ioi i, Real.log (projection (θ + s) (z i - z j)) := by
    funext θ
    rw [Finset.sum_apply, pairSum]
  rw [heq]
  exact IntervalIntegrable.sum univ (fun i _ => inner_pair_integrable hi s a b i)

private theorem integral_pairSum {n : ℕ} {z : Fin n → ℂ} (hi : Function.Injective z)
    (s : ℝ) :
    ∫ θ in 0..Real.pi, pairSum (fun i j => Real.log (projection (θ + s) (z i - z j))) =
      Real.pi * (pairSum (fun i j => Real.log ‖z i - z j‖) - (n.choose 2 : ℝ) * Real.log 2) := by
  rw [← pairSum_const]
  unfold pairSum
  rw [intervalIntegral.integral_finsetSum (fun i _ => inner_pair_integrable hi s 0 Real.pi i), mul_sub, mul_sum, mul_sum,
    ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun j hj =>
    projection_integrable s (sub_ne_zero.mpr (hi.ne (Finset.mem_Ioi.mp hj).ne)) 0 Real.pi),
    mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j hj => ?_
  rw [integral_log_projection s (sub_ne_zero.mpr (hi.ne (Finset.mem_Ioi.mp hj).ne)), mul_sub]

/-- The triangle forces a loss proportional to the number of pairs, uniformly in the sample. -/
private theorem strict_log_bound (G : Set ℂ) (hG : IsCompact G) (h0 : (0:ℂ) ∈ G)
    (hdiam : ∀ z ∈ G, ∀ w ∈ G, dist z w ≤ 2)
    (T : Finset ℂ) (hT : T.card = 3) (hsub : (T : Set ℂ) ⊆ G)
    (hcover : ∀ c : ℂ, ¬ (T : Set ℂ) ⊆ closedBall c 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 2 ≤ n → ∀ z : Fin n → ℂ,
      (∀ i, z i ∈ G) → Function.Injective z →
      pairSum (fun i j => Real.log ‖z i - z j‖) ≤
        Real.log ((2 * (n : ℝ)) ^ n) - (n.choose 2 : ℝ) * η := by
  obtain ⟨ε, he, hε⟩ := triangle_margin T hT hcover
  obtain ⟨α, ha, hapi, hcos⟩ := angular_margin he
  refine ⟨α * (ε / 2) ^ 2 / Real.pi, by positivity, fun n hn z hz hi => ?_⟩
  let c : ℂ := ((n : ℝ)⁻¹ : ℂ) * ∑ i, z i
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : ‖c‖ ≤ 2 := by
    rw [show c = ((↑((n : ℝ)⁻¹) : ℂ) * ∑ i, z i) by simp [c], norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnR)]
    have hsum : ‖∑ i, z i‖ ≤ (n : ℝ) * 2 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖z i‖ ≤ ∑ _ : Fin n, (2 : ℝ) := sum_le_sum fun i _ => by
            simpa only [dist_zero_right] using hdiam (z i) (hz i) 0 h0
        _ = (n : ℝ) * 2 := by simp
    calc (n : ℝ)⁻¹ * ‖∑ i, z i‖ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * 2) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnR.le)
      _ = 2 := by rw [← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul]
  obtain ⟨t, ht, htc⟩ := hε c hc
  let s := -(t - c).arg
  have hproj (θ : ℝ) (hθ : θ ∈ Set.Icc 0 α) :
      1 + ε / 2 ≤ projection (θ + s) (t - c) := by
    rw [projection_eq_cos, show θ + s + (t - c).arg = θ by dsimp [s]; ring]
    have hh := hcos θ hθ
    have hcos0 : 0 ≤ Real.cos θ := by
      by_contra! h
      linarith [mul_neg_of_pos_of_neg (by linarith : 0 < 1 + ε) h]
    exact hh.trans (mul_le_mul_of_nonneg_right htc hcos0)
  have hgeneric : ∀ᵐ θ : ℝ, Function.Injective (fun i : Fin n => projection (θ + s) (z i)) := by
    have hh : ∀ᵐ θ : ℝ, ∀ i j : Fin n, i ≠ j → projection (θ + s) (z i - z j) ≠ 0 := by
      rw [ae_all_iff]
      intro i
      rw [ae_all_iff]
      intro j
      by_cases hij : i = j
      · simp [hij]
      · exact (ae_projection_nonzero s (sub_ne_zero.mpr (hi.ne hij))).mono fun _ h _ => h
    filter_upwards [hh] with θ hθ i j hij
    by_contra! h
    exact hθ i j h (by rw [projection_sub]; exact sub_eq_zero.mpr hij)
  let D : ℝ := n.choose 2
  let C : ℝ := Real.log ((2 * (n : ℝ)) ^ n) - D * Real.log 2
  let F : ℝ → ℝ := fun θ => pairSum (fun i j => Real.log (projection (θ + s) (z i - z j)))
  have hD : 0 ≤ D := by positivity
  have hbound (θ : ℝ) (hθ : Function.Injective (fun i : Fin n => projection (θ + s) (z i))) :
      ∃ m : ℝ, F θ ≤ C - D * m ^ 2 ∧ (θ ∈ Set.Icc 0 α → m ≤ -(ε / 2)) := by
    obtain ⟨b, hbt, hb, hm⟩ := normalized_projection G hG h0 hdiam hn z hz t (hsub ht) (θ + s)
    let x : Fin n → ℝ := fun i => projection (θ + s) (z i) - b + 1
    let m : ℝ := projection (θ + s) c - b + 1
    have hxi : Function.Injective x := by
      intro i j hij
      apply hθ
      dsimp [x] at hij
      linarith
    refine ⟨m, ?_, fun hangle => ?_⟩
    · have hh := biased_interval_log_vdm hn x hb hxi m hm
      have heq : F θ = pairSum (fun i j => Real.log (x i - x j)) := by
        unfold F pairSum
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        dsimp only
        rw [projection_sub]
        congr 1
        dsimp [x]
        ring
      rw [heq]
      dsimp [C, D]
      linarith
    · have hh := hproj θ hangle
      rw [projection_sub] at hh
      dsimp [m]
      linarith
  have hint1 : (∫ θ in 0..α, F θ) ≤ α * (C - D * (ε / 2) ^ 2) := by
    have hh : (∫ θ in 0..α, F θ) ≤ ∫ _ in 0..α, (C - D * (ε / 2) ^ 2) := by
      apply intervalIntegral.integral_mono_ae_restrict ha.le
        (pair_integrable hi s 0 α) intervalIntegrable_const
      filter_upwards [ae_mono (Measure.restrict_le_self (s := Set.Icc 0 α)) hgeneric, ae_restrict_mem measurableSet_Icc]
        with θ hθ hmem
      obtain ⟨m, hm, hml⟩ := hbound θ hθ
      have hsq : (ε / 2) ^ 2 ≤ m ^ 2 := by
        have h := hml hmem
        nlinarith
      exact hm.trans (sub_le_sub_left (mul_le_mul_of_nonneg_left hsq hD) C)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hh
  have hint2 : (∫ θ in α..Real.pi, F θ) ≤ (Real.pi - α) * C := by
    have hh : (∫ θ in α..Real.pi, F θ) ≤ ∫ _ in α..Real.pi, C := by
      apply intervalIntegral.integral_mono_ae hapi.le
        (pair_integrable hi s α Real.pi) intervalIntegrable_const
      filter_upwards [hgeneric] with θ hθ
      obtain ⟨m, hm, _⟩ := hbound θ hθ
      exact hm.trans (sub_le_self _ (by positivity))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hh
  have hsum := add_le_add hint1 hint2
  rw [intervalIntegral.integral_add_adjacent_intervals (pair_integrable hi s 0 α)
    (pair_integrable hi s α Real.pi)] at hsum
  have htotal := integral_pairSum hi s
  change (∫ θ in 0..Real.pi, F θ) = _ at htotal
  rw [htotal] at hsum
  apply (mul_le_mul_iff_of_pos_left Real.pi_pos).mp
  have hcancel : Real.pi * (D * (α * (ε / 2) ^ 2 / Real.pi)) = α * (D * (ε / 2) ^ 2) := by
    field_simp
  change Real.pi * _ ≤ Real.pi * (Real.log ((2 * (n : ℝ)) ^ n) -
    D * (α * (ε / 2) ^ 2 / Real.pi))
  rw [mul_sub, hcancel]
  dsimp [C, D] at hsum ⊢
  linarith

/-- The root of `(c n)^n` of order `n choose 2` tends to one. -/
private theorem root_lim (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => ((c * n) ^ n) ^ (1 / ((n.choose 2 : ℕ) : ℝ))) atTop (𝓝 1) := by
  have hscale : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hlog : Tendsto (fun n : ℕ => Real.log (c * n) / ((n : ℝ) - 1)) atTop (𝓝 0) := by
    refine ((Real.tendsto_pow_log_div_mul_add_atTop (1 / c) (-1) 1
      (by positivity)).comp hscale).congr ?_
    intro n
    simp only [Function.comp_apply, pow_one]
    congr 1
    field_simp
    ring
  have hexp : Tendsto (fun n : ℕ => Real.exp (2 * (Real.log (c * n) / ((n : ℝ) - 1))))
      atTop (𝓝 1) := by
    have := hlog.const_mul 2
    rw [mul_zero] at this
    have h2 := (Real.continuous_exp.tendsto 0).comp this
    rw [Real.exp_zero] at h2
    exact h2
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (c * n) ^ n := by positivity
  rw [Real.rpow_def_of_pos hpos, Real.log_pow, Nat.cast_choose_two]
  have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (n : ℝ) ≠ 0 := by linarith
  congr 1
  field_simp

private theorem td_lt_one (G : Set ℂ) (hG : IsCompact G) (h0 : (0:ℂ) ∈ G)
    (hdiam : ∀ z ∈ G, ∀ w ∈ G, dist z w ≤ 2)
    (T : Finset ℂ) (hT : T.card = 3) (hsub : (T : Set ℂ) ⊆ G)
    (hcover : ∀ c : ℂ, ¬ (T : Set ℂ) ⊆ closedBall c 1) :
    Erdos1042.transfiniteDiameter G < 1 := by
  obtain ⟨η, hη, hlog⟩ := strict_log_bound G hG h0 hdiam T hT hsub hcover
  let ρ := Real.exp (-η)
  have hρ : ρ < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hη)
  have hbound (n : ℕ) (hn : 2 ≤ n) : Erdos1042.nthDiameter G n ≤
      ENNReal.ofReal (((2 * (n : ℝ)) ^ n) ^ (1 / (n.choose 2 : ℝ)) * ρ) := by
    unfold Erdos1042.nthDiameter
    refine iSup_le fun z => iSup_le fun hz => ?_
    have hD : (0 : ℝ) < n.choose 2 := by exact_mod_cast Nat.choose_pos hn
    have hprod : (∏ i : Fin n, ∏ j ∈ Ioi i, edist (z i) (z j)) =
        ENNReal.ofReal (∏ i : Fin n, ∏ j ∈ Ioi i, ‖z i - z j‖) := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => prod_nonneg fun _ _ => norm_nonneg _)]
      refine prod_congr rfl fun i _ => ?_
      rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
      exact prod_congr rfl fun j _ => by rw [edist_dist, dist_eq_norm]
    let P : ℝ := ∏ i : Fin n, ∏ j ∈ Ioi i, ‖z i - z j‖
    change _ = ENNReal.ofReal P at hprod
    have hP : 0 ≤ P := prod_nonneg fun _ _ => prod_nonneg fun _ _ => norm_nonneg _
    rw [hprod, ENNReal.ofReal_rpow_of_nonneg hP (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    by_cases hi : Function.Injective z
    · have hne i j (hij : i < j) : ‖z i - z j‖ ≠ 0 :=
        norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hi.ne hij.ne))
      have hPpos : 0 < P := lt_of_le_of_ne hP (Ne.symm (prod_ne_zero_iff.mpr fun i _ =>
        prod_ne_zero_iff.mpr fun j hj => hne i j (Finset.mem_Ioi.mp hj)))
      have hsum : Real.log P = pairSum (fun i j => Real.log ‖z i - z j‖) := by
        unfold P pairSum
        rw [Real.log_prod (fun i _ => prod_ne_zero_iff.mpr fun j hj =>
          hne i j (Finset.mem_Ioi.mp hj))]
        exact sum_congr rfl fun i _ => Real.log_prod fun j hj => hne i j (Finset.mem_Ioi.mp hj)
      have hh := hlog n hn z hz hi
      rw [← hsum] at hh
      have hBn : (0 : ℝ) < (2 * (n : ℝ)) ^ n := by
        have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        positivity
      dsimp only [ρ]
      rw [Real.rpow_def_of_pos hPpos, Real.rpow_def_of_pos hBn, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      calc _ ≤ (Real.log ((2 * (n : ℝ)) ^ n) - (n.choose 2 : ℝ) * η) *
            (1 / (n.choose 2 : ℝ)) := mul_le_mul_of_nonneg_right hh (by positivity)
        _ = _ := by
          field_simp
          ring
    · unfold Function.Injective at hi
      push Not at hi
      obtain ⟨i, j, hij, hne⟩ := hi
      have hpzero (i j : Fin n) (hij : i < j) (heq : z i = z j) : P = 0 := by
        apply prod_eq_zero (mem_univ i)
        exact prod_eq_zero (Finset.mem_Ioi.mpr hij) (by rw [heq, sub_self, norm_zero])
      have hzero : P = 0 := (lt_or_gt_of_ne hne).elim (fun h => hpzero i j h hij)
        (fun h => hpzero j i h hij.symm)
      rw [hzero, Real.zero_rpow (by positivity : (1 / (n.choose 2 : ℝ)) ≠ 0)]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (((2 * (n : ℝ)) ^ n) ^
      (1 / (n.choose 2 : ℝ)) * ρ)) atTop (𝓝 (ENNReal.ofReal ρ)) := by
    have h := (root_lim 2 (by norm_num)).mul_const ρ
    rw [one_mul] at h
    exact (ENNReal.continuous_ofReal.tendsto ρ).comp h
  have hle : Erdos1042.transfiniteDiameter G ≤ ENNReal.ofReal ρ := by
    unfold Erdos1042.transfiniteDiameter
    rw [← hlim.limsup_eq]
    exact limsup_le_limsup ((eventually_ge_atTop 2).mono fun n hn => hbound n hn)
  refine hle.trans_lt ?_
  rw [← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hρ

end OMA.Capacity

theorem OMA.solution : OMA.R_Erdos1042_erdos_1042_variants_universal_R1_H2_R1.H1 := by
  intro G r _ hr hG hcap h0 _ hdiam _ T hT hsub hcover _
  exfalso
  have h := Capacity.td_lt_one G hG h0 (fun z hz w hw => (hdiam z hz w hw).trans hr)
    T hT hsub hcover
  rw [hcap] at h
  exact (lt_irrefl _ h)
