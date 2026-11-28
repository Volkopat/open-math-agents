import OMAStatements.S_mse_1250537

-- The stated first continued-fraction coefficient is incompatible with the lattice sums.
-- The constant and linear coefficients eliminate the common Gamma normalization.

namespace MSE1250537Proof

noncomputable def lattice (z : ℤ × ℤ) : ℂ :=
  (z.1 : ℂ) * Complex.exp (-2 * Complex.I * (Real.pi : ℂ) / 3) +
  (z.2 : ℂ) * Complex.exp (2 * Complex.I * (Real.pi : ℂ) / 3)

noncomputable def window : Finset (ℤ × ℤ) :=
  (Finset.Icc (-5 : ℤ) 5).product (Finset.Icc (-5 : ℤ) 5)

noncomputable def latticeTerm (k : ℕ) (z : ℤ × ℤ) : ℂ :=
  (lattice z ^ k)⁻¹

end MSE1250537Proof

namespace MSE1250537Proof

open scoped BigOperators

theorem positiveAngle : 2 * Complex.I * (Real.pi : ℂ) / 3 =
    (↑(Real.pi - Real.pi / 3) : ℂ) * Complex.I := by
  push_cast
  ring

theorem negativeAngle : -2 * Complex.I * (Real.pi : ℂ) / 3 =
    (↑(-(Real.pi - Real.pi / 3)) : ℂ) * Complex.I := by
  push_cast
  ring

theorem lattice_re (z : ℤ × ℤ) : (lattice z).re = -((z.1 : ℝ) + (z.2 : ℝ)) / 2 := by
  simp only [lattice, Complex.add_re, Complex.mul_re, Complex.intCast_re,
    Complex.intCast_im, zero_mul, sub_zero, negativeAngle, positiveAngle,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_three]
  ring

theorem lattice_im (z : ℤ × ℤ) :
    (lattice z).im = ((z.2 : ℝ) - (z.1 : ℝ)) * Real.sqrt 3 / 2 := by
  simp only [lattice, Complex.add_im, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, add_zero, negativeAngle, positiveAngle,
    Complex.exp_ofReal_mul_I_im, Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_three]
  ring

theorem lattice_im_sq (z : ℤ × ℤ) :
    (lattice z).im ^ 2 = 3 * ((z.2 : ℝ) - (z.1 : ℝ)) ^ 2 / 4 := by
  rw [lattice_im]
  calc
    (((z.2 : ℝ) - (z.1 : ℝ)) * Real.sqrt 3 / 2) ^ 2 =
        ((z.2 : ℝ) - (z.1 : ℝ)) ^ 2 * (Real.sqrt 3) ^ 2 / 4 := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring

theorem normSq_lattice (z : ℤ × ℤ) :
    Complex.normSq (lattice z) = (z.1 : ℝ) ^ 2 - (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2 := by
  rw [Complex.normSq_apply, ← pow_two, ← pow_two, lattice_re, lattice_im_sq]
  ring

theorem re_pow_six (z : ℂ) :
    (z ^ 6).re = z.re ^ 6 - 15 * z.re ^ 4 * z.im ^ 2 +
      15 * z.re ^ 2 * (z.im ^ 2) ^ 2 - (z.im ^ 2) ^ 3 := by
  simp only [pow_succ, pow_zero, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im]
  ring

def finiteQuad (z : ℤ × ℤ) : ℚ := (z.1 : ℚ) ^ 2 - (z.1 : ℚ) * (z.2 : ℚ) + (z.2 : ℚ) ^ 2

def finiteRe (z : ℤ × ℤ) : ℚ :=
  let x : ℚ := -((z.1 : ℚ) + (z.2 : ℚ)) / 2
  let ySquared : ℚ := 3 * ((z.2 : ℚ) - (z.1 : ℚ)) ^ 2 / 4
  (x ^ 6 - 15 * x ^ 4 * ySquared + 15 * x ^ 2 * ySquared ^ 2 - ySquared ^ 3) / finiteQuad z ^ 6

def finiteNorm (z : ℤ × ℤ) : ℚ := (finiteQuad z ^ 6)⁻¹

theorem finiteRe_cast (z : ℤ × ℤ) : (finiteRe z : ℝ) = (((lattice z) ^ 6)⁻¹).re := by
  rw [Complex.inv_re, map_pow, normSq_lattice, re_pow_six, lattice_re, lattice_im_sq]
  unfold finiteRe finiteQuad
  push_cast
  rfl

theorem finiteNorm_cast (z : ℤ × ℤ) : (finiteNorm z : ℝ) = ‖((lattice z) ^ 12)⁻¹‖ := by
  rw [norm_inv, norm_pow, show (12 : ℕ) = 2 * 6 by decide, pow_mul,
    Complex.sq_norm, normSq_lattice]
  unfold finiteNorm finiteQuad
  push_cast
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem lattice_window_re :
    (5863 / 1000 : ℝ) ≤ (∑ z ∈ window, ((lattice z) ^ 6)⁻¹).re := by
  have hq : (5863 / 1000 : ℚ) ≤ ∑ z ∈ window, finiteRe z := by decide +kernel
  calc
    (5863 / 1000 : ℝ) = ((5863 / 1000 : ℚ) : ℝ) := by norm_num
    _ ≤ (↑(∑ z ∈ window, finiteRe z) : ℝ) := Rat.cast_le.mpr hq
    _ = _ := by rw [Complex.re_sum, Rat.cast_sum]; simp_rw [finiteRe_cast]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem lattice_window_norm :
    (∑ z ∈ window, ‖((lattice z) ^ 12)⁻¹‖) ≤ (601 / 100 : ℝ) := by
  have hq : (∑ z ∈ window, finiteNorm z) ≤ (601 / 100 : ℚ) := by decide +kernel
  calc
    (∑ z ∈ window, ‖((lattice z) ^ 12)⁻¹‖) = (↑(∑ z ∈ window, finiteNorm z) : ℝ) := by
      rw [Rat.cast_sum]; simp_rw [finiteNorm_cast]
    _ ≤ ((601 / 100 : ℚ) : ℝ) := Rat.cast_le.mpr hq
    _ = (601 / 100 : ℝ) := by norm_num

end MSE1250537Proof

open Finset Set MeasureTheory

namespace MSE1250537Proof

theorem sumRangeBox (f : ℤ × ℤ → ℂ) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), ∑ z ∈ Finset.box m, f z) =
      ∑ z ∈ Finset.Icc (-(N : ℤ × ℤ)) (N : ℤ × ℤ), f z := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, add_comm,
      ← Finset.sum_disjUnion (Finset.disjoint_box_succ_prod N),
      Finset.box_succ_disjUnion]

theorem boundedBoxLattice {f : ℤ × ℤ → ℂ} {C p : ℝ}
    (hC : 0 ≤ C) (hp : 2 < p) (hzero : f 0 = 0)
    (hbound : ∀ m : ℕ, 0 < m → ∀ z ∈ (Finset.box m : Finset (ℤ × ℤ)),
      ‖f z‖ ≤ C * (m : ℝ) ^ (-p)) :
    Summable f ∧
      ‖(∑' z, f z) - ∑ z ∈ (Finset.Icc (-5 : ℤ) 5).product (Finset.Icc (-5 : ℤ) 5), f z‖
        ≤ (8 * C) * (-(5 : ℝ) ^ (2 - p) / (2 - p)) := by
  let boxSet (m : ℕ) : Set (ℤ × ℤ) := ↑(Finset.box m : Finset (ℤ × ℤ))
  let major (m : ℕ) : ℝ := (8 * C) * (m : ℝ) ^ (1 - p)
  have hmajor : Summable major :=
    (Real.summable_nat_rpow.mpr (by linarith : 1 - p < -1)).mul_left (8 * C)
  have hshell (m : ℕ) : (∑ z ∈ (Finset.box m : Finset (ℤ × ℤ)), ‖f z‖) ≤ major m := by
    by_cases hm : m = 0
    · subst m
      simp [hzero, major]
      positivity
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    calc
      _ ≤ ∑ z ∈ (Finset.box m : Finset (ℤ × ℤ)), C * (m : ℝ) ^ (-p) :=
        Finset.sum_le_sum fun z hz ↦ hbound m (Nat.pos_of_ne_zero hm) z hz
      _ = major m := by
        rw [Finset.sum_const, nsmul_eq_mul, Int.card_box hm]
        simp only [major, Nat.cast_mul, Nat.cast_ofNat, sub_eq_add_neg,
          Real.rpow_add hmpos, Real.rpow_one]
        ring
  have hnorm : Summable (fun z ↦ ‖f z‖) := by
    rw [summable_partition (fun _ ↦ norm_nonneg _) (s := boxSet)
      Int.existsUnique_mem_box]
    refine ⟨fun m ↦ (hasSum_fintype (β := Finset.box (α := ℤ × ℤ) m) _).summable, ?_⟩
    apply hmajor.of_nonneg_of_le
    · intro m
      exact tsum_nonneg fun _ ↦ norm_nonneg _
    · intro m
      change (∑' z : (Finset.box m : Finset (ℤ × ℤ)), ‖f z‖) ≤ major m
      rw [tsum_fintype, Finset.univ_eq_attach,
        Finset.sum_attach _ (fun z : ℤ × ℤ ↦ ‖f z‖)]
      exact hshell m
  have hf : Summable f := hnorm.of_norm
  let boxSum (m : ℕ) : ℂ := ∑ z ∈ (Finset.box m : Finset (ℤ × ℤ)), f z
  let e := Set.sigmaEquiv boxSet Int.existsUnique_mem_box
  have hdecomp : HasSum boxSum (∑' z, f z) := by
    have hfull : HasSum (fun x : (Σ m, boxSet m) ↦ f (e x)) (∑' z, f z) :=
      e.hasSum_iff.mpr hf.hasSum
    have hsh := hfull.sigma (fun m ↦
      (hasSum_fintype (β := Finset.box (α := ℤ × ℤ) m) (fun z ↦ f z)))
    simpa only [boxSet, boxSum, Finset.univ_eq_attach, Finset.sum_attach] using hsh
  have hshift : (∑' z, f z) -
      (∑ z ∈ (Finset.Icc (-5 : ℤ) 5).product (Finset.Icc (-5 : ℤ) 5), f z) =
      ∑' m : ℕ, boxSum (m + 6) := by
    have hfive := sumRangeBox f 5
    change (∑ m ∈ Finset.range 6, boxSum m) = _ at hfive
    change (∑ m ∈ Finset.range 6, boxSum m) =
      ∑ z ∈ (Finset.Icc (-5 : ℤ) 5).product (Finset.Icc (-5 : ℤ) 5), f z at hfive
    rw [← hfive, ← hdecomp.tsum_eq, ← hdecomp.summable.sum_add_tsum_nat_add 6,
      add_sub_cancel_left]
  have hshell' (m : ℕ) : ‖boxSum m‖ ≤ major m :=
    (norm_sum_le _ _).trans (hshell m)
  have hmajShift : Summable fun m : ℕ ↦ major (m + 6) :=
    (summable_nat_add_iff 6).mpr hmajor
  have hnormShift : Summable fun m : ℕ ↦ ‖boxSum (m + 6)‖ :=
    hmajShift.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ hshell' (m + 6))
  have hint : (∑' m : ℕ, ((m + 6 : ℕ) : ℝ) ^ (1 - p))
      ≤ -(5 : ℝ) ^ (2 - p) / (2 - p) := by
    have hanti : AntitoneOn (fun x : ℝ ↦ x ^ (1 - p)) (Set.Ici 5) := by
      intro x hx y _ hxy
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le (by norm_num) hx) hxy (by linarith)
    have hle := hanti.tsum_comp_add_le_integral 5
      (integrableOn_Ioi_rpow_of_lt (by linarith : 1 - p < -1) (by norm_num))
      (fun x hx ↦ Real.rpow_nonneg (by
        change (5 : ℝ) < x at hx
        linarith) _)
    rw [integral_Ioi_rpow_of_lt (by linarith : 1 - p < -1) (by norm_num),
      show 1 - p + 1 = 2 - p by ring] at hle
    exact hle
  refine ⟨hf, ?_⟩
  rw [hshift]
  calc
    _ ≤ ∑' m : ℕ, ‖boxSum (m + 6)‖ := norm_tsum_le_tsum_norm hnormShift
    _ ≤ ∑' m : ℕ, major (m + 6) :=
      hnormShift.tsum_le_tsum (fun m ↦ hshell' (m + 6)) hmajShift
    _ = (8 * C) * ∑' m : ℕ, ((m + 6 : ℕ) : ℝ) ^ (1 - p) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hint (by positivity)

theorem latticeTermTail (k : ℕ) (hk : 1 < k)
    (hnorm : ∀ z : ℤ × ℤ, Complex.normSq (lattice z) =
      (z.1 : ℝ)^2 - (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ)^2) :
    Summable (latticeTerm (2 * k)) ∧
      ‖(∑' z, latticeTerm (2 * k) z) - ∑ z ∈ window, latticeTerm (2 * k) z‖
        ≤ (8 * (4 / 3 : ℝ)^k) * (-(5 : ℝ) ^ (2 - 2 * (k : ℝ)) / (2 - 2 * (k : ℝ))) := by
  have hk' : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  refine boundedBoxLattice (C := (4 / 3 : ℝ)^k) (p := 2 * (k : ℝ))
    (by positivity) (by linarith) ?_ ?_
  · change (lattice (0 : ℤ × ℤ) ^ (2 * k))⁻¹ = 0
    rw [show lattice (0 : ℤ × ℤ) = 0 by simp [lattice],
      zero_pow (by omega : 2 * k ≠ 0), inv_zero]
  · intro m hm z hz
    have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
    have hrank : max z.1.natAbs z.2.natAbs = m := Int.mem_box.mp hz
    have hsq : (3 / 4 : ℝ) * (m : ℝ)^2 ≤ ‖lattice z‖^2 := by
      rw [← Complex.normSq_eq_norm_sq, hnorm z, ← hrank, Nat.cast_max]
      rcases le_total z.1.natAbs z.2.natAbs with hle | hle
      · have hle' : (z.1.natAbs : ℝ) ≤ (z.2.natAbs : ℝ) := by exact_mod_cast hle
        rw [max_eq_right hle', Nat.cast_natAbs, Int.cast_abs, sq_abs]
        nlinarith [sq_nonneg ((z.1 : ℝ) - (z.2 : ℝ) / 2)]
      · have hle' : (z.2.natAbs : ℝ) ≤ (z.1.natAbs : ℝ) := by exact_mod_cast hle
        rw [max_eq_left hle', Nat.cast_natAbs, Int.cast_abs, sq_abs]
        nlinarith [sq_nonneg ((z.2 : ℝ) - (z.1 : ℝ) / 2)]
    have hmpos : 0 < (3 / 4 : ℝ) * (m : ℝ)^2 := by positivity
    calc
      ‖latticeTerm (2 * k) z‖ = ((‖lattice z‖^2)^k)⁻¹ := by
        simp [latticeTerm, pow_mul]
      _ ≤ (((3 / 4 : ℝ) * (m : ℝ)^2)^k)⁻¹ :=
        inv_anti₀ (pow_pos hmpos _) (pow_le_pow_left₀ hmpos.le hsq k)
      _ = (4 / 3 : ℝ)^k * (m : ℝ) ^ (-(2 * (k : ℝ))) := by
        rw [← show ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) by push_cast; rfl,
          Real.rpow_neg hm'.le, Real.rpow_natCast, pow_mul, mul_pow, mul_inv,
          ← inv_pow (3 / 4 : ℝ)]
        norm_num

theorem latticeTailSix
    (hnorm : ∀ z : ℤ × ℤ, Complex.normSq (lattice z) =
      (z.1 : ℝ)^2 - (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ)^2) :
    Summable (latticeTerm 6) ∧
      ‖(∑' z, latticeTerm 6 z) - ∑ z ∈ window, latticeTerm 6 z‖ ≤ (1 / 100 : ℝ) := by
  obtain ⟨hf, h⟩ := latticeTermTail 3 (by decide) hnorm
  refine ⟨hf, h.trans ?_⟩
  norm_num [show (2 - 2 * ((3 : ℕ) : ℝ)) = -((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5), Real.rpow_natCast]

theorem latticeTailTwelve
    (hnorm : ∀ z : ℤ × ℤ, Complex.normSq (lattice z) =
      (z.1 : ℝ)^2 - (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ)^2) :
    Summable (latticeTerm 12) ∧
      ‖(∑' z, latticeTerm 12 z) - ∑ z ∈ window, latticeTerm 12 z‖ ≤ (1 / 100000 : ℝ) := by
  obtain ⟨hf, h⟩ := latticeTermTail 6 (by decide) hnorm
  refine ⟨hf, h.trans ?_⟩
  norm_num [show (2 - 2 * ((6 : ℕ) : ℝ)) = -((10 : ℕ) : ℝ) by norm_num,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5), Real.rpow_natCast]

end MSE1250537Proof

namespace MSE1250537Proof

open OMA.S_mse_1250537 PowerSeries

private lemma denom_constant (a : ℂ) (tail : PowerSeries ℂ) :
    constantCoeff (1 - C a * X * tail) = 1 := by simp

private lemma auxiliary_constant (start depth : ℕ) :
    constantCoeff (cfConvergentAux start depth) = 1 := by
  cases depth with
  | zero => simp [cfConvergentAux]
  | succ n =>
      rw [cfConvergentAux, constantCoeff_inv, denom_constant, inv_one]

private lemma coeff_inverse_linear (a : ℂ) (tail : PowerSeries ℂ)
    (htail : constantCoeff tail = 1) :
    coeff 1 ((1 - C a * X * tail)⁻¹) = a := by
  let D := (1 - C a * X * tail : PowerSeries ℂ)
  have hc : constantCoeff D = 1 := denom_constant a tail
  have hci : constantCoeff D⁻¹ = 1 := by rw [constantCoeff_inv, hc, inv_one]
  have h1 : coeff 1 D = -a := by
    have hm : coeff 1 (X * tail) = coeff 0 tail := coeff_succ_X_mul 0 tail
    simp [D, mul_assoc, hm, coeff_zero_eq_constantCoeff_apply, htail]
  change coeff 1 D⁻¹ = a
  rw [coeff_inv, Finset.Nat.sum_antidiagonal_succ (n := 0)]
  simp [hc, hci, h1, coeff_zero_eq_constantCoeff_apply]

private lemma equiharmonic_initials (equiharmonic : ℕ → ℂ)
    (h : ∀ m : ℕ, coeff m (cfConvergent (m + 1)) =
      (7 / 36 : ℂ) * equiharmonic (m + 1)) :
    equiharmonic 1 = (36 / 7 : ℂ) ∧
      equiharmonic 2 = (36 / 7 : ℂ) * (10880 / 13 : ℂ) := by
  have h0 := h 0
  rw [coeff_zero_eq_constantCoeff_apply, cfConvergent, auxiliary_constant] at h0
  have h1 := h 1
  change coeff 1 ((1 - C (dCoeff 1) * X * cfConvergentAux 2 1)⁻¹) =
    (7 / 36 : ℂ) * equiharmonic 2 at h1
  rw [coeff_inverse_linear _ _ (auxiliary_constant 2 1)] at h1
  change (10880 / 13 : ℂ) = (7 / 36 : ℂ) * equiharmonic 2 at h1
  constructor
  · calc
      equiharmonic 1 = (36 / 7 : ℂ) * ((7 / 36 : ℂ) * equiharmonic 1) := by ring
      _ = 36 / 7 := by rw [← h0, mul_one]
  · calc
      equiharmonic 2 = (36 / 7 : ℂ) * ((7 / 36 : ℂ) * equiharmonic 2) := by ring
      _ = (36 / 7 : ℂ) * (10880 / 13 : ℂ) := by rw [← h1]

end MSE1250537Proof

namespace MSE1250537Proof

theorem ratioOfNormalization {w a b : ℂ}
    (h₁ : (720 : ℂ) / w ^ 6 * a = 36 / 7)
    (h₂ : (479001600 : ℂ) / w ^ 12 * b = (36 / 7) * (10880 / 13)) :
    (10880 / 13 : ℂ) * a ^ 2 = 4752 * b := by
  have hw : w ≠ 0 := by
    intro hw
    norm_num [hw] at h₁
  have ha : a = w ^ 6 / 140 := calc
    a = (w ^ 6 / 720) * ((720 : ℂ) / w ^ 6 * a) := by
      field_simp
    _ = w ^ 6 / 140 := by rw [h₁]; ring
  have hb : b = (10880 / 13 : ℂ) * w ^ 12 / 93139200 := calc
    b = (w ^ 12 / 479001600) * ((479001600 : ℂ) / w ^ 12 * b) := by
      field_simp
    _ = _ := by rw [h₂]; ring
  rw [ha, hb]
  ring

theorem ratioImpossible {a b : ℂ}
    (ha : (5853 / 1000 : ℝ) ≤ ‖a‖)
    (hb : ‖b‖ ≤ (6011 / 1000 : ℝ))
    (heq : (10880 / 13 : ℂ) * a ^ 2 = 4752 * b) : False := by
  have hnorm : (10880 / 13 : ℝ) * ‖a‖ ^ 2 = 4752 * ‖b‖ := by
    simpa only [Complex.norm_mul, Complex.norm_pow, Complex.norm_div,
      Complex.norm_ofNat] using congrArg (fun z : ℂ => ‖z‖) heq
  have hsquare : (5853 / 1000 : ℝ) ^ 2 ≤ ‖a‖ ^ 2 :=
    pow_le_pow_left₀ (by norm_num) ha _
  linarith

theorem tsumWithoutOrigin {k : ℕ} (hk : 0 < k) :
    (∑' z : {q : ℤ × ℤ // q ≠ (0, 0)}, latticeTerm k z.1) = ∑' z, latticeTerm k z := by
  apply tsum_subtype_eq_of_support_subset (f := latticeTerm k)
    (s := {q : ℤ × ℤ | q ≠ (0, 0)})
  intro z hz hz0
  change z = (0, 0) at hz0
  subst z
  exact hz (by simp [latticeTerm, lattice, zero_pow (Nat.ne_of_gt hk)])

theorem latticeValuesBounds
    (h₆finite : (5863 / 1000 : ℝ) ≤ (∑ z ∈ window, latticeTerm 6 z).re)
    (h₁₂finite : (∑ z ∈ window, ‖latticeTerm 12 z‖) ≤ (601 / 100 : ℝ))
    (h₆tail : ‖(∑' z, latticeTerm 6 z) - ∑ z ∈ window, latticeTerm 6 z‖ ≤ 1 / 100)
    (h₁₂tail : ‖(∑' z, latticeTerm 12 z) - ∑ z ∈ window, latticeTerm 12 z‖ ≤ 1 / 100000) :
    (5853 / 1000 : ℝ) ≤ ‖∑' z, latticeTerm 6 z‖ ∧
      ‖∑' z, latticeTerm 12 z‖ ≤ (6011 / 1000 : ℝ) := by
  constructor
  · have hre := Complex.re_le_norm ((∑ z ∈ window, latticeTerm 6 z) - (∑' z, latticeTerm 6 z))
    rw [Complex.sub_re, norm_sub_rev] at hre
    linarith [Complex.re_le_norm (∑' z, latticeTerm 6 z)]
  · have htri := norm_add_le ((∑' z, latticeTerm 12 z) - ∑ z ∈ window, latticeTerm 12 z)
      (∑ z ∈ window, latticeTerm 12 z)
    rw [sub_add_cancel] at htri
    have hsum := norm_sum_le window (fun z => latticeTerm 12 z)
    linarith

open OMA.S_mse_1250537 in
theorem equiharmonicAsLattice {ν : ℕ} (hν : 0 < ν) :
    equiharmonic ν = ((Nat.factorial (6 * ν) : ℂ) / omegaVal ^ (6 * ν)) *
      ∑' z, latticeTerm (6 * ν) z := by
  rw [← tsumWithoutOrigin (Nat.mul_pos (by decide) hν)]
  simp only [equiharmonic, latticeTerm, lattice, one_div]

end MSE1250537Proof

set_option maxHeartbeats 1000000 in
open MSE1250537Proof OMA.S_mse_1250537 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_1250537.main) := by
  intro h
  obtain ⟨h6, h12⟩ := equiharmonic_initials equiharmonic h
  rw [equiharmonicAsLattice (by decide : 0 < 1),
    show (6 * 1 : ℕ).factorial = 720 by decide, show (6 * 1 : ℕ) = 6 by decide] at h6
  rw [equiharmonicAsLattice (by decide : 0 < 2),
    show (6 * 2 : ℕ).factorial = 479001600 by decide, show (6 * 2 : ℕ) = 12 by decide] at h12
  obtain ⟨hb6, hb12⟩ := latticeValuesBounds lattice_window_re lattice_window_norm
    (latticeTailSix normSq_lattice).2 (latticeTailTwelve normSq_lattice).2
  exact ratioImpossible hb6 hb12 (ratioOfNormalization h6 h12)
