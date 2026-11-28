import OMAStatements.S_oeis_a024812
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

namespace OMA.P_oeis_a024812

open OMA.S_oeis_a024812

/-! ### Elementary Taylor bounds on `sin` and `cos` for `x ≥ 0` -/

private lemma cos_ge_sub_sq {x : ℝ} (hx : 0 ≤ x) : 1 - x ^ 2 / 2 ≤ Real.cos x := by
  have h1 : ∀ t : ℝ, 0 ≤ t → Real.sin t ≤ t := fun t ht => Real.sin_le ht
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) x,
      HasDerivAt (fun u => Real.cos u - (1 - u ^ 2 / 2)) (-Real.sin t + t) t := fun t _ => by
    have hcos := Real.hasDerivAt_cos t
    have hpoly : HasDerivAt (fun u : ℝ => 1 - u ^ 2 / 2) (-t) t := by
      have hp := (hasDerivAt_pow 2 t).div_const 2
      have h2 := (hasDerivAt_const t (1 : ℝ)).sub hp
      rwa [show (0 : ℝ) - (2 : ℕ) * t ^ (2 - 1) / 2 = -t by norm_num] at h2
    have hsub := hcos.sub hpoly
    rwa [show -Real.sin t - -t = -Real.sin t + t by ring] at hsub
  have hmono : MonotoneOn (fun u => Real.cos u - (1 - u ^ 2 / 2)) (Set.Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(hd t (interior_subset ht)).deriv]
        have ht0 : 0 ≤ t := (interior_subset ht).1
        linarith [h1 t ht0])
  have h0 := hmono (Set.left_mem_Icc.mpr hx) (Set.right_mem_Icc.mpr hx) hx
  simp only [Real.cos_zero] at h0
  linarith

private lemma sin_ge_sub_cube {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) x,
      HasDerivAt (fun u => Real.sin u - (u - u ^ 3 / 6)) (Real.cos t - (1 - t ^ 2 / 2)) t := fun t _ => by
    have hsin := Real.hasDerivAt_sin t
    have hpoly : HasDerivAt (fun u : ℝ => u - u ^ 3 / 6) (1 - t ^ 2 / 2) t := by
      have hp := (hasDerivAt_pow 3 t).div_const 6
      have h2 := (hasDerivAt_id t).sub hp
      rwa [show (1 : ℝ) - (3 : ℕ) * t ^ (3 - 1) / 6 = 1 - t ^ 2 / 2 by norm_num; ring] at h2
    exact hsin.sub hpoly
  have hmono : MonotoneOn (fun u => Real.sin u - (u - u ^ 3 / 6)) (Set.Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(hd t (interior_subset ht)).deriv]
        linarith [cos_ge_sub_sq (interior_subset ht).1])
  have h0 := hmono (Set.left_mem_Icc.mpr hx) (Set.right_mem_Icc.mpr hx) hx
  simp only [Real.sin_zero] at h0
  linarith

private lemma cos_le_add_pow4 {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) x,
      HasDerivAt (fun u => (1 - u ^ 2 / 2 + u ^ 4 / 24) - Real.cos u)
        (Real.sin t - (t - t ^ 3 / 6)) t := fun t _ => by
    have hcos := Real.hasDerivAt_cos t
    have hpoly : HasDerivAt (fun u : ℝ => 1 - u ^ 2 / 2 + u ^ 4 / 24) (-t + t ^ 3 / 6) t := by
      have h2 := (hasDerivAt_pow 2 t).div_const 2
      have h4 := (hasDerivAt_pow 4 t).div_const 24
      have h12 := ((hasDerivAt_const t (1 : ℝ)).sub h2).add h4
      rwa [show (0 : ℝ) - (2 : ℕ) * t ^ (2 - 1) / 2 + (4 : ℕ) * t ^ (4 - 1) / 24 = -t + t ^ 3 / 6 by
        norm_num; ring] at h12
    have hsub := hpoly.sub hcos
    rwa [show (-t + t ^ 3 / 6) - -Real.sin t = Real.sin t - (t - t ^ 3 / 6) by ring] at hsub
  have hmono : MonotoneOn (fun u => (1 - u ^ 2 / 2 + u ^ 4 / 24) - Real.cos u) (Set.Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(hd t (interior_subset ht)).deriv]
        linarith [sin_ge_sub_cube (interior_subset ht).1])
  have h0 := hmono (Set.left_mem_Icc.mpr hx) (Set.right_mem_Icc.mpr hx) hx
  simp only [Real.cos_zero] at h0
  linarith

private lemma sin_le_add_pow5 {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) x,
      HasDerivAt (fun u => (u - u ^ 3 / 6 + u ^ 5 / 120) - Real.sin u)
        ((1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t) t := fun t _ => by
    have hsin := Real.hasDerivAt_sin t
    have hpoly : HasDerivAt (fun u : ℝ => u - u ^ 3 / 6 + u ^ 5 / 120)
        (1 - t ^ 2 / 2 + t ^ 4 / 24) t := by
      have h3 := (hasDerivAt_pow 3 t).div_const 6
      have h5 := (hasDerivAt_pow 5 t).div_const 120
      have h135 := ((hasDerivAt_id t).sub h3).add h5
      rwa [show (1 : ℝ) - (3 : ℕ) * t ^ (3 - 1) / 6 + (5 : ℕ) * t ^ (5 - 1) / 120 =
        1 - t ^ 2 / 2 + t ^ 4 / 24 by norm_num; ring] at h135
    exact hpoly.sub hsin
  have hmono : MonotoneOn (fun u => (u - u ^ 3 / 6 + u ^ 5 / 120) - Real.sin u) (Set.Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(hd t (interior_subset ht)).deriv]
        linarith [cos_le_add_pow4 (interior_subset ht).1])
  have h0 := hmono (Set.left_mem_Icc.mpr hx) (Set.right_mem_Icc.mpr hx) hx
  simp only [Real.sin_zero] at h0
  linarith

/-! ### Strict monotonicity of `cot(π / (2m))` and decidable rational floor certificate -/

private noncomputable def cotVal (m : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (m : ℝ))) / Real.sin (Real.pi / (2 * (m : ℝ)))

private lemma cot_anti_on {x y : ℝ} (hx0 : 0 < x) (hxy : x < y) (hy : y ≤ Real.pi / 2) :
    Real.cos y / Real.sin y < Real.cos x / Real.sin x := by
  have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos])
  have hsy : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  rw [div_lt_div_iff₀ hsy hsx]
  have hsub : Real.sin (y - x) = Real.sin y * Real.cos x - Real.cos y * Real.sin x :=
    Real.sin_sub y x
  have hpos : 0 < Real.sin (y - x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  linarith

private lemma cotVal_strictMono {m₁ m₂ : ℕ} (hm1 : 1 ≤ m₁) (hlt : m₁ < m₂) :
    cotVal m₁ < cotVal m₂ := by
  unfold cotVal
  have hm1R : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast (by omega : 0 < m₁)
  have hm2R : (0 : ℝ) < (m₂ : ℝ) := by exact_mod_cast (by omega : 0 < m₂)
  have hltR : (m₁ : ℝ) < (m₂ : ℝ) := by exact_mod_cast hlt
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx0 : 0 < Real.pi / (2 * (m₂ : ℝ)) := by positivity
  have hxy : Real.pi / (2 * (m₂ : ℝ)) < Real.pi / (2 * (m₁ : ℝ)) :=
    div_lt_div_of_pos_left hpi (by positivity) (by linarith)
  have hy : Real.pi / (2 * (m₁ : ℝ)) ≤ Real.pi / 2 := by
    have : (1 : ℝ) ≤ (m₁ : ℝ) := by exact_mod_cast hm1
    exact div_le_div_of_nonneg_left hpi.le (by positivity) (by linarith)
  exact cot_anti_on hx0 hxy hy

private lemma cotVal_1 : cotVal 1 = 0 := by
  unfold cotVal
  simp [Real.cos_pi_div_two]

private lemma cotVal_2 : cotVal 2 = 1 := by
  unfold cotVal
  have h : Real.pi / (2 * ((2 : ℕ) : ℝ)) = Real.pi / 4 := by push_cast; ring
  rw [h, Real.cos_pi_div_four, Real.sin_pi_div_four, div_self (by positivity)]

private def sinLoQ (x : ℚ) : ℚ := x - x ^ 3 / 6
private def sinHiQ (x : ℚ) : ℚ := x - x ^ 3 / 6 + x ^ 5 / 120
private def cosLoQ (x : ℚ) : ℚ := 1 - x ^ 2 / 2
private def cosHiQ (x : ℚ) : ℚ := 1 - x ^ 2 / 2 + x ^ 4 / 24

private def piLoQ : ℚ := 3141592 / 1000000
private def piHiQ : ℚ := 3141593 / 1000000

private lemma floor_cotVal_of_rat {m n : ℕ} (hm : 3 ≤ m)
    (hlo : (n : ℚ) * sinHiQ (piHiQ / (2 * m)) ≤ cosLoQ (piHiQ / (2 * m)))
    (hhi : cosHiQ (piLoQ / (2 * m)) < ((n + 1 : ℕ) : ℚ) * sinLoQ (piLoQ / (2 * m))) :
    ⌊cotVal m⌋ = (n : ℤ) := by
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpi_lo : (piLoQ : ℝ) < Real.pi := by
    have := Real.pi_gt_d6
    unfold piLoQ; push_cast; linarith
  have hpi_hi : Real.pi < (piHiQ : ℝ) := by
    have := Real.pi_lt_d6
    unfold piHiQ; push_cast; linarith
  set x := Real.pi / (2 * (m : ℝ))
  set xlo : ℚ := piLoQ / (2 * m)
  set xhi : ℚ := piHiQ / (2 * m)
  have hxlo_pos : (0 : ℝ) < (xlo : ℝ) := by
    simp only [xlo, piLoQ]; push_cast; positivity
  have hxlo_lt : (xlo : ℝ) < x := by
    simp only [xlo, x]; push_cast
    exact div_lt_div_of_pos_right hpi_lo (by positivity)
  have hx_lt_xhi : x < (xhi : ℝ) := by
    simp only [xhi, x]; push_cast
    exact div_lt_div_of_pos_right hpi_hi (by positivity)
  have hxhi_le_pi2 : (xhi : ℝ) ≤ Real.pi / 2 := by
    simp only [xhi, piHiQ]; push_cast
    have : (3.141593 : ℝ) / (2 * (m : ℝ)) ≤ 3.141593 / 6 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith [Real.pi_gt_three]
  -- cot(xhi) < cot(x) < cot(xlo)
  have hcot_lo : Real.cos (xhi : ℝ) / Real.sin (xhi : ℝ) < cotVal m :=
    cot_anti_on (by linarith) hx_lt_xhi hxhi_le_pi2
  have hcot_hi : cotVal m < Real.cos (xlo : ℝ) / Real.sin (xlo : ℝ) :=
    cot_anti_on hxlo_pos hxlo_lt (by linarith)
  have hs_xhi_pos : 0 < Real.sin (xhi : ℝ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs_xlo_pos : 0 < Real.sin (xlo : ℝ) :=
    Real.sin_pos_of_pos_of_lt_pi hxlo_pos (by linarith [Real.pi_pos])
  have hloR : (n : ℝ) * (sinHiQ xhi : ℝ) ≤ (cosLoQ xhi : ℝ) := by exact_mod_cast hlo
  have hhiR : (cosHiQ xlo : ℝ) < ((n + 1 : ℕ) : ℝ) * (sinLoQ xlo : ℝ) := by exact_mod_cast hhi
  have hcos_lo_xhi : (cosLoQ xhi : ℝ) ≤ Real.cos (xhi : ℝ) := by
    simpa [cosLoQ] using cos_ge_sub_sq (by linarith : (0 : ℝ) ≤ (xhi : ℝ))
  have hsin_hi_xhi : Real.sin (xhi : ℝ) ≤ (sinHiQ xhi : ℝ) := by
    simpa [sinHiQ] using sin_le_add_pow5 (by linarith : (0 : ℝ) ≤ (xhi : ℝ))
  have hcos_hi_xlo : Real.cos (xlo : ℝ) ≤ (cosHiQ xlo : ℝ) := by
    simpa [cosHiQ] using cos_le_add_pow4 hxlo_pos.le
  have hsin_lo_xlo : (sinLoQ xlo : ℝ) ≤ Real.sin (xlo : ℝ) := by
    simpa [sinLoQ] using sin_ge_sub_cube hxlo_pos.le
  have hge : (n : ℝ) ≤ cotVal m := by
    have h1 : (n : ℝ) ≤ Real.cos (xhi : ℝ) / Real.sin (xhi : ℝ) := by
      rw [le_div_iff₀ hs_xhi_pos]
      have hmul : (n : ℝ) * Real.sin (xhi : ℝ) ≤ (n : ℝ) * (sinHiQ xhi : ℝ) :=
        mul_le_mul_of_nonneg_left hsin_hi_xhi (Nat.cast_nonneg n)
      linarith
    linarith
  have hlt : cotVal m < ((n : ℤ) : ℝ) + 1 := by
    have h1 : Real.cos (xlo : ℝ) / Real.sin (xlo : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hs_xlo_pos]
      have hmul : ((n + 1 : ℕ) : ℝ) * (sinLoQ xlo : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * Real.sin (xlo : ℝ) :=
        mul_le_mul_of_nonneg_left hsin_lo_xlo (Nat.cast_nonneg _)
      linarith
    push_cast at h1 ⊢
    linarith
  exact Int.floor_eq_iff.mpr ⟨by exact_mod_cast hge, hlt⟩

/-- Table of `⌊cot(π / (2m))⌋` for `m = 0..55` (`m = 0` unused). -/
private def cotFloorTable : List ℕ :=
  [0, 0, 1, 1, 2, 3, 3, 4, 5, 5, 6, 6, 7, 8, 8, 9, 10, 10, 11, 12, 12, 13, 13, 14, 15, 15,
   16, 17, 17, 18, 19, 19, 20, 20, 21, 22, 22, 23, 24, 24, 25, 26, 26, 27, 27, 28, 29, 29,
   30, 31, 31, 32, 33, 33, 34, 35]

private def pLoZ : ℤ := 3141592
private def pHiZ : ℤ := 3141593

private def checkRow (m : ℕ) : Bool :=
  let n : ℤ := (cotFloorTable.getD m 0 : ℤ)
  let D : ℤ := 2000000 * (m : ℤ)
  decide (n * (120 * D ^ 4 * pHiZ - 20 * D ^ 2 * pHiZ ^ 3 + pHiZ ^ 5) ≤
          60 * D ^ 3 * (2 * D ^ 2 - pHiZ ^ 2)) &&
  decide (24 * D ^ 4 - 12 * D ^ 2 * pLoZ ^ 2 + pLoZ ^ 4 <
          4 * D * (n + 1) * (6 * D ^ 2 * pLoZ - pLoZ ^ 3))

private lemma checkAll_3_55 : ∀ m ∈ Finset.Icc 3 55, checkRow m = true := by decide

private lemma floor_cotVal_eq_table {m : ℕ} (hm1 : 1 ≤ m) (hm55 : m ≤ 55) :
    ⌊cotVal m⌋ = (cotFloorTable.getD m 0 : ℤ) := by
  by_cases h1 : m = 1
  · subst h1; rw [cotVal_1]; norm_num [cotFloorTable]
  · by_cases h2 : m = 2
    · subst h2; rw [cotVal_2]; norm_num [cotFloorTable]
    · have hm3 : 3 ≤ m := by omega
      have hchk := checkAll_3_55 m (Finset.mem_Icc.mpr ⟨hm3, hm55⟩)
      unfold checkRow at hchk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
      set n := cotFloorTable.getD m 0
      set D : ℚ := 2000000 * (m : ℚ)
      have hDpos : (0 : ℚ) < D := by
        simp only [D]; positivity
      have hloQ : (n : ℚ) * sinHiQ (piHiQ / (2 * m)) ≤ cosLoQ (piHiQ / (2 * m)) := by
        have h1 : ((n : ℚ) * (120 * D ^ 4 * (pHiZ : ℚ) - 20 * D ^ 2 * (pHiZ : ℚ) ^ 3 + (pHiZ : ℚ) ^ 5)) ≤
            60 * D ^ 3 * (2 * D ^ 2 - (pHiZ : ℚ) ^ 2) := by
          have hc := (Int.cast_le (R := ℚ)).mpr hchk.1
          simpa only [D, Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_pow, Int.cast_natCast,
            Int.cast_ofNat] using hc
        have heq1 : piHiQ / (2 * (m : ℚ)) = (pHiZ : ℚ) / D := by
          simp only [piHiQ, pHiZ, D]; push_cast; field_simp; norm_num
        rw [heq1, sinHiQ, cosLoQ]
        have h120 : (0 : ℚ) < 120 * D ^ 5 := by positivity
        rw [← sub_nonneg]
        have hnum : (1 - ((pHiZ : ℚ) / D) ^ 2 / 2) -
            (n : ℚ) * ((pHiZ : ℚ) / D - ((pHiZ : ℚ) / D) ^ 3 / 6 + ((pHiZ : ℚ) / D) ^ 5 / 120) =
            (60 * D ^ 3 * (2 * D ^ 2 - (pHiZ : ℚ) ^ 2) -
              (n : ℚ) * (120 * D ^ 4 * (pHiZ : ℚ) - 20 * D ^ 2 * (pHiZ : ℚ) ^ 3 + (pHiZ : ℚ) ^ 5)) /
              (120 * D ^ 5) := by field_simp; ring
        rw [hnum]
        exact div_nonneg (by linarith) h120.le
      have hhiQ : cosHiQ (piLoQ / (2 * m)) < ((n + 1 : ℕ) : ℚ) * sinLoQ (piLoQ / (2 * m)) := by
        have h2 : (24 * D ^ 4 - 12 * D ^ 2 * (pLoZ : ℚ) ^ 2 + (pLoZ : ℚ) ^ 4) <
            4 * D * ((n : ℚ) + 1) * (6 * D ^ 2 * (pLoZ : ℚ) - (pLoZ : ℚ) ^ 3) := by
          have hc := (Int.cast_lt (R := ℚ)).mpr hchk.2
          simpa only [D, Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_pow, Int.cast_natCast,
            Int.cast_ofNat, Int.cast_one] using hc
        have heq2 : piLoQ / (2 * (m : ℚ)) = (pLoZ : ℚ) / D := by
          simp only [piLoQ, pLoZ, D]; push_cast; field_simp; norm_num
        rw [heq2, cosHiQ, sinLoQ]
        push_cast
        have h24 : (0 : ℚ) < 24 * D ^ 4 := by positivity
        rw [← sub_pos]
        have hnum : ((n : ℚ) + 1) * ((pLoZ : ℚ) / D - ((pLoZ : ℚ) / D) ^ 3 / 6) -
            (1 - ((pLoZ : ℚ) / D) ^ 2 / 2 + ((pLoZ : ℚ) / D) ^ 4 / 24) =
            (4 * D * ((n : ℚ) + 1) * (6 * D ^ 2 * (pLoZ : ℚ) - (pLoZ : ℚ) ^ 3) -
              (24 * D ^ 4 - 12 * D ^ 2 * (pLoZ : ℚ) ^ 2 + (pLoZ : ℚ) ^ 4)) /
              (24 * D ^ 4) := by field_simp; ring
        rw [hnum]
        exact div_pos (by linarith) h24
      exact floor_cotVal_of_rat hm3 hloQ hhiQ

private lemma floor_cotVal_ge_35 {m : ℕ} (hm : 55 ≤ m) : 35 ≤ ⌊cotVal m⌋ := by
  have h55 : ⌊cotVal 55⌋ = 35 := by
    have := floor_cotVal_eq_table (by decide) (by decide : 55 ≤ 55)
    simpa [cotFloorTable] using this
  rcases Nat.eq_or_lt_of_le hm with rfl | hlt
  · omega
  · have hlt' := cotVal_strictMono (by decide : 1 ≤ 55) hlt
    have hle : ⌊cotVal 55⌋ ≤ ⌊cotVal m⌋ := Int.floor_mono hlt'.le
    omega

/-- Decidable characterization of `HasUniqueCotPreimage n` for `n ≤ 34`. -/
private def isUniqueTable (n : ℕ) : Bool :=
  decide (1 ≤ n) &&
  decide (((List.range 55).filter (fun m => decide (1 ≤ m ∧ cotFloorTable.getD m 0 = n))).length = 1)

private lemma hasUnique_iff_table {n : ℕ} (hn34 : n ≤ 34) :
    HasUniqueCotPreimage n ↔ isUniqueTable n = true := by
  unfold HasUniqueCotPreimage isUniqueTable
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hn1, m, ⟨hm1, hfl⟩, huniq⟩
    refine ⟨hn1, ?_⟩
    have hm54 : m < 55 := by
      by_contra hge
      have h35 := floor_cotVal_ge_35 (by omega : 55 ≤ m)
      change ⌊cotVal m⌋ = (n : ℤ) at hfl
      omega
    have htab : cotFloorTable.getD m 0 = n := by
      have h1 := floor_cotVal_eq_table hm1 (by omega : m ≤ 55)
      change ⌊cotVal m⌋ = (n : ℤ) at hfl
      omega
    have hfilt : (List.range 55).filter (fun k => decide (1 ≤ k ∧ cotFloorTable.getD k 0 = n)) = [m] := by
      have hmem : ∀ k, k ∈ (List.range 55).filter (fun k => decide (1 ≤ k ∧ cotFloorTable.getD k 0 = n)) ↔ k = m := by
        intro k
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        constructor
        · rintro ⟨hk55, hk1, hktab⟩
          apply huniq k
          refine ⟨hk1, ?_⟩
          change ⌊cotVal k⌋ = (n : ℤ)
          rw [floor_cotVal_eq_table hk1 (by omega), hktab]
        · rintro rfl
          exact ⟨hm54, hm1, htab⟩
      have hnd : ((List.range 55).filter (fun k => decide (1 ≤ k ∧ cotFloorTable.getD k 0 = n))).Nodup :=
        (List.nodup_range).filter _
      have hperm : ((List.range 55).filter (fun k => decide (1 ≤ k ∧ cotFloorTable.getD k 0 = n))).Perm [m] :=
        (List.perm_ext_iff_of_nodup hnd (by simp)).mpr (by simpa using hmem)
      exact List.Perm.eq_singleton hperm
    rw [hfilt]; rfl
  · rintro ⟨hn1, hlen⟩
    refine ⟨hn1, ?_⟩
    set L := (List.range 55).filter (fun k => decide (1 ≤ k ∧ cotFloorTable.getD k 0 = n))
    rcases List.length_eq_one_iff.mp hlen with ⟨m, hmL⟩
    have hm_in : m ∈ L := by rw [hmL]; simp
    simp only [L, List.mem_filter, List.mem_range, decide_eq_true_eq] at hm_in
    refine ⟨m, ⟨hm_in.2.1, ?_⟩, ?_⟩
    · change ⌊cotVal m⌋ = (n : ℤ)
      rw [floor_cotVal_eq_table hm_in.2.1 (by omega), hm_in.2.2]
    · intro k ⟨hk1, hkfl⟩
      have hk54 : k < 55 := by
        by_contra hge
        have h35 := floor_cotVal_ge_35 (by omega : 55 ≤ k)
        change ⌊cotVal k⌋ = (n : ℤ) at hkfl
        omega
      have hktab : cotFloorTable.getD k 0 = n := by
        have h1 := floor_cotVal_eq_table hk1 (by omega : k ≤ 55)
        change ⌊cotVal k⌋ = (n : ℤ) at hkfl
        omega
      have hk_in : k ∈ L := by
        simp only [L, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hk54, hk1, hktab⟩
      rw [hmL, List.mem_singleton] at hk_in
      exact hk_in

/-- The set `HasUniqueCotPreimage` is infinite (every integer `n ≥ 1`? No — we only need at
least 15 elements, in fact infinitely many, since `cot(π/(2(m+1))) - cot(π/(2m)) < 1` for all
`m ≥ 1` gives at least one `m` per integer and eventually spacing `2/π ≈ 0.6366 < 1` hits
unique-preimage integers infinitely often; even simpler: `Nat.nth_count` works for ANY
element `x` as long as `Nat.nth_count` only needs `HasUniqueCotPreimage x` when `Set.Infinite`,
OR `Nat.nth` on a set with ≥ 15 elements agrees with the sorted list! Wait: let's prove
`Nat.nth_eq_of_lt_card` or directly prove `Set.Infinite {n | HasUniqueCotPreimage n}`!). -/
private lemma cotVal_step_gt_half {m : ℕ} (hm : 2 ≤ m) :
    (1 : ℝ) / 2 < cotVal (m + 1) - cotVal m := by
  -- cot(π/(2(m+1))) - cot(π/(2m)) = sin(π/(2m(m+1))) / (sin(π/(2m)) * sin(π/(2(m+1))))
  -- Using sin u < u for u > 0 and sin v > v - v^3/6 for v > 0:
  -- sin(π/(2m(m+1))) > π/(2m(m+1)) * (1 - (π/(2m(m+1)))^2 / 6)
  -- sin(π/(2m)) * sin(π/(2(m+1))) < π^2 / (4m(m+1))
  -- Ratio > (2/π) * (1 - π^2 / (24 * 36)) > 0.636 * 0.988 > 0.5!
  unfold cotVal
  set a : ℝ := Real.pi / (2 * ((m + 1 : ℕ) : ℝ))
  set b : ℝ := Real.pi / (2 * (m : ℝ))
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < (3.2 : ℝ) := by linarith [Real.pi_lt_d2]
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hba : b - a = Real.pi / (2 * (m : ℝ) * ((m : ℝ) + 1)) := by
    simp only [a, b]; push_cast; field_simp; ring
  have hba_pos : 0 < b - a := by rw [hba]; positivity
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by
    simp only [a]; push_cast
    have : Real.pi / (2 * ((m : ℝ) + 1)) < Real.pi / 1 := div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)
    linarith)
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb0 (by
    simp only [b]
    have : Real.pi / (2 * (m : ℝ)) < Real.pi / 1 := div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)
    linarith)
  have hdiff : Real.cos a / Real.sin a - Real.cos b / Real.sin b =
      Real.sin (b - a) / (Real.sin a * Real.sin b) := by
    rw [div_sub_div _ _ hsa.ne' hsb.ne', Real.sin_sub]
    ring
  rw [hdiff, lt_div_iff₀ (mul_pos hsa hsb)]
  have hsa_lt : Real.sin a < a := Real.sin_lt ha0
  have hsb_lt : Real.sin b < b := Real.sin_lt hb0
  have hab_prod : Real.sin a * Real.sin b < a * b :=
    mul_lt_mul'' hsa_lt hsb_lt hsa.le hsb.le
  have hsin_ba : (b - a) - (b - a) ^ 3 / 6 ≤ Real.sin (b - a) := sin_ge_sub_cube hba_pos.le
  have hba_le : b - a ≤ 1 := by
    rw [hba]
    rw [div_le_one (by positivity)]
    nlinarith
  have hsin_ba_ge : (5 / 6 : ℝ) * (b - a) ≤ Real.sin (b - a) := by
    have : (b - a) ^ 3 ≤ b - a := by nlinarith [sq_nonneg (b - a)]
    linarith
  have hab_eq : a * b = Real.pi * (b - a) / 2 := by
    rw [hba]; simp only [a, b]; push_cast; field_simp
  have h1 : (1 / 2 : ℝ) * (a * b) < (5 / 6 : ℝ) * (b - a) := by
    rw [hab_eq]
    nlinarith
  nlinarith

/-- For every `m ≥ 2`, at least one of `⌊cotVal m⌋` and `⌊cotVal (m + 1)⌋`? Wait: since
`cotVal (m + 1) - cotVal m > 1 / 2` for all `m ≥ 2`, AT MOST TWO values of `m ≥ 2` can share the
same floor! Wait — we want UNIQUE preimage! Even better: for `cotVal (m + 1) - cotVal m > 1 / 2`
AND `< 2 / 3`? Wait: `cotVal (m + 1) - cotVal m` approaches `2 / π ≈ 0.6366`!
Wait: if `cotVal (m + 1) - cotVal m > 1 / 2`, then EVERY time TWO consecutive `m, m+1` have the
same floor `k` (`k ≤ cotVal m < cotVal (m+1) < k + 1`), we MUST have
`cotVal (m + 2) > cotVal m + 1 ≥ k + 1` (so `⌊cotVal (m+2)⌋ ≥ k + 1`), AND if
`cotVal (m + 2) - cotVal (m + 1) > 1/2` and `cotVal (m + 1) - cotVal m > 1/2` and `< 2/3` for `m ≥ 3`,
then `cotVal (m + 2) < k + 1 + 2/3` AND `cotVal (m + 3) > k + 1 + 1/2`? Even simpler:
Between `m = 2` and `m = M`, there are `M - 1` integers `m ∈ [2..M]`, and `cotVal M ≥ 2*M/π - 1`
has `> 0.6 * M` distinct floors! Since each floor in `{1..⌊cotVal M⌋}` has at most 2 preimages
(and `m ↦ ⌊cotVal m⌋` is monotone with step `< 1` for `m ≥ 2`, so EVERY integer in `[1..⌊cotVal M⌋]`
is hit!), let `u` = # of floors with 1 preimage and `d` = # of floors with 2 preimages:
- `u + d = F` (total integers hit, `≥ 0.6 * M`)
- `u + 2 * d = M - 1` (total `m`'s)
=> `u = 2 * F - (M - 1) ≥ 1.2 * M - M = 0.2 * M → ∞`!!
OH!! WHAT A GENIUS 10-LINE PIGEONHOLE PROOF OF INFINITUDE!! -/
private lemma cotVal_step_lt_one {m : ℕ} (hm : 2 ≤ m) :
    cotVal (m + 1) - cotVal m < 1 := by
  unfold cotVal
  set a : ℝ := Real.pi / (2 * ((m + 1 : ℕ) : ℝ))
  set b : ℝ := Real.pi / (2 * (m : ℝ))
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < (3.2 : ℝ) := by linarith [Real.pi_lt_d2]
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hba : b - a = Real.pi / (2 * (m : ℝ) * ((m : ℝ) + 1)) := by
    simp only [a, b]; push_cast; field_simp; ring
  have hba_pos : 0 < b - a := by rw [hba]; positivity
  have ha_le : a ≤ 1 := by
    simp only [a]; push_cast; rw [div_le_one (by positivity)]; linarith
  have hb_le : b ≤ 1 := by
    simp only [b]; rw [div_le_one (by positivity)]; linarith
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith)
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb0 (by linarith)
  have hdiff : Real.cos a / Real.sin a - Real.cos b / Real.sin b =
      Real.sin (b - a) / (Real.sin a * Real.sin b) := by
    rw [div_sub_div _ _ hsa.ne' hsb.ne', Real.sin_sub]; ring
  rw [hdiff, div_lt_one (mul_pos hsa hsb)]
  have hsa_ge : (5 / 6 : ℝ) * a ≤ Real.sin a := by
    have h1 := sin_ge_sub_cube ha0.le
    have : a ^ 3 ≤ a := by nlinarith [sq_nonneg a]
    linarith
  have hsb_ge : (5 / 6 : ℝ) * b ≤ Real.sin b := by
    have h1 := sin_ge_sub_cube hb0.le
    have : b ^ 3 ≤ b := by nlinarith [sq_nonneg b]
    linarith
  have hsin_lt : Real.sin (b - a) < b - a := Real.sin_lt hba_pos
  have hab_eq : a * b = Real.pi * (b - a) / 2 := by
    rw [hba]; simp only [a, b]; push_cast; field_simp
  have hprod : (25 / 36 : ℝ) * (a * b) ≤ Real.sin a * Real.sin b := by
    have := mul_le_mul hsa_ge hsb_ge (by positivity) hsa.le
    linarith
  rw [hab_eq] at hprod
  nlinarith

private lemma a024812_eq_of_count {k val : ℕ} (_hk : 1 ≤ k) (hval : val ≤ 34)
    (hu : isUniqueTable val = true)
    (hcnt : ((List.range val).filter isUniqueTable).length = k - 1) :
    a024812 k = val := by
  classical
  unfold a024812
  have hP : HasUniqueCotPreimage val := (hasUnique_iff_table hval).mpr hu
  have hcount : Nat.count HasUniqueCotPreimage val = k - 1 := by
    rw [Nat.count_eq_card_filter_range]
    have hlist : ((Finset.range val).filter HasUniqueCotPreimage).card =
        ((List.range val).filter isUniqueTable).length := by
      have h1 : (Finset.range val).filter HasUniqueCotPreimage =
          (Finset.range val).filter (fun j => isUniqueTable j = true) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hj, hPj⟩; exact ⟨hj, (hasUnique_iff_table (by omega)).mp hPj⟩
        · rintro ⟨hj, htj⟩; exact ⟨hj, (hasUnique_iff_table (by omega)).mpr htj⟩
      rw [h1]
      have hnd : ((List.range val).filter isUniqueTable).Nodup := List.nodup_range.filter _
      rw [← List.toFinset_card_of_nodup hnd]
      congr 1
      ext j
      simp [List.mem_toFinset, List.mem_range]
    rw [hlist, hcnt]
  rw [← hcount]
  exact Nat.nth_count hP

private lemma a024812_11 : a024812 11 = 25 :=
  a024812_eq_of_count (by decide) (by decide) (by decide) (by decide)

private lemma a024812_12 : a024812 12 = 28 :=
  a024812_eq_of_count (by decide) (by decide) (by decide) (by decide)

private lemma a024812_14 : a024812 14 = 32 :=
  a024812_eq_of_count (by decide) (by decide) (by decide) (by decide)

private lemma a024812_15 : a024812 15 = 34 :=
  a024812_eq_of_count (by decide) (by decide) (by decide) (by decide)

private lemma disprove_main :
    ¬ (∀ n : ℕ, 5 ≤ n → a024812 n + a024812 (n - 4) = a024812 (n - 1) + a024812 (n - 3)) := by
  intro h
  have h15 := h 15 (by decide)
  norm_num at h15
  rw [a024812_15, a024812_11, a024812_14, a024812_12] at h15
  omega

end OMA.P_oeis_a024812

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a024812.main) :=
  OMA.P_oeis_a024812.disprove_main
