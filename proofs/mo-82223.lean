import OMAStatements.S_mo_82223
import Mathlib.Tactic

namespace MO82223Proof

open OMA.S_mo_82223

private noncomputable def w : Fin 3 → Fin 3 → ℝ
  | 0, 0 => 3 / 12
  | 0, 1 => 1 / 12
  | 0, 2 => 0
  | 1, 0 => 1 / 12
  | 1, 1 => 2 / 12
  | 1, 2 => 1 / 12
  | 2, 0 => 0
  | 2, 1 => 1 / 12
  | 2, 2 => 3 / 12

private def f0 : Fin 3 → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => -1

private lemma w_nonneg (i j : Fin 3) : 0 ≤ w i j := by
  fin_cases i <;> fin_cases j <;> norm_num [w]

private lemma w_prob : probabilityTable w := by
  refine ⟨w_nonneg, ?_⟩
  simp only [Fin.sum_univ_three, w]
  norm_num

private lemma corr_f0 : (3 / 4 : ℝ) ∈ allCorrelations w := by
  refine ⟨f0, f0, ?_, ?_, ?_⟩
  · simp only [varLeft, meanLeft, Fin.sum_univ_three, w, f0]
    norm_num
  · simp only [varRight, meanRight, Fin.sum_univ_three, w, f0]
    norm_num
  · simp only [correlation, covariance, varLeft, varRight, meanLeft, meanRight,
      Fin.sum_univ_three, w, f0]
    norm_num

private lemma corr_le_one (f g : Fin 3 → ℝ) (hf : 0 < varLeft w f) (hg : 0 < varRight w g) :
    correlation w f g ≤ 1 := by
  set s := Real.sqrt (varLeft w f)
  set t := Real.sqrt (varRight w g)
  have hs : 0 < s := Real.sqrt_pos.mpr hf
  have ht : 0 < t := Real.sqrt_pos.mpr hg
  have hs2 : s ^ 2 = varLeft w f := Real.sq_sqrt hf.le
  have ht2 : t ^ 2 = varRight w g := Real.sq_sqrt hg.le
  have hst : Real.sqrt (varLeft w f * varRight w g) = s * t :=
    Real.sqrt_mul hf.le (varRight w g)
  have hnn : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      w i j * (t * (f i - meanLeft w f) - s * (g j - meanRight w g)) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (w_nonneg i j) (sq_nonneg _)
  have hexp : (∑ i : Fin 3, ∑ j : Fin 3,
      w i j * (t * (f i - meanLeft w f) - s * (g j - meanRight w g)) ^ 2) =
      t ^ 2 * varLeft w f + s ^ 2 * varRight w g - 2 * s * t * covariance w f g := by
    simp only [varLeft, varRight, covariance, meanLeft, meanRight, Fin.sum_univ_three, w]
    ring
  have hcov : covariance w f g ≤ s * t := by
    have h1 : 0 ≤ 2 * (s * t) * (s * t - covariance w f g) := by
      nlinarith [hnn, hexp, hs2, ht2]
    nlinarith [mul_pos hs ht]
  rw [correlation, hst, div_le_one (mul_pos hs ht)]
  exact hcov

private lemma bddAbove_all : BddAbove (allCorrelations w) := by
  refine ⟨1, ?_⟩
  rintro r ⟨f, g, hf, hg, rfl⟩
  exact corr_le_one f g hf hg

private def b2z (b : Bool) : ℤ := if b then 1 else 0

private def varZ (x0 x1 x2 : ℤ) : ℤ :=
  3 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) - (x0 + x1 + x2) ^ 2

private def covZ (x0 x1 x2 y0 y1 y2 : ℤ) : ℤ :=
  3 * (3 * x0 * y0 + x0 * y1 + x1 * y0 + 2 * x1 * y1 + x1 * y2 + x2 * y1 + 3 * x2 * y2) -
    4 * (x0 + x1 + x2) * (y0 + y1 + y2)

private lemma int_bound : ∀ a0 a1 a2 b0 b1 b2 : Bool,
    4 * (covZ (b2z a0) (b2z a1) (b2z a2) (b2z b0) (b2z b1) (b2z b2)) ^ 2 ≤
      25 * varZ (b2z a0) (b2z a1) (b2z a2) * varZ (b2z b0) (b2z b1) (b2z b2) := by
  decide

private lemma b2z_cast (b : Bool) : (b2z b : ℝ) = if b then 1 else 0 := by
  cases b <;> simp [b2z]

private lemma ind_corr_le (a b : Fin 3 → Bool)
    (ha : 0 < varLeft w (indicator a)) (hb : 0 < varRight w (indicator b)) :
    correlation w (indicator a) (indicator b) ≤ 5 / 8 := by
  have hint : ((4 * (covZ (b2z (a 0)) (b2z (a 1)) (b2z (a 2))
      (b2z (b 0)) (b2z (b 1)) (b2z (b 2))) ^ 2 : ℤ) : ℝ) ≤
      ((25 * varZ (b2z (a 0)) (b2z (a 1)) (b2z (a 2)) *
        varZ (b2z (b 0)) (b2z (b 1)) (b2z (b 2)) : ℤ) : ℝ) := by
    exact_mod_cast int_bound (a 0) (a 1) (a 2) (b 0) (b 1) (b 2)
  have hvl : varLeft w (indicator a) =
      (varZ (b2z (a 0)) (b2z (a 1)) (b2z (a 2)) : ℝ) / 9 := by
    simp only [varLeft, meanLeft, indicator, Fin.sum_univ_three, w, varZ]
    push_cast
    simp only [b2z_cast]
    ring
  have hvr : varRight w (indicator b) =
      (varZ (b2z (b 0)) (b2z (b 1)) (b2z (b 2)) : ℝ) / 9 := by
    simp only [varRight, meanRight, indicator, Fin.sum_univ_three, w, varZ]
    push_cast
    simp only [b2z_cast]
    ring
  have hcv : covariance w (indicator a) (indicator b) =
      (covZ (b2z (a 0)) (b2z (a 1)) (b2z (a 2)) (b2z (b 0)) (b2z (b 1)) (b2z (b 2)) : ℝ) / 36 := by
    simp only [covariance, meanLeft, meanRight, indicator, Fin.sum_univ_three, w, covZ]
    push_cast
    simp only [b2z_cast]
    ring
  have hsq : 64 * (covariance w (indicator a) (indicator b)) ^ 2 ≤
      25 * (varLeft w (indicator a) * varRight w (indicator b)) := by
    rw [hvl, hvr, hcv]
    push_cast at hint
    linarith
  have hpos : 0 < Real.sqrt (varLeft w (indicator a) * varRight w (indicator b)) :=
    Real.sqrt_pos.mpr (mul_pos ha hb)
  have hsq_rt : (Real.sqrt (varLeft w (indicator a) * varRight w (indicator b))) ^ 2 =
      varLeft w (indicator a) * varRight w (indicator b) :=
    Real.sq_sqrt (mul_pos ha hb).le
  have hcov_le : covariance w (indicator a) (indicator b) ≤
      (5 / 8) * Real.sqrt (varLeft w (indicator a) * varRight w (indicator b)) := by
    nlinarith [hsq, hsq_rt, hpos]
  rw [correlation, div_le_iff₀ hpos]
  exact hcov_le

private lemma sSup_ind_le : sSup (indicatorCorrelations w) ≤ 5 / 8 := by
  refine Real.sSup_le ?_ (by norm_num)
  rintro r ⟨a, b, ha, hb, rfl⟩
  exact ind_corr_le a b ha hb

end MO82223Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_82223.main) := by
  intro h
  have heq := h 3 3 MO82223Proof.w MO82223Proof.w_prob
  have hlo : (3 / 4 : ℝ) ≤ sSup (OMA.S_mo_82223.allCorrelations MO82223Proof.w) :=
    le_csSup MO82223Proof.bddAbove_all MO82223Proof.corr_f0
  have hhi : sSup (OMA.S_mo_82223.indicatorCorrelations MO82223Proof.w) ≤ 5 / 8 :=
    MO82223Proof.sSup_ind_le
  linarith
