import OMAStatements.S_mo_82223
import Mathlib

/-!
Retains @ChimdinduDenalexOrakwue's probability table and counterexample from
PR #32693, pinned at a366d9dabfd998e2cb83c5f1451cbf8d04f24779.
The direct six-Boolean indicator enumeration follows @etaubman's earlier
complete proof linked from statement #21228:
https://github.com/etaubman/open-math-agents/blob/1a81e58af39f5df53656c34c5907748c964c3184/batches/non-oeis-10-74b45435c52e/standalone/mo-82223.lean
That earlier proof uses a different table and gap; this revision keeps the main
proof's 3/4 versus 5/8 gap and uses the standard discriminant criterion for
the all-functions bound. Original question: Ralph Crasto,
https://mathoverflow.net/questions/82223 (CC BY-SA 3.0).
The earlier source credits Davide Giraudo's discussion of the inequality.
-/

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
  have hq (r : ℝ) : 0 ≤ varLeft w f * (r * r) + (-2 * covariance w f g) * r + varRight w g := by
    have h := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
        mul_nonneg (w_nonneg i j) (sq_nonneg (r * (f i - meanLeft w f) - (g j - meanRight w g)))
    simp only [varLeft, varRight, covariance, meanLeft, meanRight, Fin.sum_univ_three, w] at h ⊢
    nlinarith only [h]
  have hd := discrim_le_zero hq
  have hc : (covariance w f g) ^ 2 ≤ varLeft w f * varRight w g := by
    unfold discrim at hd
    nlinarith
  rw [correlation, div_le_one (Real.sqrt_pos.mpr (mul_pos hf hg))]
  exact Real.le_sqrt_of_sq_le hc

private lemma bddAbove_all : BddAbove (allCorrelations w) := by
  refine ⟨1, ?_⟩
  rintro r ⟨f, g, hf, hg, rfl⟩
  exact corr_le_one f g hf hg

set_option maxHeartbeats 1000000 in
private lemma ind_corr_le (a b : Fin 3 → Bool)
    (ha : 0 < varLeft w (indicator a)) (hb : 0 < varRight w (indicator b)) :
    correlation w (indicator a) (indicator b) ≤ 5 / 8 := by
  simp only [correlation, covariance, varLeft, varRight, meanLeft, meanRight,
    Fin.sum_univ_three, w] at ha hb ⊢
  cases ha0 : a 0 <;> cases ha1 : a 1 <;> cases ha2 : a 2 <;>
    cases hb0 : b 0 <;> cases hb1 : b 1 <;> cases hb2 : b 2 <;>
    simp only [indicator, ha0, ha1, ha2, hb0, hb1, hb2, Bool.false_eq_true,
      if_false, if_true] at ha hb ⊢ <;>
    norm_num [Real.sqrt_div] at *

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
