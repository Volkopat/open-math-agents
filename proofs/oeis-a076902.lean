import OMAStatements.S_oeis_a076902
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open OMA.S_oeis_a076902 Filter Topology

namespace HalvingError

noncomputable def error (n : ℕ) : ℝ := (a n:ℝ)-(n:ℝ)/3

lemma even_error (m : ℕ) (hm : 0<m) : error (2*m) = -error m := by
  have ha : a (2*m) = (m:ℤ) - a m := by
    rw [a, if_neg (by omega), show 2*m/2 = m by omega]
  unfold error
  rw [ha]
  push_cast
  ring

lemma odd_error (m : ℕ) (hm : 0<m) : error (2*m+1) = -error m - 1/3 := by
  have ha : a (2*m+1) = (m:ℤ) - a m := by
    rw [a, if_neg (by omega), show (2*m+1)/2 = m by omega]
  unfold error
  rw [ha]
  push_cast
  ring

lemma log_bound (n : ℕ) (hn : 0 < n) : |error n| < Real.log ((n:ℝ)+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n=1
    · subst n
      have ha : a 1 = 1 := by rw [a]; decide
      norm_num [error, ha]
      linarith [Real.log_two_gt_d9]
    · obtain ⟨m, rfl | rfl⟩ : ∃ m, n=2*m ∨ n=2*m+1 := ⟨n/2, by omega⟩
      · have hm : 0 < m := by omega
        rw [even_error m hm, abs_neg]
        apply (ih m (by omega) hm).trans
        apply Real.log_lt_log (by positivity)
        exact_mod_cast (show m+1 < 2*m+1 by omega)
      · have hm : 0<m := by omega
        have h := ih m (by omega) hm
        rw [odd_error m hm]
        push_cast
        rw [show 2*(m:ℝ)+1+1 = 2*((m:ℝ)+1) by ring,
          Real.log_mul (by norm_num) (by positivity)]
        calc
          |-error m - 1/3| ≤ |-error m| + |(1:ℝ)/3| := abs_sub _ _
          _ < Real.log 2 + Real.log ((m:ℝ)+1) := by
            rw [abs_neg, abs_of_pos (by norm_num : (0:ℝ)<1/3)]
            linarith [Real.log_two_gt_d9]

lemma log_ratio : Tendsto (fun n : ℕ => Real.log ((n:ℝ)+1)/(n:ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => Real.log ((n:ℝ)+1)/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  have q := h.div (tendsto_natCast_div_add_atTop (1:ℝ)) one_ne_zero
  rw [zero_div] at q
  apply q.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  change (Real.log ((n:ℝ)+1)/((n:ℝ)+1)) / ((n:ℝ)/((n:ℝ)+1)) = Real.log ((n:ℝ)+1)/(n:ℝ)
  field_simp

lemma error_ratio : Tendsto (fun n : ℕ => error n/(n:ℝ)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using log_ratio.neg) log_ratio
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (abs_lt.mp (log_bound n hn)).1.le (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_le_div_of_nonneg_right (abs_lt.mp (log_bound n hn)).2.le (by positivity)

end HalvingError

open HalvingError

theorem OMA.solution : type_of% @OMA.S_oeis_a076902.main := by
  refine ⟨log_bound, ?_⟩
  have h := (tendsto_const_nhds (x := (1:ℝ))).add (error_ratio.const_mul 3)
  rw [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  dsimp [error]
  field_simp
  ring
