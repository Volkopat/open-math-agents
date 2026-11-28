import OMAReductions.R_wp_regularity_of_solutions_of_vlasov_maxwell_equations_R1_H2_R1
import Mathlib

open MeasureTheory
open scoped BigOperators

theorem OMA.solution : OMA.R_wp_regularity_of_solutions_of_vlasov_maxwell_equations_R1_H2_R1.H2 := by
  intro ι _ e b g hc hInt hzero
  let I (i : ι) : ℝ := ∫ v, g i v ^ 2
  have hI (i : ι) : 0 ≤ I i := integral_nonneg fun v => sq_nonneg (g i v)
  have hs : 0 ≤ ∑ i, I i := Finset.sum_nonneg fun i _ => hI i
  change ‖e‖ ^ 2 + ‖b‖ ^ 2 + (∑ i, I i) = 0 at hzero
  have he : ‖e‖ ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg ‖b‖]) (sq_nonneg _)
  have hb : ‖b‖ ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg ‖e‖]) (sq_nonneg _)
  have hsum : (∑ i, I i) = 0 := by linarith
  refine ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp he), norm_eq_zero.mp (sq_eq_zero_iff.mp hb), ?_⟩
  intro i v
  have hle : I i ≤ ∑ j, I j :=
    Finset.single_le_sum (fun j _ => hI j) (Finset.mem_univ i)
  have hIi : I i = 0 := le_antisymm (hsum ▸ hle) (hI i)
  have hae := (integral_eq_zero_iff_of_nonneg (fun v => sq_nonneg (g i v)) (hInt i)).mp hIi
  have heq : (fun v => g i v ^ 2) = (fun _ => (0 : ℝ)) :=
    (((hc i).pow 2).ae_eq_iff_eq volume continuous_const).mp hae
  exact sq_eq_zero_iff.mp (congrFun heq v)