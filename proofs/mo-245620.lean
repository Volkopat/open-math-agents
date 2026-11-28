import OMAStatements.S_mo_245620
import Mathlib

-- Problem: mo-245620, the literal strict form of an empirical Hoeffding-type bound:
-- P( E X > mean - (max - a) sqrt(log(1/delta) / (2n)) ) >= 1 - delta.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- False as literally stated: for the constant variable X = a = 0 (one sample) the event is
-- 0 > 0 - 0, which never happens, so its probability is 0 < 1 - delta for delta = 1/2.

open MeasureTheory ProbabilityTheory

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_245620.main) := by
  intro h
  have hsub : Subsingleton (Fin (0 + 1)) := (inferInstance : Subsingleton (Fin 1))
  have key := h Unit (Measure.dirac ()) 0 (fun _ _ => (0 : ℝ)) 0 0 (1 / 2)
    (fun _ => measurable_const) iIndepFun.of_subsingleton
    (fun _ => IdentDistrib.refl measurable_const.aemeasurable)
    (fun _ => Filter.Eventually.of_forall (fun _ => ⟨le_rfl, le_rfl⟩))
    (by norm_num) le_rfl
  norm_num [OMA.S_mo_245620.sampleMax] at key
