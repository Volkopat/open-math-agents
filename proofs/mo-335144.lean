import OMAStatements.S_mo_335144
import Mathlib

-- Problem: mo-335144, is E[prod (V_i - p)] <= C(n) E[prod V_i] for Bernoulli(p) variables
-- V_1, ..., V_n with p < 1/2 and arbitrary dependence?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No, for n = 3. On three equally likely outcomes let V_i be the indicator of outcome i, so
-- p = 1/3. The product of the V_i is identically 0, while the centered product is
-- (2/3) (1/3)^2 = 2/27 at every outcome.

open MeasureTheory

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_335144.main) := by
  intro h
  obtain ⟨C, hC, hmain⟩ := h 3 (by norm_num)
  have hset : ∀ i : Fin 3, {ω : Fin 3 | (if ω = i then (1 : ℝ) else 0) = 1} = {i} := by
    intro i
    ext ω
    simp
  have hmass : ∀ i : Fin 3, (PMF.uniformOfFintype (Fin 3)).toMeasure
      {ω : Fin 3 | (if ω = i then (1 : ℝ) else 0) = 1} = ENNReal.ofReal (1 / 3) := by
    intro i
    rw [hset i, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i),
      PMF.uniformOfFintype_apply, show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    simp
  have key := hmain (Fin 3) (PMF.uniformOfFintype (Fin 3)).toMeasure
    (fun i ω => if ω = i then 1 else 0) (1 / 3)
    (fun i => measurable_of_finite _)
    (fun i => Filter.Eventually.of_forall (fun ω => by by_cases hω : ω = i <;> simp [hω]))
    hmass (by norm_num) (by norm_num)
  simp [PMF.integral_eq_sum, Fin.sum_univ_three, Fin.prod_univ_three] at key
  norm_num at key
