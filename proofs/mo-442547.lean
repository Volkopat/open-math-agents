import OMAStatements.S_mo_442547

open MeasureTheory
open scoped ENNReal

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_442547.main) := by
  intro h
  let Q : Measure (Fin 2) := ENNReal.ofReal (1 / 2) • Measure.count
  let : IsProbabilityMeasure Q := by
    refine ⟨?_⟩
    change (ENNReal.ofReal (1 / 2)) * Measure.count (Set.univ : Set (Fin 2)) = 1
    rw [Measure.count_univ]
    have hcard : (ENat.card (Fin 2) : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
    rw [hcard, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have havg (v : Fin 2 → ℝ) : (∫ x, v x ∂Q) = (v 0 + v 1) / 2 := by
    simp [Q, Fin.sum_univ_two]
    ring
  let f : Fin 2 → ℝ := fun _ => 0
  let g : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
  let F : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
  have henvelope (x : Fin 2) : |f x| ≤ F x := by
    by_cases hx : x = 0 <;> simp [f, F, hx]
  have hstrict : (∫ x, |f x - g x| ∂Q) < 2 * (∫ x, F x ∂Q) := by
    rw [havg, havg]
    norm_num [f, g, F]
  have hbound := h (Fin 2) Q 2 f g F (by norm_num)
    (measurable_of_finite f) (measurable_of_finite g) (measurable_of_finite F)
    henvelope Integrable.of_finite hstrict
  rw [havg, havg] at hbound
  norm_num [f, g, F, Real.rpow_two] at hbound