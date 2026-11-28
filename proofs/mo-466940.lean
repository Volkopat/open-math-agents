import OMAStatements.S_mo_466940
import Mathlib

open MeasureTheory OMA.S_mo_466940

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_466940.main) := by
  intro h
  let μ : Measure PUnit := Measure.dirac PUnit.unit
  let F : Filtration ℕ (inferInstance : MeasurableSpace PUnit) := ⊤
  let Z : ℕ → PUnit → ℝ := fun _ _ => -1
  have hprob : IsProbabilityMeasure μ := inferInstance
  have hadapted : Adapted F Z := fun i => measurable_const
  have hbound : ∀ t ∈ Finset.Icc 1 32, ∀ᵐ ω ∂μ, |Z t ω| ≤ (1 : ℝ) := by
    intro t ht
    simp [Z]
  have hineq := h.1 PUnit (inferInstance : MeasurableSpace PUnit) μ hprob F Z 32 1 (1 / 2)
    hadapted (by norm_num) (by norm_num) (by norm_num) hbound
  have hlog : Real.log 4 < 4 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hempty : firstEvent μ F Z 32 1 (1 / 2) = ∅ := by
    apply (Set.eq_empty_iff_forall_notMem).mpr
    intro ω
    simp only [firstEvent, Set.mem_setOf_eq]
    have hZ : (∑ t ∈ Finset.Icc 1 32, Z t ω) = -32 := by simp [Z]
    have hC : (∑ t ∈ Finset.Icc 1 32, μ[Z t | F (t - 1)] ω) = -32 := by
      have h1 : ∀ t, μ[Z t | F (t - 1)] ω = -1 := by
        intro t
        have hconst : μ[fun _ : PUnit => (-1 : ℝ) | F (t - 1)] = fun _ => -1 :=
          condExp_const (F.le (t - 1)) (-1)
        simpa [Z] using congrFun hconst ω
      simp [h1]
    rw [hZ, hC]
    intro hle
    norm_num at hle
    nlinarith [hlog]
  rw [hempty, measureReal_empty] at hineq
  norm_num at hineq
