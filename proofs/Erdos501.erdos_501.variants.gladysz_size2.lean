import FormalConjectures.ErdosProblems.«501»

/-! Shorter proof of `Erdos501.erdos_501.variants.gladysz_size2` via Tonelli's theorem. -/

open Set MeasureTheory
open scoped ENNReal

theorem OMA.solution : type_of% @Erdos501.erdos_501.variants.gladysz_size2 := by
  classical
  intro A hcl hvol
  suffices ∃ x y : ℝ, x ≠ y ∧ x ∉ A y ∧ y ∉ A x by
    obtain ⟨x, y, hne, hxy, hyx⟩ := this
    refine ⟨{x, y}, (ncard_pair hne).ge, fun a ha b hb hab => ?_⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      first | exact (hab rfl).elim | assumption
  by_contra hbad
  let D x : Set ℝ := insert x (A x)
  have hDc x : IsClosed (D x) := by
    change IsClosed (insert x (A x)); rw [← singleton_union]; exact isClosed_singleton.union (hcl x)
  have hor {x y} (hy : y ∉ D x) : x ∈ D y := by
    by_contra hx
    exact hbad ⟨x, y, fun h => hy (Or.inl h.symm), fun h => hx (Or.inr h), fun h => hy (Or.inr h)⟩
  let I (i : ℚ × ℚ) : Set ℝ := Ioo i.1 i.2
  let L (i : ℚ × ℚ) : Set ℝ := closure {x | I i ⊆ (D x)ᶜ}
  let B : Set (ℝ × ℝ) := ⋃ i : ℚ × ℚ, L i ×ˢ I i
  have hB : MeasurableSet B :=
    .iUnion fun _ => isClosed_closure.measurableSet.prod measurableSet_Ioo
  have hH y : (fun x => (x, y)) ⁻¹' B ⊆ D y := fun x hx => by
    obtain ⟨i, hx', hy'⟩ := mem_iUnion.mp hx
    exact closure_minimal (s := {z | I i ⊆ (D z)ᶜ}) (fun z hz => hor (hz hy')) (hDc y) hx'
  have hV x : (D x)ᶜ ⊆ Prod.mk x ⁻¹' B := fun y hy => by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hDc x).isOpen_compl y hy
    obtain ⟨a, hay, ha⟩ := exists_rat_btwn (show y - ε < y by linarith)
    obtain ⟨b, hb, hby⟩ := exists_rat_btwn (show y < y + ε by linarith)
    exact mem_iUnion.mpr ⟨(a, b), subset_closure fun z hz => hball <| by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hz.1, hz.2], ha, hb⟩
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 3)
  have hμ : μ univ = 3 := by norm_num [μ, Measure.restrict_apply, Real.volume_Icc]
  have hDs x : μ (D x) ≤ 1 := (Measure.restrict_le_self (D x)).trans <|
    (show volume (D x) ≤ volume (A x) by
      change volume (insert x (A x)) ≤ _; rw [← singleton_union]
      exact (measure_union_le _ _).trans_eq (by simp)).trans (hvol x).le
  have hDl x : (2 : ℝ≥0∞) ≤ μ (D x)ᶜ := by
    have hs := measure_add_measure_compl (μ := μ) (hDc x).measurableSet
    have hsum : (3 : ℝ≥0∞) ≤ μ (D x)ᶜ + 1 := by
      rw [← hμ, ← hs, add_comm (μ (D x)ᶜ)]; exact add_le_add (hDs x) le_rfl
    exact (show (2 : ℝ≥0∞) = 3 - 1 by
      rw [show (3 : ℝ≥0∞) = 2 + 1 by norm_num]
      exact (ENNReal.add_sub_cancel_right ENNReal.one_ne_top).symm) ▸ tsub_le_iff_right.mpr hsum
  have hlo : (6 : ℝ≥0∞) ≤ μ.prod μ B := by
    rw [Measure.prod_apply hB]
    exact (show (6 : ℝ≥0∞) = ∫⁻ _, 2 ∂μ by norm_num [lintegral_const, hμ]) ▸
      lintegral_mono fun x => (hDl x).trans (measure_mono (hV x))
  have hhi : μ.prod μ B ≤ 3 := by
    rw [Measure.prod_apply_symm hB]
    exact (lintegral_mono fun y => (measure_mono (hH y)).trans (hDs y)).trans_eq
      (by simp [lintegral_const, hμ])
  have := hlo.trans hhi; norm_num at this
