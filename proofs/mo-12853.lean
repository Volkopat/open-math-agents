import OMAStatements.S_mo_12853
import Mathlib

/-!
MathOverflow 12853: prescribe `α` and `β` uniform on `[1, 2]` and `α / β` uniform on `[3, 4]`.
Any joint law with these marginals puts `(α, β)` in `[1, 2]²` almost surely, where
`α / β ≤ 2 < 3`, so the ratio cannot have the prescribed law.
-/

-- Retains @koolkao’s incompatible uniform-density counterexample (#27603).
-- Indicator densities are handled by the restriction and integral library APIs.

namespace OMA.P12853

open MeasureTheory OMA.S_mo_12853
open scoped ENNReal

/-- The uniform density on `[a, a + 1]`. -/
noncomputable def u (a : ℝ) : ℝ → ℝ≥0∞ := (Set.Icc a (a + 1)).indicator 1

lemma u_meas (a : ℝ) : Measurable (u a) :=
  measurable_one.indicator measurableSet_Icc

lemma u_set (a : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    volume.withDensity (u a) s = volume (s ∩ Set.Icc a (a + 1)) := by
  simp [u, withDensity_indicator_one measurableSet_Icc, hs]

lemma u_density (a : ℝ) : IsDensity (u a) := by
  refine ⟨u_meas a, ?_⟩
  simp [u, lintegral_indicator measurableSet_Icc]

theorem disproof_aux :
    ¬ ∀ fα fβ fr : ℝ → ℝ≥0∞, IsDensity fα → IsDensity fβ → IsDensity fr →
      ∃ μ : Measure (ℝ × ℝ), IsProbabilityMeasure μ ∧
        μ.map Prod.fst = volume.withDensity fα ∧
        μ.map Prod.snd = volume.withDensity fβ ∧
        μ.map (fun p => p.1 / p.2) = volume.withDensity fr := by
  intro h
  obtain ⟨μ, -, h1, h2, h3⟩ := h (u 1) (u 1) (u 3) (u_density 1) (u_density 1) (u_density 3)
  have hdiv : Measurable (fun p : ℝ × ℝ => p.1 / p.2) := measurable_fst.div measurable_snd
  set I : Set ℝ := Set.Icc 1 (1 + 1)
  have hIc : MeasurableSet Iᶜ := measurableSet_Icc.compl
  have z1 : μ (Prod.fst ⁻¹' Iᶜ) = 0 := by
    rw [← Measure.map_apply measurable_fst hIc, h1, u_set 1 _ hIc]; simp [I]
  have z2 : μ (Prod.snd ⁻¹' Iᶜ) = 0 := by
    rw [← Measure.map_apply measurable_snd hIc, h2, u_set 1 _ hIc]; simp [I]
  have one : μ ((fun p : ℝ × ℝ => p.1 / p.2) ⁻¹' Set.Icc 3 (3 + 1)) = 1 := by
    rw [← Measure.map_apply hdiv measurableSet_Icc, h3, u_set 3 _ measurableSet_Icc]
    simp
  have sub : (fun p : ℝ × ℝ => p.1 / p.2) ⁻¹' Set.Icc 3 (3 + 1) ⊆
      Prod.fst ⁻¹' Iᶜ ∪ Prod.snd ⁻¹' Iᶜ := by
    intro p hp
    by_contra hc
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, not_or, not_not] at hc
    obtain ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩ := hc
    have hp3 : 3 ≤ p.1 / p.2 := hp.1
    have hb0 : (0 : ℝ) < p.2 := by linarith
    rw [le_div_iff₀ hb0] at hp3
    linarith
  have := measure_mono_null sub (measure_union_null z1 z2)
  rw [one] at this
  exact one_ne_zero this

end OMA.P12853

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_12853.main) := OMA.P12853.disproof_aux
