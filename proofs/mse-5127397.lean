import OMAStatements.S_mse_5127397
import Mathlib

/-!
The 2-adic product counterexample is from @carl2sheriff's proof (#9187).
Summability is transported by the continuous linear equivalence. The direct product-norm
calculation follows the pattern used by @sturdy4days in the alternate proof (#8126).
-/

open Filter Topology

abbrev OMA_E := WithLp 1 (ℚ_[2] × ℚ_[2])

theorem OMA_hyp : ∀ u : ℕ → OMA_E,
    OMA.S_mse_5127397.SeriesConverges u ↔ Tendsto u atTop (nhds 0) := by
  intro u
  constructor
  · rintro ⟨s, hs⟩
    have h1 := hs.comp (tendsto_add_atTop_nat 1)
    have h2 := h1.sub hs
    simp only [Function.comp_def, Finset.sum_range_succ, add_sub_cancel_left, sub_self] at h2
    exact h2
  · intro hu
    let e := WithLp.prodContinuousLinearEquiv 1 ℚ_[2] ℚ_[2] ℚ_[2]
    have hv : Tendsto (fun n => e (u n)) atTop (nhds 0) := by
      have := e.continuous.tendsto 0
      rw [map_zero] at this
      exact this.comp hu
    have hs : Summable (fun n => e (u n)) :=
      NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by simpa [Nat.cofinite_eq_atTop] using hv)
    exact ⟨∑' n, u n, (e.summable.mp hs).hasSum.tendsto_sum_nat⟩

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_5127397.main) := by
  intro h
  have htriangle := (h ℚ_[2] OMA_E OMA_hyp).2
    (WithLp.toLp 1 ((1 : ℚ_[2]), 0)) (WithLp.toLp 1 ((0 : ℚ_[2]), 1))
  rw [WithLp.prod_norm_eq_of_L1, WithLp.norm_toLp_fst, WithLp.norm_toLp_snd] at htriangle
  norm_num [WithLp.add_fst, WithLp.add_snd] at htriangle
