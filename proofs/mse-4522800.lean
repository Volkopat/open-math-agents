import OMAStatements.S_mse_4522800

/-!
# Uniform ball and closure formulations of the open mapping theorem

Source: https://math.stackexchange.com/questions/4522800/another-generalization-of-open-mapping-theorem
Retains @etaubman’s complete earlier proof linked from statement #20474.
Main proof #26403 is by @FrancoisCharroin. Standard geometric bounds and
norm convergence replace the corresponding local arguments.

The approximate-preimage argument below adapts the second half of Mathlib's
ContinuousLinearMap.exists_preimage_norm_le proof (Apache-2.0,
copyright 2019 Sebastien Gouezel).
-/

namespace Mse4522800Earlier

open OMA.S_mse_4522800

open Function Metric Set Filter Finset Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

lemma surjective_of_approx (T : E →L[𝕜] F) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ y : F, ∃ x : E,
      dist (T x) y ≤ (1 / 2 : ℝ) * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) :
    Surjective T := by
  choose g hg using hC
  let h y := y - T (g y)
  have hle : ∀ y, ‖h y‖ ≤ (1 / 2 : ℝ) * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  intro y
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2 : ℝ) ^ n * ‖y‖ := by
    intro n
    exact le_geom (u := fun k => ‖h^[k] y‖) (by norm_num) n
      (fun k _ => by simpa only [iterate_succ_apply'] using hle (h^[k] y))
  let u n := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2 : ℝ) ^ n * (C * ‖y‖) := fun n ↦ by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2 : ℝ) ^ n * ‖y‖) := by
        gcongr
        exact hnle n
      _ = (1 / 2 : ℝ) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have su : Summable u := sNu.of_norm
  have fsumeq : ∀ n : ℕ, T (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [T.map_zero]
    | succ n IH =>
      rw [sum_range_succ, T.map_add, IH, iterate_succ_apply', sub_add]
  have L₁ := (T.hasSum su.hasSum).tendsto_sum_nat
  simp only [← map_sum, fsumeq] at L₁
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub (squeeze_zero_norm hnle ?_)
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul
      tendsto_const_nhds <;> norm_num
  exact ⟨∑' n, u n, by simpa using tendsto_nhds_unique L₁ L₂⟩

lemma ballImage_of_surjective (T : E →L[𝕜] F) (hT : Surjective T) :
    uniformBallImage T := by
  obtain ⟨C, hC, hbound⟩ := T.exists_preimage_norm_le hT
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro x ε hε y hy
  obtain ⟨w, hw, hnorm⟩ := hbound (y - T x)
  refine ⟨x + w, ?_, ?_⟩
  · have hy' : ‖y - T x‖ < C⁻¹ * ε := by
      simpa only [mem_ball, dist_eq_norm] using hy
    calc
      dist (x + w) x = ‖w‖ := by simp
      _ ≤ C * ‖y - T x‖ := hnorm
      _ < C * (C⁻¹ * ε) := mul_lt_mul_of_pos_left hy' hC
      _ = ε := by simp [← mul_assoc, ne_of_gt hC]
  · rw [T.map_add, hw, add_sub_cancel]

lemma ballClosure_of_ballImage (T : E →L[𝕜] F) (hT : uniformBallImage T) :
    uniformBallClosure T := by
  rcases hT with ⟨r, hr, h⟩
  exact ⟨r, hr, fun x ε hε => (h x ε hε).trans subset_closure⟩

lemma surjective_of_ballClosure (T : E →L[𝕜] F) (hT : uniformBallClosure T) :
    Surjective T := by
  rcases hT with ⟨r, hr, h⟩
  apply surjective_of_approx T (2 / r) (by positivity)
  intro y
  by_cases hy : y = 0
  · subst y
    exact ⟨0, by simp, by simp⟩
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have heps : 0 < 2 * ‖y‖ / r := by positivity
  have hyball : y ∈ ball (T 0) (r * (2 * ‖y‖ / r)) := by
    simp only [T.map_zero, mem_ball_zero_iff]
    have heq : r * (2 * ‖y‖ / r) = 2 * ‖y‖ := by field_simp [ne_of_gt hr]
    rw [heq]
    linarith
  have hyclosure := h 0 (2 * ‖y‖ / r) heps hyball
  obtain ⟨z, hz, hzy⟩ :=
    Metric.mem_closure_iff.mp hyclosure (‖y‖ / 2) (by positivity)
  rcases hz with ⟨x, hx, rfl⟩
  refine ⟨x, ?_, ?_⟩
  · rw [dist_comm]
    linarith
  · have hx' : ‖x‖ < 2 * ‖y‖ / r := by
      simpa only [mem_ball_zero_iff] using hx
    calc
      ‖x‖ ≤ 2 * ‖y‖ / r := hx'.le
      _ = (2 / r) * ‖y‖ := by ring

theorem main (T : E →L[𝕜] F) :
    (Surjective T ↔ uniformBallImage T) ∧
    (Surjective T ↔ uniformBallClosure T) := by
  have h₁ := ballImage_of_surjective T
  have h₂ := ballClosure_of_ballImage T
  have h₃ := surjective_of_ballClosure T
  exact ⟨⟨h₁, fun h => h₃ (h₂ h)⟩, ⟨fun h => h₂ (h₁ h), h₃⟩⟩

end Mse4522800Earlier

theorem OMA.solution : type_of% @OMA.S_mse_4522800.main :=
  Mse4522800Earlier.main
