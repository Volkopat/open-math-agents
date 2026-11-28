import OMAStatements.S_mse_4522800

-- Problem: Another generalization of open mapping theorem
-- Upstream: statements/mse-4522800.lean (declaration OMA.S_mse_4522800.main)
-- Credit: @FrancoisCharroin
-- Equivalence of surjectivity, uniformBallImage, and uniformBallClosure for bounded linear maps between Banach spaces.

namespace OMA.Mse4522800

open Function Metric Set Filter Finset Topology
open OMA.S_mse_4522800

section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma surjective_to_uniformBallImage [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) (hsurj : Surjective T) :
    uniformBallImage T := by
  obtain ⟨C, Cpos, hC⟩ := T.exists_preimage_norm_le hsurj
  refine ⟨C⁻¹, inv_pos.mpr Cpos, fun x ε hε z hz => ?_⟩
  rw [mem_ball, dist_eq_norm] at hz
  obtain ⟨w, hw, hwnorm⟩ := hC (z - T x)
  refine ⟨x + w, ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    calc
      ‖w‖ ≤ C * ‖z - T x‖ := hwnorm
      _ < C * (C⁻¹ * ε) := by gcongr
      _ = ε := by field_simp [Cpos.ne']
  · rw [T.map_add, hw, add_sub_cancel]

lemma uniformBallImage_to_uniformBallClosure (T : E →L[𝕜] F) (h : uniformBallImage T) :
    uniformBallClosure T := by
  obtain ⟨r, rpos, hr⟩ := h
  exact ⟨r, rpos, fun x ε hε => (hr x ε hε).trans subset_closure⟩

lemma approx_preimage_of_uniformBallClosure (T : E →L[𝕜] F) (h : uniformBallClosure T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : F, ∃ w : E, ‖y - T w‖ ≤ 1 / 2 * ‖y‖ ∧ ‖w‖ ≤ C * ‖y‖ := by
  obtain ⟨r, rpos, hr⟩ := h
  refine ⟨2 / r, by positivity, fun y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp, by simp⟩
  · have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
    let ε : ℝ := (2 / r) * ‖y‖
    have hε : 0 < ε := by positivity
    have hyball : y ∈ ball (T 0) (r * ε) := by
      rw [mem_ball, T.map_zero, dist_zero_right]
      have hre : r * ε = 2 * ‖y‖ := by
        dsimp only [ε]
        field_simp [rpos.ne']
      rw [hre]
      linarith
    have hycl : y ∈ closure (T '' ball 0 ε) := hr 0 ε hε hyball
    obtain ⟨z, hz_im, hdist⟩ := Metric.mem_closure_iff.mp hycl (1 / 2 * ‖y‖) (by positivity)
    rcases hz_im with ⟨w, hw_ball, rfl⟩
    rw [mem_ball, dist_zero_right] at hw_ball
    rw [dist_eq_norm] at hdist
    exact ⟨w, hdist.le, hw_ball.le⟩

lemma uniformBallClosure_to_surjective [CompleteSpace E]
    (T : E →L[𝕜] F) (h : uniformBallClosure T) :
    Surjective T := by
  obtain ⟨C, Cnonneg, hC⟩ := approx_preimage_of_uniformBallClosure T h
  choose g hg using hC
  let step : F → F := fun y => y - T (g y)
  have hstep : ∀ y : F, ‖step y‖ ≤ 1 / 2 * ‖y‖ := fun y => (hg y).1
  intro y
  have hnle : ∀ n : ℕ, ‖step^[n] y‖ ≤ (1 / 2 : ℝ) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ']
      calc
        ‖step (step^[n] y)‖ ≤ 1 / 2 * ‖step^[n] y‖ := hstep _
        _ ≤ 1 / 2 * ((1 / 2 : ℝ) ^ n * ‖y‖) := by gcongr
        _ = (1 / 2 : ℝ) ^ (n + 1) * ‖y‖ := by rw [pow_succ', mul_assoc]
  let u : ℕ → E := fun n => g (step^[n] y)
  have ule : ∀ n : ℕ, ‖u n‖ ≤ (1 / 2 : ℝ) ^ n * (C * ‖y‖) := fun n => by
    calc
      ‖u n‖ ≤ C * ‖step^[n] y‖ := (hg _).2
      _ ≤ C * ((1 / 2 : ℝ) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2 : ℝ) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have su : Summable u := sNu.of_norm
  let x : E := ∑' n, u n
  have fsumeq : ∀ n : ℕ, T (∑ i ∈ Finset.range n, u i) = y - step^[n] y := by
    intro n
    induction n with
    | zero => simp [T.map_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, T.map_add, ih, iterate_succ_apply']
      dsimp only [step, u]
      abel
  have hsum : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 x) :=
    su.hasSum.tendsto_sum_nat
  have hL1 : Tendsto (fun n => T (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (T x)) :=
    (T.continuous.tendsto _).comp hsum
  simp only [fsumeq] at hL1
  have hL2 : Tendsto (fun n => y - step^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul
      tendsto_const_nhds
  have hTx : T x = y - 0 := tendsto_nhds_unique hL1 hL2
  rw [sub_zero] at hTx
  exact ⟨x, hTx⟩

end

end OMA.Mse4522800

theorem OMA.solution : type_of% @OMA.S_mse_4522800.main := by
  intro 𝕜 E F _ _ _ _ _ _ _ T
  refine ⟨⟨OMA.Mse4522800.surjective_to_uniformBallImage T, ?_⟩,
    ⟨fun h => OMA.Mse4522800.uniformBallImage_to_uniformBallClosure T
      (OMA.Mse4522800.surjective_to_uniformBallImage T h),
     OMA.Mse4522800.uniformBallClosure_to_surjective T⟩⟩
  intro h
  exact OMA.Mse4522800.uniformBallClosure_to_surjective T
    (OMA.Mse4522800.uniformBallImage_to_uniformBallClosure T h)
