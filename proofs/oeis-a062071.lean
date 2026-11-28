import OMAStatements.S_oeis_a062071
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

open OMA.S_oeis_a062071 Filter Topology

namespace SelfPowerFloors

noncomputable def scaledFloor (n d : ℕ) : ℝ := ((n/d:ℕ):ℝ)/(n:ℝ)

lemma bounds (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    1/(d:ℝ)-1/(n:ℝ) ≤ scaledFloor n d ∧ scaledFloor n d ≤ 1/(d:ℝ) := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have qr : ((n%d:ℕ):ℝ)+(d:ℝ)*((n/d:ℕ):ℝ) = (n:ℝ) := by
    exact_mod_cast Nat.mod_add_div n d
  have rem_lt : ((n%d:ℕ):ℝ) < d := by exact_mod_cast Nat.mod_lt n hd
  have rem_nn : 0 ≤ ((n%d:ℕ):ℝ) := by positivity
  unfold scaledFloor
  constructor
  · rw [sub_le_iff_le_add, ← add_div, div_le_div_iff₀ hd' hn']
    nlinarith
  · rw [div_le_div_iff₀ hn' hd']
    nlinarith

lemma each_limit (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n => scaledFloor n d) atTop (𝓝 (1/(d:ℝ))) := by
  have lo : Tendsto (fun n : ℕ => 1/(d:ℝ)-1/(n:ℝ)) atTop (𝓝 (1/(d:ℝ))) := by
    simpa using (tendsto_const_nhds (x := 1/(d:ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0] with n hn using (bounds n d hn hd).1
  · filter_upwards [eventually_gt_atTop 0] with n hn using (bounds n d hn hd).2

/-- Normalized floor sums commute with any summable series of reciprocal denominators. -/
lemma floor_sum_limit (d : ℕ → ℕ) (hd : ∀ k, 0 < d k)
    (hs : Summable (fun k => 1/(d k : ℝ))) :
    Tendsto (fun n : ℕ => (∑' k, ((n / d k : ℕ):ℝ)) / (n:ℝ))
      atTop (𝓝 (∑' k, 1/(d k : ℝ))) := by
  have h := tendsto_tsum_of_dominated_convergence (f := fun n k => scaledFloor n (d k))
    hs (fun k => each_limit (d k) (hd k)) (by
      filter_upwards [eventually_gt_atTop 0] with n hn
      intro k
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ scaledFloor n (d k) by unfold scaledFloor; positivity)]
      exact (bounds n (d k) hn (hd k)).2)
  simpa only [scaledFloor, tsum_div_const] using h

lemma reciprocal_summable : Summable (fun k => 1/(denominator k : ℝ)) := by
  have hs : Summable (fun k : ℕ => 1/((k:ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun k : ℕ => 1/(k:ℝ)^2) 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hs
  intro k
  have hk : (k+1)^2 ≤ denominator k := by
    cases k with
    | zero => decide
    | succ j => exact Nat.pow_le_pow_right (by omega) (by omega)
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hk)

end SelfPowerFloors

open SelfPowerFloors

theorem OMA.solution : type_of% @OMA.S_oeis_a062071.main := by
  have pos : 0 < constantValue := reciprocal_summable.tsum_pos
    (fun k => by positivity) 0 (by norm_num [denominator])
  have h := floor_sum_limit denominator (fun k => by unfold denominator; positivity) reciprocal_summable
  change Tendsto (fun n : ℕ => floorSum n / (n:ℝ)) atTop (𝓝 constantValue) at h
  have h' := h.div_const constantValue
  rw [div_self pos.ne'] at h'
  simpa only [div_div, mul_comm] using h'
