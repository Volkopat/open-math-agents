import OMAStatements.S_oeis_a038663
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

open OMA.S_oeis_a038663 Filter Topology

namespace FibonacciFloorLimit

noncomputable def reciprocal (k : ℕ) : ℝ := 1/(Nat.fib (k+2) : ℝ)

noncomputable def scaled (n k : ℕ) : ℝ := ((n / Nat.fib (k+2) : ℕ) : ℝ)/(n:ℝ)

lemma fib_square_bound (k : ℕ) : (k+1)^2 ≤ 4*Nat.fib (k+2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    by_cases small : k < 2
    · interval_cases k <;> decide
    · have hk := Nat.le_fib_add_one (k+1)
      have step := Nat.fib_add_two (n := k+1)
      nlinarith

lemma fib_positive (k : ℕ) : 0 < (Nat.fib (k+2) : ℝ) := by
  exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < k+2)

lemma summable_reciprocal : Summable reciprocal := by
  have hs : Summable (fun k : ℕ => 1/((k:ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun k : ℕ => 1/(k:ℝ)^2) 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  apply Summable.of_nonneg_of_le (fun k => by unfold reciprocal; positivity) _ (hs.mul_left 4)
  intro k
  have hk : ((k:ℝ)+1)^2 ≤ 4*(Nat.fib (k+2):ℝ) := by exact_mod_cast fib_square_bound k
  have hf := fib_positive k
  unfold reciprocal
  rw [← mul_div_assoc, mul_one, div_le_div_iff₀ hf (by positivity)]
  simpa only [one_mul] using hk

lemma scaled_bounds (n k : ℕ) (hn : 0 < n) :
    reciprocal k - 1/(n:ℝ) ≤ scaled n k ∧ scaled n k ≤ reciprocal k := by
  let d := Nat.fib (k+2)
  have hd : 0 < d := Nat.fib_pos.mpr (by omega)
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have qr : ((n%d:ℕ):ℝ)+(d:ℝ)*((n/d:ℕ):ℝ) = (n:ℝ) := by
    exact_mod_cast Nat.mod_add_div n d
  have small : ((n%d:ℕ):ℝ) < (d:ℝ) := by exact_mod_cast Nat.mod_lt n hd
  have pos : 0 ≤ ((n%d:ℕ):ℝ) := by positivity
  change 1/(d:ℝ)-1/(n:ℝ) ≤ ((n/d:ℕ):ℝ)/(n:ℝ) ∧ ((n/d:ℕ):ℝ)/(n:ℝ) ≤ 1/(d:ℝ)
  constructor
  · rw [sub_le_iff_le_add, ← add_div, div_le_div_iff₀ hd' hn']
    nlinarith
  · rw [div_le_div_iff₀ hn' hd']
    nlinarith

lemma pointwise (k : ℕ) : Tendsto (fun n => scaled n k) atTop (𝓝 (reciprocal k)) := by
  have lo : Tendsto (fun n : ℕ => reciprocal k - 1/(n:ℝ)) atTop (𝓝 (reciprocal k)) := by
    simpa using (tendsto_const_nhds (x := reciprocal k)).sub (tendsto_const_div_atTop_nhds_zero_nat 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0] with n hn using (scaled_bounds n k hn).1
  · filter_upwards [eventually_gt_atTop 0] with n hn using (scaled_bounds n k hn).2

lemma summed_limit : Tendsto (fun n : ℕ => value n / (n:ℝ)) atTop (𝓝 (∑' k, reciprocal k)) := by
  have ht := tendsto_tsum_of_dominated_convergence (f := scaled) (g := reciprocal)
    summable_reciprocal pointwise (by
      filter_upwards [eventually_gt_atTop 0] with n hn
      intro k
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ scaled n k by unfold scaled; positivity)]
      exact (scaled_bounds n k hn).2)
  simpa only [scaled, tsum_div_const, value] using ht

lemma identify : reciprocalConstant - 1 = ∑' k, reciprocal k := by
  have hs : Summable (fun k : ℕ => 1/(Nat.fib (k+1):ℝ)) :=
    (summable_nat_add_iff 1).mp summable_reciprocal
  unfold reciprocalConstant
  rw [hs.tsum_eq_zero_add]
  simp [reciprocal, Nat.add_assoc]

end FibonacciFloorLimit

open FibonacciFloorLimit

theorem OMA.solution : type_of% @OMA.S_oeis_a038663.main := by
  have pos : 0 < ∑' k, reciprocal k := summable_reciprocal.tsum_pos
    (fun k => by unfold reciprocal; positivity) 0 (by norm_num [reciprocal, Nat.fib])
  have h := summed_limit.div_const (∑' k, reciprocal k)
  rw [div_self pos.ne'] at h
  simpa only [identify, div_div, mul_comm] using h
