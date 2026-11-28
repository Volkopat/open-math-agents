import OMAStatements.S_oeis_a113768
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

open Filter Topology Finset OMA.S_oeis_a113768

theorem OMA.solution : type_of% @OMA.S_oeis_a113768.main := by
  let r (n : ℕ) : ℝ := (value n : ℝ) ^ (1 / 3 : ℝ)
  let d (n : ℕ) : ℝ := (⌊r n⌋₊ : ℕ)
  have hgr (n : ℕ) : n + 1 ≤ value n := by
    induction n with
    | zero => simp [value]
    | succ n ih =>
      have hf : 1 ≤ ⌊r n⌋₊ := Nat.le_floor (by simpa [r] using Real.one_le_rpow (by exact_mod_cast (show 1 ≤ value n by omega) : (1 : ℝ) ≤ value n) (by norm_num : (0 : ℝ) ≤ 1 / 3))
      change n + 1 + 1 ≤ value n + ⌊r n⌋₊; omega
  have hpos (n : ℕ) : 0 < (value n : ℝ) := by exact_mod_cast (show 0 < value n by have := hgr n; omega)
  have hrpos (n : ℕ) : 0 < r n := Real.rpow_pos_of_pos (hpos n) _
  have hcube (n : ℕ) : r n ^ 3 = (value n : ℝ) := by dsimp [r]; rw [← Real.rpow_mul_natCast (hpos n).le]; norm_num
  have hnext (n : ℕ) : (value (n + 1) : ℝ) = (value n : ℝ) + d n := by change ((value n + ⌊r n⌋₊ : ℕ) : ℝ) = _; push_cast; rfl
  have hbig : Tendsto r atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_atTop_mono (fun n => (Nat.le_succ n).trans (hgr n)) tendsto_id))
  have hfl : Tendsto (fun n => d n / r n) atTop (𝓝 1) := by
    have lo := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_inv_atTop_zero.comp hbig)
    rw [sub_zero] at lo
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lo tendsto_const_nhds ?_ ?_
    · filter_upwards with n
      change 1 - (r n)⁻¹ ≤ d n / r n
      rw [le_div_iff₀ (hrpos n), sub_mul, inv_mul_cancel₀ (hrpos n).ne', one_mul]
      linarith [Nat.lt_floor_add_one (r n)]
    · filter_upwards with n
      exact (div_le_iff₀ (hrpos n)).2 (by simpa [d] using Nat.floor_le (hrpos n).le)
  have htr : Tendsto (fun n => (value (n + 1) : ℝ) / value n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add (hfl.mul ((tendsto_inv_atTop_zero.comp hbig).pow 2))
    norm_num at h
    exact h.congr fun n => by
      change 1 + (d n / r n) * (r n ^ 2)⁻¹ = _
      rw [hnext, ← hcube n]; field_simp [(hrpos n).ne']
  have hrr : Tendsto (fun n => r (n + 1) / r n) atTop (𝓝 1) := by
    have h := ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 3)).tendsto 1).comp htr
    rw [Real.one_rpow] at h
    exact h.congr fun n => Real.div_rpow (hpos (n + 1)).le (hpos n).le _
  have hst : Tendsto (fun n => r (n + 1) ^ 2 - r n ^ 2) atTop (𝓝 (2 / 3)) := by
    have h := (hfl.mul (hrr.add_const 1)).div (((hrr.pow 2).add hrr).add_const 1) (by norm_num)
    norm_num at h
    refine h.congr fun n => ?_
    have hc : r (n + 1) ^ 3 - r n ^ 3 = d n := by rw [hcube, hcube, hnext]; ring
    have hd : 0 < (r (n + 1) / r n) ^ 2 + r (n + 1) / r n + 1 := by have := hrpos n; have := hrpos (n + 1); positivity
    symm; change r (n + 1) ^ 2 - r n ^ 2 = (d n / r n) * (r (n + 1) / r n + 1) / ((r (n + 1) / r n) ^ 2 + r (n + 1) / r n + 1)
    rw [← hc, eq_div_iff hd.ne']; field_simp [(hrpos n).ne']; ring
  have hsq : Tendsto (fun n : ℕ => r n ^ 2 / ((n : ℝ) + 1)) atTop (𝓝 (2 / 3)) := by
    have h := (hst.cesaro.add (tendsto_const_div_atTop_nhds_zero_nat (r 0 ^ 2))).mul (tendsto_natCast_div_add_atTop (1 : ℝ))
    rw [add_zero, mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    change ((n : ℝ)⁻¹ * ∑ i ∈ range n, (r (i + 1) ^ 2 - r i ^ 2) + r 0 ^ 2 / n) * (n / (n + 1)) = _
    rw [sum_range_sub fun i => r i ^ 2]; field_simp; ring
  exact (hsq.mul hsq.sqrt).congr fun n => by
    change (r n ^ 2 / ((n : ℝ) + 1)) * Real.sqrt (r n ^ 2 / ((n : ℝ) + 1)) = _
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (hrpos n).le, ← hcube, div_mul_div_comm]; congr 1
