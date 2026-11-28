import OMAReductions.R_Erdos687_erdos_687_parts_iii_R3_H1_R2
import Mathlib

-- Proof of Erdos687.erdos_687.parts.iii.R3.H1.R2.H3
-- Credit: @carterleffen

/-!
# Prime extraction from the second difference of `ψ₁`

Proves `H3` of `Erdos687.erdos_687.parts.iii.R3.H1.R2`: eventually, if
`(h n)^2 / 4 < Δ²_{h n} ψ₁(n + 1)` with `h n = ⌊n^(33/50)⌋₊ / 2`, then there exists a prime
`p` with `n < p` and `(p - n)^3 ≤ n^2`, using the tent upper bound and Mathlib's
`Chebyshev.psi_sub_theta_le_mul_sqrt`.
-/
section
namespace Cramer
open ArithmeticFunction Finset
noncomputable def vdr (n : ℕ) : ℝ := ∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)
lemma viB (n : ℕ) (hn : 1 ≤ n) :
    vdr n = n * ∑ k ∈ range n, (Λ k : ℝ) * (1 - (k : ℝ) / n) := by
  rw [vdr, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp
lemma veh {n N : ℕ} (hn : n ≤ N) :
    vdr n = ∑ k ∈ range N, (Λ k : ℝ) * max ((n : ℝ) - k) 0 := by
  rw [vdr]
  rw [← sum_subset (range_subset_range.mpr hn)]
  · refine sum_congr rfl fun k hk => ?_
    have : (k : ℝ) < n := by exact_mod_cast mem_range.mp hk
    rw [max_eq_left (by linarith)]
  · intro k _ hk
    have : (n : ℝ) ≤ k := by exact_mod_cast not_lt.mp (by simpa using hk)
    rw [max_eq_right (by linarith), mul_zero]
theorem vgv (a h : ℕ) :
    vdr (a + 2 * h) - 2 * vdr (a + h) + vdr a
      ≤ h * ∑ k ∈ Ico a (a + 2 * h), (Λ k : ℝ) := by
  set b := a + 2 * h
  rw [veh (N := b) le_rfl, veh (N := b) (by omega),
    veh (n := a) (N := b) (by omega), mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib]
  rw [← sum_range_add_sum_Ico _ (show a ≤ b by omega)]
  have h0 : ∑ k ∈ range a, ((Λ k : ℝ) * max ((b : ℝ) - k) 0 - 2 * ((Λ k : ℝ) *
      max (((a + h : ℕ) : ℝ) - k) 0) + (Λ k : ℝ) * max ((a : ℝ) - k) 0) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    have hk' : (k : ℝ) < a := by exact_mod_cast mem_range.mp hk
    have hb : (b : ℝ) = a + 2 * h := by simp [b]
    push_cast
    have hh : (0 : ℝ) ≤ h := h.cast_nonneg
    rw [max_eq_left (by rw [hb]; linarith), max_eq_left (by linarith),
      max_eq_left (by linarith), hb]
    ring
  rw [h0, zero_add, Finset.mul_sum]
  refine sum_le_sum fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := mem_Ico.mp hk
  have hΛ : (0 : ℝ) ≤ Λ k := vonMangoldt_nonneg
  have hak : (a : ℝ) ≤ k := by exact_mod_cast hk1
  have hkb : (k : ℝ) < a + 2 * h := by exact_mod_cast hk2
  have hb : (b : ℝ) = a + 2 * h := by simp [b]
  rw [max_eq_right (show (a : ℝ) - k ≤ 0 by linarith), hb]
  push_cast
  have key : max ((a : ℝ) + 2 * h - k) 0 - 2 * max ((a : ℝ) + h - k) 0 ≤ h := by
    rcases le_total ((a : ℝ) + h) k with h1 | h1
    · rw [max_eq_right (show (a : ℝ) + h - k ≤ 0 by linarith),
        max_eq_left (show (0 : ℝ) ≤ a + 2 * h - k by linarith)]; linarith
    · rw [max_eq_left (show (0 : ℝ) ≤ a + h - k by linarith),
        max_eq_left (show (0 : ℝ) ≤ a + 2 * h - k by linarith)]; linarith
  nlinarith
end Cramer
end
namespace R3Arithmetic
open Filter ArithmeticFunction Finset Cramer

theorem arithmetic_leaf : OMA.R_Erdos687_erdos_687_parts_iii_R3_H1_R2.H3 := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have ht : Tendsto (fun n : ℕ => (n:ℝ) ^ (4/25:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (16 * |C| + 4)), eventually_ge_atTop 1] with n hg hn
  let h := (fun n : ℕ => ⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ / 2) n
  let a := n+1
  let Y := a+2*h
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hfl := Nat.lt_floor_add_one ((n:ℝ) ^ (33/50:ℝ))
  have h2 : 2*h ≤ ⌊(n:ℝ)^(33/50:ℝ)⌋₊ := by dsimp [h]; omega
  have h2' : ⌊(n:ℝ)^(33/50:ℝ)⌋₊ ≤ 2*h+1 := by dsimp [h]; omega
  have hu : ((2*h:ℕ):ℝ) ≤ (n:ℝ)^(33/50:ℝ) :=
    (Nat.cast_le.mpr h2).trans (Nat.floor_le (by positivity))
  have hsmall : (n:ℝ)^(33/50:ℝ) ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 (show (33/50:ℝ) ≤ 1 by norm_num)
  have hy : (Y:ℝ) ≤ 4*n := by dsimp [Y,a]; push_cast at hu ⊢; linarith
  have hs : Real.sqrt Y ≤ 2 * Real.sqrt n := by
    calc _ ≤ Real.sqrt (4 * (n:ℝ)) := Real.sqrt_le_sqrt hy
         _ = _ := by rw [Real.sqrt_mul (by norm_num)]; norm_num
  have hs1 : (1:ℝ) ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
  have he : (n:ℝ)^(33/50:ℝ) = Real.sqrt n * (n:ℝ)^(4/25:ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]; norm_num
  have hc : 4 * (C * Real.sqrt Y) ≤ (h:ℝ) := by
    have f' : (⌊(n:ℝ)^(33/50:ℝ)⌋₊ : ℝ) ≤ 2*(h:ℝ)+1 := by exact_mod_cast h2'
    change 16 * |C| + 4 ≤ (n:ℝ) ^ (4/25:ℝ) at hg
    have m1 := mul_le_mul_of_nonneg_left hg (Real.sqrt_nonneg (n:ℝ))
    have m2 := mul_le_mul_of_nonneg_left hs (abs_nonneg C)
    have m3 := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg (Y:ℝ))
    rw [he] at hfl f'
    nlinarith
  intro hbig
  by_contra! hbad
  have hnop : ∀ k ∈ Ico a Y, ¬ k.Prime := by
    intro k hk hkp
    have hk' := Finset.mem_Ico.mp hk
    have hnlt : n < k := by dsimp [a] at hk'; omega
    have hk2 : k-n ≤ 2*h := by dsimp [a,Y] at hk'; omega
    have hle : ((k-n:ℕ):ℝ) ≤ (n:ℝ)^(2/3:ℝ) :=
      ((Nat.cast_le.mpr hk2).trans hu).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num))
    have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (k-n:ℕ)) hle 3
    rw [← Real.rpow_mul_natCast hn0.le] at hpow
    norm_num at hpow
    exact (not_lt_of_ge (by exact_mod_cast hpow)) (hbad k hkp hnlt)
  have hsub : Ico a Y ⊆ (Ioc 0 ⌊(Y:ℝ)⌋₊).filter (fun k => ¬ k.Prime) := by
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    rw [Finset.mem_filter,Finset.mem_Ioc,Nat.floor_natCast]
    exact ⟨⟨by dsimp [a] at hk'; omega, hk'.2.le⟩,hnop k hk⟩
  have hsum : ∑ k ∈ Ico a Y, (vonMangoldt k : ℝ) ≤ C * Real.sqrt Y := by
    calc _ ≤ ∑ k ∈ (Ioc 0 ⌊(Y:ℝ)⌋₊).filter (fun k => ¬ k.Prime), (vonMangoldt k : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
         _ = Chebyshev.psi Y - Chebyshev.theta Y := (Chebyshev.psi_sub_theta_eq_sum_not_prime _).symm
         _ ≤ _ := hC _
  have htent := vgv a h
  change (h:ℝ)^2/4 < vdr (a+2*h) - 2*vdr (a+h) + vdr a at hbig
  have hle := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg h)
  have hle' := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg h)
  change _ ≤ (h : ℝ) * (∑ k ∈ Ico a Y, (vonMangoldt k : ℝ)) at htent
  nlinarith

end R3Arithmetic
theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R3_H1_R2.H3 := R3Arithmetic.arithmetic_leaf
