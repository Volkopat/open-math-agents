import OMAStatements.S_oeis_a345096
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-!
Every term contributes one. An extra contribution k−1 occurs precisely
when k^i divides n. Each divisor k contributes at most n in excess,
and pairing complementary divisors gives at most 2(⌊√n⌋+1) choices of k.
-/

open Finset Filter Topology
open OMA.S_oeis_a345096

namespace DivisorFloorSum

lemma summand_eq (n k i : ℕ) (hk : 0 < k) :
    summand n k i = 1 + if k^i ∣ n then k-1 else 0 := by
  have hm : (k^i : ℕ) ≠ 0 := pow_ne_zero i hk.ne'
  have hm' : (((k^i : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast hm
  unfold summand
  dsimp only
  by_cases hd : k^i ∣ n
  · obtain ⟨t, ht⟩ := hd
    have hq : (n : ℚ) / ((k^i : ℕ) : ℚ) = t := by
      apply (div_eq_iff hm').2
      rw [mul_comm]
      exact_mod_cast ht
    rw [if_pos (show k^i ∣ n from ⟨t, ht⟩), hq]
    simp
    omega
  · have hq : (n : ℚ) / ((k^i : ℕ) : ℚ) ∉ Set.range (Int.cast : ℤ → ℚ) := by
      rintro ⟨z, hz⟩
      have he := (div_eq_iff hm').1 hz.symm
      apply hd
      apply Int.natCast_dvd_natCast.mp
      refine ⟨z, ?_⟩
      rw [mul_comm]
      exact_mod_cast he
    rw [if_neg hd, (Int.ceil_eq_floor_add_one_iff_notMem _).2 hq]
    simp

def powers (n k : ℕ) : Finset ℕ := (Icc 1 k).filter (fun i => k^i ∣ n)

lemma row (n k : ℕ) (hk : 0 < k) :
    ∑ i ∈ Icc 1 k, summand n k i = k + (powers n k).card * (k-1) := by
  simp_rw [summand_eq n k _ hk]
  rw [Finset.sum_add_distrib, ← Finset.sum_filter]
  simp [powers]

lemma index_bound (k : ℕ) (hk : 2 ≤ k) (i : ℕ) (hi : 1 ≤ i) : i*k ≤ k^i := by
  induction i, hi using Nat.le_induction with
  | base => simp
  | succ i hi ih =>
    rw [pow_succ, Nat.add_mul, one_mul]
    have a : 2*(i*k) ≤ (i*k)*k := by nlinarith [Nat.mul_le_mul_left (i*k) hk]
    have b : k ≤ i*k := by simpa using Nat.mul_le_mul_right k hi
    exact le_trans (by omega : i*k + k ≤ (i*k)*k) (Nat.mul_le_mul_right k ih)

lemma extra_bound {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    (powers n k).card * (k-1) ≤ if k ∈ n.divisors then n else 0 := by
  by_cases hd : k ∈ n.divisors
  · rw [if_pos hd]
    by_cases h1 : k = 1
    · simp [h1]
    have hsub : powers n k ⊆ Icc 1 (n/k) := by
      intro i hi
      obtain ⟨hi, hdiv⟩ := Finset.mem_filter.mp hi
      have hi' := (Finset.mem_Icc.mp hi).1
      refine Finset.mem_Icc.mpr ⟨hi', (Nat.le_div_iff_mul_le hk).2 ?_⟩
      exact (index_bound k (by omega) i hi').trans (Nat.le_of_dvd hn hdiv)
    have count := Finset.card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at count
    exact (Nat.mul_le_mul count (Nat.sub_le k 1)).trans (Nat.div_mul_le_self n k)
  · rw [if_neg hd]
    have hempty : powers n k = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hi, hdiv⟩ := Finset.mem_filter.mp hi
      have hi' := (Finset.mem_Icc.mp hi).1
      exact hd (Nat.mem_divisors.mpr ⟨(dvd_pow_self k (by omega : i ≠ 0)).trans hdiv, hn.ne'⟩)
    simp [hempty]

lemma divisor_bound (n : ℕ) (hn : 0 < n) :
    n.divisors.card ≤ 2 * (Nat.sqrt n + 1) := by
  let small := Finset.range (Nat.sqrt n + 1)
  have cover : n.divisors ⊆ small ∪ small.image (fun k => n/k) := by
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hprod := Nat.div_mul_cancel hdvd
    by_cases hsmall : d ≤ Nat.sqrt n
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    have hq : 0 < n/d := by
      by_contra h
      have hz := Nat.eq_zero_of_not_pos h
      exact hn.ne' (by simpa only [hz, zero_mul] using hprod.symm)
    have hs : n/d ≤ Nat.sqrt n := by
      by_contra! hl
      have square := Nat.mul_le_mul (show Nat.sqrt n+1 ≤ n/d by omega)
        (show Nat.sqrt n+1 ≤ d by omega)
      rw [hprod] at square
      exact (Nat.not_le_of_lt (Nat.lt_succ_sqrt n)) square
    refine ⟨n/d, Finset.mem_range.mpr (by omega), ?_⟩
    calc
      n / (n/d) = ((n/d)*d) / (n/d) := congrArg (fun t : ℕ => t/(n/d)) hprod.symm
      _ = d := Nat.mul_div_cancel_left d hq
  have h := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have h' := Finset.card_image_le (s := small) (f := fun k => n/k)
  have hc : small.card = Nat.sqrt n+1 := Finset.card_range _
  omega

def triangle (n : ℕ) : ℕ := ∑ k ∈ Icc 1 n, k

lemma twice_triangle (n : ℕ) : 2 * triangle n = n*(n+1) := by
  induction n with
  | zero => simp [triangle]
  | succ n ih =>
    have ht : triangle (n+1) = triangle n + (n+1) := by
      unfold triangle
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [ht]
    nlinarith

lemma bounds (n : ℕ) (hn : 0 < n) :
    triangle n ≤ value n ∧ value n ≤ triangle n + 2*(Nat.sqrt n+1)*n := by
  have hsum : value n = triangle n + ∑ k ∈ Icc 1 n, (powers n k).card*(k-1) := by
    unfold value triangle
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k hk => row n k (Finset.mem_Icc.mp hk).1
  rw [hsum]
  refine ⟨by omega, Nat.add_le_add_left ?_ _⟩
  calc
    _ ≤ ∑ k ∈ Icc 1 n, (if k ∈ n.divisors then n else 0) :=
      Finset.sum_le_sum fun k hk => extra_bound hn (Finset.mem_Icc.mp hk).1
    _ = ((Icc 1 n).filter (fun k => k ∈ n.divisors)).card * n := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ n.divisors.card * n := Nat.mul_le_mul_right n (Finset.card_le_card
      (fun _ hi => (Finset.mem_filter.mp hi).2))
    _ ≤ _ := Nat.mul_le_mul_right n (divisor_bound n hn)

lemma triangle_limit : Tendsto (fun n : ℕ => (triangle n : ℝ)/(n:ℝ)^2) atTop (𝓝 (1/2)) := by
  have h := (tendsto_const_nhds (x := (1:ℝ))).add (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  have hh := h.div_const 2
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have ht : 2 * (triangle n : ℝ) = (n:ℝ) * (n+1) := by exact_mod_cast twice_triangle n
  change (1 + 1/(n:ℝ))/2 = (triangle n : ℝ)/(n:ℝ)^2
  field_simp
  linarith

lemma small_ratio :
    Tendsto (fun n : ℕ => (Real.sqrt n + 1)/(n:ℝ)) atTop (𝓝 0) := by
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have h := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hnat)).add
    (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  change (Real.sqrt n)⁻¹ + 1/(n:ℝ) = (Real.sqrt n + 1)/(n:ℝ)
  field_simp [(Real.sqrt_pos.2 hn').ne']
  nlinarith [Real.sq_sqrt hn'.le]

end DivisorFloorSum

open DivisorFloorSum

theorem OMA.solution : type_of% @OMA.S_oeis_a345096.main := by
  have hupper := triangle_limit.add (small_ratio.const_mul 2)
  rw [mul_zero, add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' triangle_limit hupper
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_le_div_of_nonneg_right (by exact_mod_cast (bounds n hn).1) (sq_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
    have hs : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
      apply Real.le_sqrt_of_sq_le
      exact_mod_cast Nat.sqrt_le' n
    have hu : (value n : ℝ) ≤ (triangle n : ℝ) + 2*((Nat.sqrt n : ℝ)+1)*n := by
      exact_mod_cast (bounds n hn).2
    change (value n : ℝ)/(n:ℝ)^2 ≤ (triangle n : ℝ)/(n:ℝ)^2 + 2*((Real.sqrt n+1)/n)
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hs hn'.le]
