import OMAStatements.S_oeis_a178481
import Mathlib

namespace A178481H

open Filter Topology

lemma eventually_lt (k : ℕ) : ∃ L0 : ℕ, ∀ L ≥ L0, 10 * (9 * (k * L)) < 10 ^ L := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ) < 10)
  have hc : (0:ℝ) < 90 * (k:ℝ) + 1 := by positivity
  have hpos : (0:ℝ) < 1 / (90 * (k:ℝ) + 1) := by positivity
  have hev := h.eventually (gt_mem_nhds hpos)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨L0, hL0⟩ := hev
  refine ⟨L0, fun L hL => ?_⟩
  have h1 := hL0 L hL
  have h10 : (0:ℝ) < 10 ^ L := by positivity
  rw [div_lt_div_iff₀ h10 hc, pow_one] at h1
  have hL : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
  have key : ((10 * (9 * (k * L)) : ℕ) : ℝ) < ((10 ^ L : ℕ) : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast key

lemma digit_sum_le (x : ℕ) : (Nat.digits 10 x).sum ≤ 9 * (Nat.digits 10 x).length := by
  have h := List.sum_le_card_nsmul (Nat.digits 10 x) 9 (fun d hd => by
    have := Nat.digits_lt_base (by norm_num : 1 < 10) hd
    omega)
  simpa [mul_comm] using h

lemma len_le (x L : ℕ) (h : x < 10 ^ L) : (Nat.digits 10 x).length ≤ L := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have h1 := Nat.base_pow_length_digits_le 10 x (by norm_num) (by omega)
    have h2 : 10 ^ (Nat.digits 10 x).length < 10 ^ (L + 1) := by
      rw [pow_succ]
      omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp h2
    omega

lemma len_gt (x L : ℕ) (h : 10 ^ L ≤ x) : L < (Nat.digits 10 x).length := by
  have h1 := Nat.lt_base_pow_length_digits (b := 10) (m := x) (by norm_num)
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp (lt_of_le_of_lt h h1)

lemma len_pow (k x : ℕ) (hk : 1 ≤ k) :
    (Nat.digits 10 (x ^ k)).length ≤ k * (Nat.digits 10 x).length := by
  have h1 := Nat.lt_base_pow_length_digits (b := 10) (m := x) (by norm_num)
  have h2 : x ^ k < (10 ^ (Nat.digits 10 x).length) ^ k := Nat.pow_lt_pow_left h1 (by omega)
  rw [← pow_mul, mul_comm] at h2
  exact len_le _ _ h2

lemma g_le (k x : ℕ) (hk : 1 ≤ k) :
    OMA.S_oeis_a178481.g k x ≤ 9 * (k * (Nat.digits 10 x).length) := by
  unfold OMA.S_oeis_a178481.g
  have h1 := digit_sum_le (x ^ k)
  have h2 := len_pow k x hk
  omega

lemma bounded (k x0 : ℕ) (hk : 1 ≤ k) :
    ∃ B : ℕ, x0 ≤ B ∧ ∀ x ≤ B, OMA.S_oeis_a178481.g k x ≤ B := by
  obtain ⟨L0, hL0⟩ := eventually_lt k
  refine ⟨max x0 (9 * (k * L0)), le_max_left _ _, fun x hx => ?_⟩
  by_cases hc : x < 10 ^ L0
  · have hl := len_le x L0 hc
    have hm : k * (Nat.digits 10 x).length ≤ k * L0 := Nat.mul_le_mul_left k hl
    have h3 := g_le k x hk
    have h5 := le_max_right x0 (9 * (k * L0))
    omega
  · rw [not_lt] at hc
    have hlen := len_gt x L0 hc
    have hp : 0 < 10 ^ L0 := by positivity
    have hx0 : x ≠ 0 := by omega
    have h1 := Nat.base_pow_length_digits_le 10 x (by norm_num) hx0
    have h2 := hL0 _ hlen.le
    have h3 := g_le k x hk
    have h4 : 9 * (k * (Nat.digits 10 x).length) < x := by omega
    omega

end A178481H

theorem OMA.solution : type_of% @OMA.S_oeis_a178481.main := by
  intro k hk x0
  obtain ⟨B, hxB, hB⟩ := A178481H.bounded k x0 hk
  have hiter : ∀ i, (OMA.S_oeis_a178481.g k)^[i] x0 ≤ B := by
    intro i
    induction i with
    | zero => simpa using hxB
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact hB _ ih
  have hmaps : Set.MapsTo (fun i => (OMA.S_oeis_a178481.g k)^[i] x0)
      ↑(Finset.range (B + 2)) ↑(Finset.range (B + 1)) := by
    intro i _
    simp only [Finset.coe_range, Set.mem_Iio]
    have := hiter i
    omega
  obtain ⟨i, _, j, _, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simp) hmaps
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, heq⟩
  · exact ⟨j, i, h, heq.symm⟩
