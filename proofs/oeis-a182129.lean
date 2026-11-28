import OMAStatements.S_oeis_a182129
import Mathlib

namespace A182129H

open Filter Topology

lemma eventually_lt (n : ℕ) : ∃ L0 : ℕ, ∀ L ≥ L0, 10 * (9 * L) ^ n < 10 ^ L := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt n (by norm_num : (1:ℝ) < 10)
  have hpos : (0:ℝ) < 1 / (10 * 9 ^ n) := by positivity
  have hev := h.eventually (gt_mem_nhds hpos)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨L0, hL0⟩ := hev
  refine ⟨L0, fun L hL => ?_⟩
  have h1 := hL0 L hL
  have h10 : (0:ℝ) < 10 ^ L := by positivity
  have h9 : (0:ℝ) < 10 * 9 ^ n := by positivity
  rw [div_lt_div_iff₀ h10 h9] at h1
  have key : ((10 * (9 * L) ^ n : ℕ) : ℝ) < ((10 ^ L : ℕ) : ℝ) := by
    push_cast
    rw [mul_pow]
    nlinarith
  exact_mod_cast key

lemma digit_sum_le (x : ℕ) : (Nat.digits 10 x).sum ≤ 9 * (Nat.digits 10 x).length := by
  have h := List.sum_le_card_nsmul (Nat.digits 10 x) 9 (fun d hd => by
    have := Nat.digits_lt_base (by norm_num : 1 < 10) hd
    omega)
  simpa [mul_comm] using h

lemma f_le (n x : ℕ) : OMA.S_oeis_a182129.f n x ≤ (9 * (Nat.digits 10 x).length) ^ n := by
  unfold OMA.S_oeis_a182129.f
  exact Nat.pow_le_pow_left (digit_sum_le x) n

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

lemma bounded (n k : ℕ) : ∃ B : ℕ, k ≤ B ∧ ∀ x ≤ B, OMA.S_oeis_a182129.f n x ≤ B := by
  obtain ⟨L0, hL0⟩ := eventually_lt n
  refine ⟨max k ((9 * L0) ^ n), le_max_left _ _, fun x hx => ?_⟩
  by_cases hc : x < 10 ^ L0
  · have hl := len_le x L0 hc
    calc OMA.S_oeis_a182129.f n x ≤ (9 * (Nat.digits 10 x).length) ^ n := f_le n x
      _ ≤ (9 * L0) ^ n := Nat.pow_le_pow_left (by omega) n
      _ ≤ max k ((9 * L0) ^ n) := le_max_right _ _
  · rw [not_lt] at hc
    have hlen := len_gt x L0 hc
    have hp : 0 < 10 ^ L0 := by positivity
    have hx0 : x ≠ 0 := by omega
    have h1 := Nat.base_pow_length_digits_le 10 x (by norm_num) hx0
    have h2 := hL0 _ hlen.le
    have h3 := f_le n x
    have h4 : (9 * (Nat.digits 10 x).length) ^ n < x := by omega
    omega

end A182129H

theorem OMA.solution : type_of% @OMA.S_oeis_a182129.main := by
  intro n k _ _
  obtain ⟨B, hkB, hB⟩ := A182129H.bounded n k
  have hiter : ∀ i, (OMA.S_oeis_a182129.f n)^[i] k ≤ B := by
    intro i
    induction i with
    | zero => simpa using hkB
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact hB _ ih
  have hmaps : Set.MapsTo (fun i => (OMA.S_oeis_a182129.f n)^[i] k)
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
