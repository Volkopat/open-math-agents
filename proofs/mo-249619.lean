import OMAStatements.S_mo_249619
import Mathlib

-- Problem: mo-249619, for every enumeration r of the rationals in [0, 1] there are a strictly
-- increasing integer sequence k and a point y in [0, 1] with bump(k_n (y - r_n)) -> 0.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Take the irrational y = sqrt 2 - 1. Then y - r_n is never 0, and with
-- k_n = n + sum_{i <= n} ceil(1 / |y - r_i|) the sequence k is strictly increasing and
-- |k_n (y - r_n)| >= 1, where the bump function vanishes. So the sequence is identically 0.

namespace MO249619

open OMA.S_mo_249619

lemma bump_zero (z : ℝ) (hz : 1 ≤ |z|) : bump z = 0 := by
  unfold bump
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    rcases le_abs.mp hz with h3 | h3
    · have e : z = 1 := le_antisymm h2 h3
      rw [e, mul_one, Real.cos_pi_div_two]
    · have e : z = -1 := by linarith
      have e2 : Real.pi * (-1) / 2 = -(Real.pi / 2) := by ring
      rw [e, e2, Real.cos_neg, Real.cos_pi_div_two]
  · rfl

end MO249619

open Filter Topology in
theorem OMA.solution : type_of% @OMA.S_mo_249619.main := by
  intro r
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hirr : Irrational (Real.sqrt 2 - 1) := by
    have h := irrational_sqrt_two.sub_natCast 1
    simpa using h
  have hd : ∀ n : ℕ, Real.sqrt 2 - 1 - (((r n).val : ℚ) : ℝ) ≠ 0 :=
    fun n => sub_ne_zero.mpr (hirr.ne_rat _)
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℤ,
      c = fun i => ⌈1 / |Real.sqrt 2 - 1 - (((r i).val : ℚ) : ℝ)|⌉ := ⟨_, rfl⟩
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    rw [hc]
    exact Int.ceil_nonneg (by positivity)
  refine ⟨fun n => (n : ℤ) + ∑ i ∈ Finset.range (n + 1), c i, ?_, Real.sqrt 2 - 1,
    ⟨by nlinarith [hs2, hs0], by nlinarith [hs2, hs0]⟩, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    show (n : ℤ) + ∑ i ∈ Finset.range (n + 1), c i
      < ((n + 1 : ℕ) : ℤ) + ∑ i ∈ Finset.range (n + 1 + 1), c i
    rw [Finset.sum_range_succ c (n + 1)]
    have h := hc0 (n + 1)
    push_cast
    omega
  · have hz : ∀ n : ℕ, OMA.S_mo_249619.bump
        ((((n : ℤ) + ∑ i ∈ Finset.range (n + 1), c i : ℤ) : ℝ)
          * (Real.sqrt 2 - 1 - (((r n).val : ℚ) : ℝ))) = 0 := by
      intro n
      apply MO249619.bump_zero
      have hpos : 0 < |Real.sqrt 2 - 1 - (((r n).val : ℚ) : ℝ)| := abs_pos.mpr (hd n)
      have h1 : c n ≤ (n : ℤ) + ∑ i ∈ Finset.range (n + 1), c i := by
        have h := Finset.single_le_sum (f := c) (fun i _ => hc0 i)
          (Finset.self_mem_range_succ n)
        have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
        linarith
      have h2 : 1 / |Real.sqrt 2 - 1 - (((r n).val : ℚ) : ℝ)| ≤ (c n : ℝ) := by
        rw [hc]
        exact Int.le_ceil _
      have h3 : (c n : ℝ) ≤ (((n : ℤ) + ∑ i ∈ Finset.range (n + 1), c i : ℤ) : ℝ) := by
        exact_mod_cast h1
      have h4 : (1 : ℝ) ≤ (c n : ℝ) * |Real.sqrt 2 - 1 - (((r n).val : ℚ) : ℝ)| :=
        (div_le_iff₀ hpos).mp h2
      rw [abs_mul]
      calc (1 : ℝ) ≤ (c n : ℝ) * |Real.sqrt 2 - 1 - (((r n).val : ℚ) : ℝ)| := h4
        _ ≤ |(((n : ℤ) + ∑ i ∈ Finset.range (n + 1), c i : ℤ) : ℝ)|
              * |Real.sqrt 2 - 1 - (((r n).val : ℚ) : ℝ)| :=
            mul_le_mul_of_nonneg_right (h3.trans (le_abs_self _)) hpos.le
    exact (tendsto_congr hz).mpr tendsto_const_nhds
