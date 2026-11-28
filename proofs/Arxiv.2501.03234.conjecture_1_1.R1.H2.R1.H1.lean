import OMAReductions.R_Arxiv_2501_03234_conjecture_1_1_R1_H2_R1
import Mathlib

/-! Odd harmonic sums are subadditive at multiplicative odd endpoints. -/
open Finset

/-- Group the tail after k into blocks of length 2k+1. The first denominator
of block j equals (2k+1)(2j+1), so the block costs at most 1/(2j+1). -/
lemma oddHarm_product (k l : ℕ) :
    (∑ i ∈ range (k + (2*k+1)*l), (1 : ℚ)/(2*i+1)) ≤
      (∑ i ∈ range k, (1 : ℚ)/(2*i+1)) + ∑ j ∈ range l, (1 : ℚ)/(2*j+1) := by
  induction l with
  | zero => simp
  | succ l ih =>
    let start := k + (2*k+1)*l
    let width := 2*k+1
    have block (j : ℕ) : (1 : ℚ)/(2*((start+j:ℕ):ℚ)+1) ≤
        1 / ((width:ℚ)*(2*l+1)) := by
      apply one_div_le_one_div_of_le (by dsimp [width]; positivity)
      dsimp [start, width]
      push_cast
      linarith
    rw [Nat.mul_succ, ← Nat.add_assoc, sum_range_add, sum_range_succ (n := l)]
    have b := sum_le_sum (s := range width) (fun j _ => block j)
    rw [sum_const, card_range, nsmul_eq_mul] at b
    have cancel : (width:ℚ) * (1 / ((width:ℚ)*(2*l+1))) = 1/(2*l+1) := by
      have hw : (width:ℚ) ≠ 0 := by dsimp [width]; positivity
      field_simp
    rw [cancel] at b
    exact (add_le_add ih b).trans_eq (add_assoc _ _ _)

theorem OMA.solution : OMA.R_Arxiv_2501_03234_conjecture_1_1_R1_H2_R1.H1 := by
  intro n k _ h
  have h' : n ≤ k+(2*k+1)*k := by nlinarith
  have mono := sum_le_sum_of_subset_of_nonneg (f := fun j : ℕ => (1:ℚ)/(2*j+1))
    (range_subset_range.mpr h') (fun _ _ _ => by positivity)
  simpa only [two_mul] using mono.trans (oddHarm_product k k)
