import OMAStatements.S_oeis_a140427
import Mathlib.Tactic.IntervalCases

namespace OMA.S_oeis_a140427

open Finset

private theorem digit_period (i : ℕ) : digit 23 (8+i) = digit 23 i := by
  unfold digit
  rw [show (8+i)%8=i%8 by omega]

private theorem next_period (n : ℕ) :
    (∑ i ∈ range (n+8), digit 23 i) = 4 + ∑ i ∈ range n, digit 23 i := by
  have h : (∑ i ∈ range 8, digit 23 i) = 4 := by decide +kernel
  rw [Nat.add_comm n 8, sum_range_add, h]
  simp_rw [digit_period]

end OMA.S_oeis_a140427

open OMA.S_oeis_a140427 in
theorem OMA.solution : type_of% @OMA.S_oeis_a140427.main := by
  refine ⟨23, by decide +kernel, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 8
    · interval_cases n <;> decide +kernel
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 8≤n by omega)
      rw [Nat.add_comm 8 k, kappa, next_period, ih k (by omega), Nat.add_comm]
