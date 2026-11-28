import OMAStatements.S_oeis_a073642
import Mathlib

open Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a073642.main := by
  have v (m : ℕ) : padicValNat 2 (2 * m + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  have d (m : ℕ) : ∑ j ∈ range (2 * m), padicValNat 2 (j + 1) = ∑ j ∈ range m, padicValNat 2 (j + 1) + m ∧
      ∑ j ∈ range (2 * m), padicValNat 2 (j + 1) ^ 2 =
        ∑ j ∈ range m, padicValNat 2 (j + 1) ^ 2 + 2 * ∑ j ∈ range m, padicValNat 2 (j + 1) + m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [mul_add_one, ← add_assoc, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ,
        sum_range_succ, sum_range_succ, v, show 2 * m + 1 + 1 = 2 * (m + 1) by ring,
        padicValNat.mul two_ne_zero (by omega), ih.1, ih.2]
      simp
      constructor <;> ring
  have key (n : ℕ) : ∑ j ∈ range n, padicValNat 2 (j + 1) + n.bitIndices.length = n ∧
      2 * n.bitIndices.sum + ∑ j ∈ range n, padicValNat 2 (j + 1) ^ 2 + 3 * n.bitIndices.length =
        3 * n := by
    induction n using Nat.strong_induction_on with | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases m with _ | m
      · simp
      have := ih (m + 1) (by omega)
      have := d (m + 1)
      simp [Nat.bitIndices_two_mul, List.sum_map_add]
      omega
    · have := ih m (by omega)
      have := d m
      simp [Nat.bitIndices_two_mul_add_one, sum_range_succ, v, List.sum_map_add]
      omega
  intro n _
  have := key n
  omega
