import OMAStatements.S_oeis_a286015
import Mathlib

open OMA.S_oeis_a286015

private theorem total_eq (t k : ℕ) : partTotal t k = k*t+firstRow k := by
  simp [partTotal, firstRow, Finset.sum_add_distrib, Nat.mul_comm]

theorem OMA.solution : type_of% @OMA.S_oeis_a286015.main := by
  intro n _
  apply Finset.sum_congr rfl
  intro j _
  let k := j+1
  change (∑ t ∈ Finset.range n, if partTotal t k = n then t+k else 0) = entry n k
  have hk : 0 < k := by omega
  have hrow : 0 < firstRow k := by simp [k, firstRow, Finset.sum_range_succ]
  unfold entry
  by_cases h : firstRow k ≤ n ∧ k ∣ n-firstRow k
  · let u := (n-firstRow k)/k
    have hu : u < n := (Nat.div_le_self _ _).trans_lt (by omega)
    have hmul : k*u = n-firstRow k := Nat.mul_div_cancel' h.2
    have he : partTotal u k = n := by rw [total_eq, hmul]; omega
    rw [if_pos h, Finset.sum_eq_single u, if_pos he]
    · change u+k = k+u
      omega
    · intro t _ hne
      apply if_neg
      intro ht
      apply hne
      have e : k*t = k*u := by
        rw [total_eq] at ht
        rw [total_eq] at he
        omega
      exact Nat.eq_of_mul_eq_mul_left hk e
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hu)).elim
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro t _
    apply if_neg
    intro he
    rw [total_eq] at he
    exact h ⟨by omega, ⟨t, by omega⟩⟩