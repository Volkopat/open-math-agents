import OMAStatements.S_oeis_a338722
import Mathlib

open OMA.S_oeis_a338722

private theorem total_eq (t k : ℕ) : partTotal t k = k*t+firstRow k := by
  simp [partTotal, firstRow, Finset.sum_add_distrib, Nat.mul_comm]

private theorem row_pos (j : ℕ) : 0 < firstRow (j+1) := by
  simp [firstRow, Finset.sum_range_succ]

private theorem total_gt (t j : ℕ) : t < partTotal t (j+1) := by
  rw [total_eq, Nat.add_mul, one_mul]
  have h := row_pos j
  omega

private theorem weight_extend (n q j : ℕ) (hq : q < n) :
    weight (q+1) (j+1) =
      ∑ t ∈ Finset.range n, if partTotal t (j+1) = q+1 then (if t = 0 then 1 else 2) else 0 := by
  unfold weight
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro t _ ht
  rw [Finset.mem_range, not_lt] at ht
  exact if_neg (by have h := total_gt t j; omega)

private theorem sum_levels (n j t : ℕ) :
    (∑ q ∈ Finset.range n, if partTotal t (j+1) = q+1 then (if t = 0 then 1 else 2) else 0) =
      if partTotal t (j+1) ≤ n then (if t = 0 then 1 else 2) else 0 := by
  have h := total_gt t j
  by_cases hle : partTotal t (j+1) ≤ n
  · let q := partTotal t (j+1)-1
    have hq : q+1 = partTotal t (j+1) := by dsimp [q]; omega
    rw [if_pos hle, Finset.sum_eq_single q, if_pos hq.symm]
    · intro q' _ hn
      exact if_neg (by omega)
    · intro hn
      exact (hn (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg hle]
    exact Finset.sum_eq_zero (fun q hq => if_neg (by rw [Finset.mem_range] at hq; omega))

private theorem sum_count (m : ℕ) :
    (∑ t ∈ Finset.range (m+1), if t = 0 then 1 else 2) = 2*m+1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m.succ+1 = (m+1)+1 by omega, Finset.sum_range_succ, ih]
    simp
    omega

private theorem sum_col (n j : ℕ) :
    (∑ t ∈ Finset.range n, if partTotal t (j+1) ≤ n then (if t = 0 then 1 else 2) else 0) =
      column n (j+1) := by
  unfold column
  by_cases h : firstRow (j+1) ≤ n
  · let m := (n-firstRow (j+1))/(j+1)
    have hrow := row_pos j
    have hm : m < n := (Nat.div_le_self _ _).trans_lt (by omega)
    have he (t : ℕ) : partTotal t (j+1) ≤ n ↔ t < m+1 := by
      rw [total_eq, Nat.lt_succ_iff, Nat.le_div_iff_mul_le (by omega : 0 < j+1)]
      rw [Nat.mul_comm t]
      omega
    rw [if_pos h]
    simp_rw [he]
    rw [show (∑ t ∈ Finset.range n, if t < m+1 then (if t = 0 then 1 else 2) else 0) =
      ∑ t ∈ Finset.range (m+1), if t = 0 then 1 else 2 by
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        omega, sum_count]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro t _
    rw [total_eq]
    exact if_neg (by omega)

theorem OMA.solution : type_of% @OMA.S_oeis_a338722.main := by
  intro n _
  unfold row level
  symm
  calc
    _ = ∑ q ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ t ∈ Finset.range n,
          if partTotal t (j+1) = q+1 then (if t = 0 then 1 else 2) else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        have hqn := Finset.mem_range.mp hq
        calc
          _ = ∑ j ∈ Finset.range n, weight (q+1) (j+1) := by
            apply Finset.sum_subset (Finset.range_mono (by omega))
            intro j _ hj
            rw [Finset.mem_range, not_lt] at hj
            have hr : j+1 ≤ firstRow (j+1) := by
              have hh : (∑ i ∈ Finset.range (j+1), (1 : ℕ)) ≤
                  ∑ i ∈ Finset.range (j+1), (i+1) :=
                Finset.sum_le_sum (fun _ _ => by omega)
              simpa [firstRow] using hh
            unfold weight
            apply Finset.sum_eq_zero
            intro t _
            rw [total_eq]
            exact if_neg (by omega)
          _ = _ := Finset.sum_congr rfl (fun j _ => weight_extend n q j hqn)
    _ = ∑ j ∈ Finset.range n, column n (j+1) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
        simp_rw [sum_levels]
        exact sum_col n j