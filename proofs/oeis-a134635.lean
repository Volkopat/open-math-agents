import OMAStatements.S_oeis_a134635

open OMA.S_oeis_a134635 Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a134635.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have r (j : ℕ) : ((j:ℤ)+2) * catalan (j+1) = 2*(2*j+1) * catalan j := by
    have h := j.succ_mul_centralBinom_succ
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at h
    zify at h
    exact mul_left_cancel₀ j.cast_add_one_ne_zero (by linear_combination h)
  have d (n : ℕ) : (a (n+1) + 2 * catalan n : ℤ) = 2 * a n + 2 * catalan (n+1) := by
    have h1 : a n = ∑ k ∈ range n, T n (k+1) + T n 0 := sum_range_succ' _ _
    have h2 : a n = ∑ k ∈ range n, T n k + T n n := sum_range_succ _ _
    have h3 : a (n+1) = ∑ k ∈ range n, (T n (k+1) + T n k) + T (n+1) 0 + T (n+1) (n+1) := by
      rw [a, sum_range_succ, sum_range_succ']
      congr 2
      exact sum_congr rfl fun k hk => by simp [T, mem_range.1 hk, (mem_range.1 hk).ne]
    rw [sum_add_distrib] at h3
    have : T n 0 = catalan n ∧ T n n = catalan n := by cases n <;> simp [T]
    simp [T] at h3
    omega
  have r0 := r k
  have r1 := r (k+1)
  have r2 := r (k+2)
  have d0 := d k
  have d1 := d (k+1)
  have d2 := d (k+2)
  simp [add_assoc] at *
  linear_combination (4*k+2)*d0 + (-5*k-12)*d1 + (k+4)*d2 + 2*r0 - 4*r1 + 2*r2
