import OMAReductions.R_EuclidNumbers_euclid_numbers_are_square_free_R1

/-! If a prime q divides Euclid n = 1 + p_0 ⋯ p_(n-1) and q < p_n, then q = p_i with
i = count Prime q < n, so q divides the product and hence divides 1, which is impossible. -/

theorem OMA.solution : OMA.R_EuclidNumbers_euclid_numbers_are_square_free_R1.H1 := by
  intro n q hq hdvd
  by_contra hlt
  push Not at hlt
  have hi : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hq
  have hin : Nat.count Nat.Prime q < n := by
    have h := hlt
    rw [← hi] at h
    exact (Nat.nth_lt_nth Nat.infinite_setOf_prime).1 h
  have hd : q ∣ ∏ i ∈ Finset.range n, i.nth Nat.Prime := by
    have h := Finset.dvd_prod_of_mem (fun i => i.nth Nat.Prime) (Finset.mem_range.2 hin)
    rwa [hi] at h
  unfold EuclidNumbers.Euclid at hdvd
  rw [add_comm] at hdvd
  have h1 : q ∣ 1 := (Nat.dvd_add_right hd).1 hdvd
  exact hq.one_lt.ne' (Nat.dvd_one.1 h1)
