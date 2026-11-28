import OMAStatements.S_oeis_a000629

theorem a000629_key (n : ℕ) : ∀ k : ℕ,
    Nat.stirlingSecond (n + 1) (k + 1) =
      ∑ j ∈ Finset.range (n + 1), n.choose j * Nat.stirlingSecond j k := by
  induction n with
  | zero =>
    intro k
    simp [Nat.stirlingSecond_succ_succ]
  | succ n ih =>
    intro k
    have h2 : ∑ j ∈ Finset.range (n + 1), n.choose (j + 1) * Nat.stirlingSecond (j + 1) k +
        Nat.stirlingSecond 0 k =
        ∑ j ∈ Finset.range (n + 1), n.choose j * Nat.stirlingSecond j k := by
      have a := Finset.sum_range_succ' (fun j => n.choose j * Nat.stirlingSecond j k) (n + 1)
      have b := Finset.sum_range_succ (fun j => n.choose j * Nat.stirlingSecond j k) (n + 1)
      simp only [Nat.choose_zero_right, one_mul, Nat.choose_succ_self, zero_mul, add_zero] at a b
      rw [← a, b]
    have h1 : ∑ j ∈ Finset.range (n + 1 + 1), (n + 1).choose j * Nat.stirlingSecond j k =
        ∑ j ∈ Finset.range (n + 1), n.choose j * Nat.stirlingSecond (j + 1) k +
        ∑ j ∈ Finset.range (n + 1), n.choose j * Nat.stirlingSecond j k := by
      rw [Finset.sum_range_succ' _ (n + 1), ← h2]
      simp only [Nat.choose_succ_succ', add_mul, Finset.sum_add_distrib, Nat.choose_zero_right,
        one_mul]
      ring
    rw [h1, ← ih k, Nat.stirlingSecond_succ_succ (n + 1) k]
    cases k with
    | zero =>
      simp
    | succ k =>
      have h3 : ∑ j ∈ Finset.range (n + 1), n.choose j * Nat.stirlingSecond (j + 1) (k + 1) =
          (k + 1) * Nat.stirlingSecond (n + 1) (k + 1 + 1) +
            Nat.stirlingSecond (n + 1) (k + 1) := by
        rw [ih (k + 1), ih k, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [Nat.stirlingSecond_succ_succ]
        ring
      rw [h3]
      ring

theorem OMA.solution : type_of% @OMA.S_oeis_a000629.main := by
  intro n
  change ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond (n + 1) (k + 1) * k.factorial =
    ∑ k ∈ Finset.range (n + 1), n.choose k *
      ∑ j ∈ Finset.range (n - k + 1), Nat.stirlingSecond (n - k) j * j.factorial
  have hF : ∀ j ∈ Finset.range (n + 1),
      ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond j k * k.factorial =
        ∑ k ∈ Finset.range (j + 1), Nat.stirlingSecond j k * k.factorial := by
    intro j hj
    symm
    apply Finset.sum_subset (Finset.range_mono (by simpa using Finset.mem_range.mp hj))
    intro k _ hk
    rw [Nat.stirlingSecond_eq_zero_of_lt (by simp only [Finset.mem_range] at hk; omega), zero_mul]
  simp_rw [a000629_key n, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  refine (Finset.sum_congr rfl fun j hj => by rw [hF j hj]).trans ?_
  rw [← Finset.sum_range_reflect _ (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Nat.add_sub_cancel]
  rw [Nat.choose_symm (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
