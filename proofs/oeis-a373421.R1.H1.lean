import OMAReductions.R_oeis_a373421_R1

/-! A failed subset-sum test at a small denominator excludes each polygonal remainder. -/
open OMA.S_oeis_a373421 Finset

theorem OMA.solution : OMA.R_oeis_a373421_R1.H1 := by
  rintro ⟨p, k, hp, h⟩
  have hk : k < 43 := by
    by_contra! hlarge
    have := Nat.mul_le_mul hlarge (show 128 ≤ 3 * k - 1 by omega)
    unfold polygonal at h
    omega
  have tab : ∀ j < 43, ∃ m ∈ ({2, 5, 40, 82} : Finset ℕ),
      m ≤ 2671 - polygonal j ∧
      ∑ i ∈ (range (m+1)).filter (· ∣ 2671 - polygonal j), i < m := by decide +kernel
  obtain ⟨m, _, hm, hgap⟩ := tab k hk
  rw [show 2671 - polygonal k = p by omega] at hm hgap
  obtain ⟨t, ht, he⟩ := hp.2 m hm
  apply hgap.not_ge
  rw [← he] at *
  apply sum_le_sum_of_subset
  intro i hi
  exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (single_le_sum (f := id)
    (fun _ _ => Nat.zero_le _) hi)), Nat.dvd_of_mem_divisors (ht hi)⟩
