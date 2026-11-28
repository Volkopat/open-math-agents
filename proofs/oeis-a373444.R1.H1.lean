import OMAReductions.R_oeis_a373444_R1

/-! A failed subset-sum test at a small denominator excludes each polygonal remainder. -/
open OMA.S_oeis_a373444 Finset

theorem OMA.solution : OMA.R_oeis_a373444_R1.H1 := by
  rintro ⟨p, k, hp, h⟩
  have hk : k < 179 := by
    by_contra! hlarge
    have := Nat.mul_le_mul hlarge (show 892 ≤ 5 * k - 3 by omega)
    unfold polygonal at h
    omega
  have tab : ∀ j < 179, ∃ m ∈ ({2, 4, 8, 16, 32, 43, 64, 91, 128, 187, 218, 256, 379} : Finset ℕ),
      m ≤ 79445 - polygonal j ∧
      ∑ i ∈ (range (m+1)).filter (· ∣ 79445 - polygonal j), i < m := by decide +kernel
  obtain ⟨m, _, hm, hgap⟩ := tab k hk
  rw [show 79445 - polygonal k = p by omega] at hm hgap
  obtain ⟨t, ht, he⟩ := hp.2 m hm
  apply hgap.not_ge
  rw [← he] at *
  apply sum_le_sum_of_subset
  intro i hi
  exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (single_le_sum (f := id)
    (fun _ _ => Nat.zero_le _) hi)), Nat.dvd_of_mem_divisors (ht hi)⟩
