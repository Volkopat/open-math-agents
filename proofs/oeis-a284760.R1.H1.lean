import OMAReductions.R_oeis_a284760_R1

-- For n = 4k + 2, the power sum is odd and n^4 is even.
theorem OMA.solution : OMA.R_oeis_a284760_R1.H1 := by
  intro n hn hzero
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = 4 * k + 2 := ⟨n / 4, by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact (by decide : (∑ i ∈ Finset.Ico 1 2, i ^ (2 - 2)) % 2 ^ 4 ≠ 0) hzero
  let s := Finset.Ico 1 (4 * k + 2)
  let e := 4 * k + 2 - 2
  have epos : e ≠ 0 := by dsimp [e]; omega
  have pow_mod_two (i : ℕ) : i ^ e % 2 = i % 2 := by
    rw [Nat.pow_mod]
    rcases Nat.mod_two_eq_zero_or_one i with hi | hi
    · simp [hi, epos]
    · simp [hi]
  have intervalSum : (∑ i ∈ s, i) = (2 * k + 1) * (4 * k + 1) := by
    have rangeSum : (∑ i ∈ Finset.range (4 * k + 2), i) = ∑ i ∈ s, i := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      simp [s]
    rw [← rangeSum, Finset.sum_range_id, show 4 * k + 2 - 1 = 4 * k + 1 by omega]
    rw [show (4 * k + 2) * (4 * k + 1) = 2 * ((2 * k + 1) * (4 * k + 1)) by ring]
    exact Nat.mul_div_cancel_left _ (by decide)
  have sum_mod_two : (∑ i ∈ s, i ^ e) % 2 = 1 := calc
    _ = (∑ i ∈ s, i ^ e % 2) % 2 := Finset.sum_nat_mod s 2 (fun i => i ^ e)
    _ = (∑ i ∈ s, i % 2) % 2 := by simp only [pow_mod_two]
    _ = (∑ i ∈ s, i) % 2 := (Finset.sum_nat_mod s 2 id).symm
    _ = 1 := by
      rw [intervalSum, Nat.mul_mod, show (2 * k + 1) % 2 = 1 by omega,
        show (4 * k + 1) % 2 = 1 by omega]
  have evenModulus : 2 ∣ (4 * k + 2) ^ 4 :=
    dvd_pow (show 2 ∣ 4 * k + 2 by omega) (by decide)
  have evenSum : 2 ∣ ∑ i ∈ s, i ^ e :=
    evenModulus.trans (Nat.dvd_of_mod_eq_zero hzero)
  exact (by decide : 1 ≠ 0) (sum_mod_two.symm.trans (Nat.mod_eq_zero_of_dvd evenSum))
