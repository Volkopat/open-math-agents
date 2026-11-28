import OMAStatements.S_oeis_a111869

/-!
At the proposed index, the central binomial coefficient is twice an odd
factor times a Catalan number. Below that index the top of the binomial
coefficient is smaller than `p²`, so its `p`-adic valuation is at most one.
-/

private theorem odd_factor (j : ℕ) : 2 * j + 1 ∣ (j + 1).centralBinom := by
  obtain ⟨c, hc⟩ := Nat.succ_dvd_centralBinom j
  refine ⟨2 * c, Nat.eq_of_mul_eq_mul_left (Nat.succ_pos j) ?_⟩
  rw [Nat.succ_mul_centralBinom_succ, hc]
  simp only [Nat.succ_eq_add_one]
  ring

open OMA.S_oeis_a111869 in
theorem least_index (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    a p = (p ^ 2 - 1) / 2 + 1 := by
  obtain ⟨j, hsq⟩ := (hp.odd_of_ne_two hp2).pow (n := 2)
  have hi : (p ^ 2 - 1) / 2 + 1 = j + 1 := by omega
  rw [hi]
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨by omega, hsq ▸ odd_factor j⟩
  · intro k hk
    obtain ⟨_, hd⟩ := hk
    by_contra! hlt
    have htop : 2 * k < p ^ 2 := by omega
    have hlo := (hp.pow_dvd_iff_le_factorization (Nat.choose_pos (show k ≤ 2 * k by omega)).ne').mp hd
    have hhi := Nat.factorization_choose_le_one (k := k) htop
    omega


theorem OMA.solution : type_of% @OMA.S_oeis_a111869.main := least_index
