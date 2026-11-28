import OMAStatements.S_oeis_a090526
open OMA.S_oeis_a090526
theorem OMA.solution : type_of% @OMA.S_oeis_a090526.main := by
  intro n hn
  obtain ⟨k, hk⟩ := dvd_pow (Nat.minFac_dvd n) (by omega : n ≠ 0)
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  have h : 1 ≤ a090525 n ∧ (n ^ n / a090525 n).Prime :=
    Nat.sInf_mem (s := {j | 1 ≤ j ∧ (n ^ n / j).Prime})
      ⟨k, hk0, by rw [hk, Nat.mul_div_cancel _ hk0]; exact Nat.minFac_prime (by omega)⟩
  rw [a, if_neg (by omega)]
  exact h.2.ne_zero
