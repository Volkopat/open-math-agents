import OMAStatements.S_oeis_a003500

open OMA.S_oeis_a003500 in
theorem OMA.solution : type_of% @OMA.S_oeis_a003500.main := by
  have c (n) : 2 ∣ a n ∧ 2 ∣ a (n + 1) ∧ 2 ≤ a n ∧ a n < a (n + 1) := by
    induction n with
    | zero => decide
    | succ n ih => rw [a]; omega
  rintro (_ | n) hp
  · cases Nat.not_prime_zero hp
  have := c n
  refine ⟨by omega, fun h => ?_⟩
  have := (Int.prime_iff_natAbs_prime.1 h).eq_one_or_self_of_dvd 2 (Int.natAbs_dvd_natAbs.2 this.2.1)
  omega
