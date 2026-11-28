import OMAStatements.S_oeis_a276674

open ArithmeticFunction

private lemma half (n : ℕ) : (2 * n).totient ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · simp [hz]
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨j, rfl⟩ := he.two_dvd
      rw [Nat.totient_two_mul_of_even he]
      exact Nat.mul_le_mul_left 2 (ih j (by omega))
    · rw [Nat.totient_two_mul_of_odd ho]
      exact Nat.totient_le n

theorem OMA.solution : type_of% @OMA.S_oeis_a276674.main := by
  intro x m hx hm hgap
  by_cases hs : x ≤ 2
  · omega
  have : Fact (1 < x) := ⟨by omega⟩
  have : NeZero x := ⟨by omega⟩
  have hc : 2 ∣ carmichael x := by
    have h := Monoid.order_dvd_exponent (-1 : (ZMod x)ˣ)
    rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one,
      ringChar.eq (ZMod x) x, if_neg (by omega : x ≠ 2),
      ← carmichael_eq_exponent (by omega : x ≠ 0)] at h
    exact h
  have hle := Nat.le_of_dvd (Nat.totient_pos.mpr (by omega : 0 < x))
    (carmichael_dvd_totient x)
  have := Nat.totient_le x
  obtain ⟨j, hj⟩ : 2 ∣ x := by omega
  have hb := half j
  rw [← hj] at hb
  omega
