import OMAStatements.S_oeis_a217448

theorem OMA.solution : type_of% @OMA.S_oeis_a217448.main := by
  intro n hn
  set p := (1 + n ^ 2).minFac
  refine ⟨p.factorial, p.factorial_pos, ?_⟩
  have key : ∀ q, 0 < q → q ≤ p → (q ∣ 1 + (n + p.factorial) ^ 2 ↔ q ∣ 1 + n ^ 2) := fun q h0 h => by
    obtain ⟨t, ht⟩ := Nat.dvd_factorial h0 h
    rw [ht, show 1 + (n + q * t) ^ 2 = 1 + n ^ 2 + q * (2 * n * t + q * t ^ 2) by ring,
      Nat.dvd_add_left (dvd_mul_right _ _)]
  have hp := Nat.minFac_prime (show 1 + n ^ 2 ≠ 1 by simp [hn.ne'])
  have h := Nat.minFac_le_of_dvd hp.two_le ((key p hp.pos le_rfl).2 (Nat.minFac_dvd _))
  exact le_antisymm (Nat.minFac_le_of_dvd ((Nat.minFac_prime (by simp [hn.ne'])).two_le)
    ((key _ (Nat.minFac_pos _) h).1 (Nat.minFac_dvd _))) h
