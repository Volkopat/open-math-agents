import OMAStatements.S_oeis_a140869

theorem OMA.solution : type_of% @OMA.S_oeis_a140869.main := by
  intro h hns
  by_contra hnp
  have hp := Nat.minFac_prime (show 4 * h + 5 ≠ 1 by omega)
  obtain ⟨b, hb⟩ := Nat.minFac_dvd (4 * h + 5)
  have hle := Nat.minFac_le_div (by omega) hnp
  generalize (4 * h + 5).minFac = a at hp hb hle
  rw [hb, Nat.mul_div_cancel_left _ hp.pos] at hle
  obtain ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩ := Nat.odd_mul.1 (hb ▸ ⟨2 * h + 2, by ring⟩ : Odd (a * b))
  refine hns ⟨m, n, by have := hp.two_le; omega, by omega, ?_⟩
  unfold OMA.S_oeis_a140869.T
  rw [show 2 * m * n + m + n = 2 * h + 2 by nlinarith]
  omega
